import BalancedAssortments.FPTASCostKernel
import BalancedAssortments.FPTASCostOutput

namespace BalancedAssortments.FPTASCostCandidate
open KnapsackCostRational FPTASCostKernel FPTASCostOptions

def accept (ρ : Fraction) : Option KnapsackCostState.State → Option KnapsackCostState.State × ℕ
  | none => (none,1)
  | some s =>
      let test := FPTASCostOutput.accepts ρ s.profit
      (if test.1 then some s else none,test.2+4)

lemma accept_member {ρ : Fraction} {old : Option KnapsackCostState.State} {s : KnapsackCostState.State}
    (hs : (accept ρ old).1 = some s) : old = some s := by
  cases old with
  | none => simp [accept] at hs
  | some t => simp only [accept] at hs; split_ifs at hs <;> simp_all

lemma accept_decode {ρ : Fraction} {old : Option KnapsackCostState.State}
    (hp : ρ.Valid) (ho : ∀ s, old = some s → s.Valid) :
    (accept ρ old).1.map KnapsackCostState.State.decode =
      (old.map KnapsackCostState.State.decode).filter (fun s => ρ.decode ≤ s.profit) := by
  cases old with
  | none => rfl
  | some s =>
    have he := FPTASCostOutput.accepts_correct hp (ho s rfl).2.1
    simp only [accept,Option.map_some,Option.filter_some]
    by_cases h : ρ.decode ≤ s.profit.decode
    · simp [he.mpr h,KnapsackCostState.State.decode,h]
    · have hh : (FPTASCostOutput.accepts ρ s.profit).1 = false := by
        apply Bool.eq_false_iff.mpr
        exact fun ht => h (he.mp ht)
      simp [hh,KnapsackCostState.State.decode,h]

lemma accept_cost {ρ : Fraction} {old : Option KnapsackCostState.State} {b : ℕ}
    (hp : ρ.Width b) (ho : ∀ s, old = some s → s.Width b) :
    (accept ρ old).2 ≤ 512*(b+1)^2+6 := by
  cases old with
  | none => simp [accept]
  | some s => exact Nat.add_le_add_right (FPTASCostOutput.accepts_cost hp (ho s rfl).2.1) 4

/-- One fully binary candidate run: build options, select maximum profit, form θ,
run scaled DP, and apply the unrounded acceptance test. H and bound are loop fuel. -/
def candidate (H bound : ℕ) (δ count cap τ ratio α ρ : Fraction)
    (products : List (Fraction × Fraction)) : Option KnapsackCostState.State × ℕ :=
  let groups := groupsBits H τ ratio α ρ products
  let result := core δ count cap bound groups.1
  let accepted := accept ρ result.1
  (accepted.1,groups.2+result.2+accepted.2+8)

/-- Exact refinement to the actual source candidateAt, assuming the supplied
horizon covers each product and the supplied count/cap decode to N/K. -/
theorem candidate_decode {n : ℕ} (d : FPTAS.Input n) (H : ℕ)
    (δ count cap τ ratio α ρ : Fraction) (rv : Fin (n+1) → Fraction × Fraction)
    (hδ : δ.Valid) (hδpos : 0 < δ.decode) (hcount : count.decode = n+1)
    (hcap : cap.Valid) (hcapd : cap.decode = d.K)
    (ht : τ.Valid) (hratio : ratio.Valid) (ha : α.Valid) (hp : ρ.Valid)
    (hprod : ∀ i, (rv i).1.Valid ∧ (rv i).2.Valid)
    (hdecode : ∀ i, (rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (halpha : α.decode = d.α) (hrat : ratio.decode = 1+δ.decode)
    (htpos : 0 < τ.decode) (hapos : 0 < d.α) (hvpos : ∀ i, 0 < d.v i)
    (hcover : ∀ i, min (d.v i) (τ.decode/d.α) < τ.decode*(1+δ.decode)^(H+1)) :
    (candidate H ((n+1)*⌈(n+1:ℚ)/δ.decode⌉₊) δ count cap τ ratio α ρ
      ((List.finRange (n+1)).map rv)).1.map
        (fun s => FPTAS.stateVector s.decode) =
      FPTAS.candidateAt d δ.decode τ.decode ρ.decode := by
  let products := (List.finRange (n+1)).map rv
  let gs := (groupsBits H τ ratio α ρ products).1
  let B := (n+1)*⌈(n+1:ℚ)/δ.decode⌉₊
  have hgs := groupsBits_decode d H τ ratio α ρ rv δ.decode ht hratio ha hp hprod hdecode
    halpha hrat htpos hapos hvpos hδpos hcover
  have hgsvalid : ∀ g ∈ gs, ∀ i ∈ g, i.Valid := by
    apply groupsBits_valid H τ ratio α ρ products ht hratio hp (by rwa [halpha])
    intro pair hpair
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hpair
    exact ⟨(hprod i).1, by simpa only [(hdecode i).2] using hvpos i⟩
  have hn : 0 < count.decode := by rw [hcount]; positivity
  have hc := core_decode δ count cap B gs hδ hδpos hn hcap hgsvalid
  rw [hgs,hcount,hcapd] at hc
  have haccept := accept_decode (old := (core δ count cap B gs).1) hp (fun s hs => core_valid hgsvalid hs)
  have hfinal : (accept ρ (core δ count cap B gs).1).1.map KnapsackCostState.State.decode =
      ((if FPTAS.maxList (((FPTAS.groups d δ.decode τ.decode ρ.decode).flatten).map Knapsack.Item.profit) ≤ 0 then none else
        Knapsack.solve (δ.decode*FPTAS.maxList (((FPTAS.groups d δ.decode τ.decode ρ.decode).flatten).map Knapsack.Item.profit)/(n+1)) d.K B
          (FPTAS.groups d δ.decode τ.decode ρ.decode))).filter (fun s => ρ.decode ≤ s.profit) := by
    rw [haccept,hc]
  change ((accept ρ (core δ count cap B gs).1).1.map (fun s => FPTAS.stateVector s.decode)) = _
  rw [show (fun s : KnapsackCostState.State => FPTAS.stateVector (n := n) s.decode) =
    (FPTAS.stateVector (n := n)) ∘ KnapsackCostState.State.decode by rfl, ← Option.map_map, hfinal]
  dsimp only [FPTAS.candidateAt,B]
  split_ifs
  · rfl
  · cases Knapsack.solve
      (δ.decode * FPTAS.maxList (List.map Knapsack.Item.profit (FPTAS.groups d δ.decode τ.decode ρ.decode).flatten) / (↑n+1))
      (↑d.K) ((n+1)*⌈(n+1:ℚ)/δ.decode⌉₊) (FPTAS.groups d δ.decode τ.decode ρ.decode) <;> simp only [Option.filter,Option.map_none,Option.map_some,decide_eq_true_eq]
    split_ifs <;> rfl

def candidateCost (H B N b : ℕ) : ℕ :=
  let g := groupWidth H b
  N*(groupCost H b+4)+1 + coreCost N (H+2) B g +
    512*(kernelWidth N g+b+1)^2+14

theorem candidate_cost (H bound : ℕ) (δ count cap τ ratio α ρ : Fraction)
    (products : List (Fraction × Fraction)) {b : ℕ}
    (hd : δ.Width b) (hn : count.Width b) (hc : cap.Width b) (ht : τ.Width b)
    (hratio : ratio.Width b) (ha : α.Width b) (hp : ρ.Width b)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    (candidate H bound δ count cap τ ratio α ρ products).2 ≤ candidateCost H bound products.length b := by
  let gs := (groupsBits H τ ratio α ρ products).1
  let g := groupWidth H b
  have hg := groupsBits_width H τ ratio α ρ products ht hratio ha hp hprod
  have hgen := groupsBits_cost H τ ratio α ρ products ht hratio ha hp hprod
  have hgl : gs.length = products.length := by simp [gs,groupsBits_eq]
  have hb : b ≤ g := by dsimp [g,groupWidth]; omega
  have hd' := KnapsackCostState.Fraction.width_mono hd hb
  have hn' := KnapsackCostState.Fraction.width_mono hn hb
  have hc' := KnapsackCostState.Fraction.width_mono hc hb
  have hfields : ∀ group ∈ gs, ∀ i ∈ group, i.value.Width g ∧ i.weight.Width g ∧ i.profit.Width g := by
    intro group hgroup i hi
    have hh := (hg group hgroup).2 i hi
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hcore := core_cost δ count cap bound gs hd' hn' hc'
    (fun group hgroup => ⟨(hg group hgroup).1,hfields group hgroup⟩)
  let W := kernelWidth products.length g+b
  have hresult : ∀ s, (core δ count cap bound gs).1 = some s → s.Width W := by
    intro s hs
    have hh := (core_width hd' hn' hfields hs).1
    rw [hgl] at hh
    exact KnapsackCostState.State.width_mono hh (by dsimp [W]; omega)
  have haccept := accept_cost (KnapsackCostState.Fraction.width_mono hp (show b ≤ W by dsimp [W]; omega)) hresult
  rw [hgl] at hcore
  simp only [candidate,candidateCost]
  dsimp only [W,g,gs] at *
  omega

theorem candidate_valid {H bound : ℕ} {δ count cap τ ratio α ρ : Fraction}
    {products : List (Fraction × Fraction)} {s : KnapsackCostState.State}
    (ht : τ.Valid) (hratio : ratio.Valid) (hp : ρ.Valid) (hapos : 0 < α.decode)
    (hprod : ∀ rv ∈ products, rv.1.Valid ∧ 0 < rv.2.decode)
    (hs : (candidate H bound δ count cap τ ratio α ρ products).1 = some s) : s.Valid := by
  have hg := groupsBits_valid H τ ratio α ρ products ht hratio hp hapos hprod
  exact core_valid hg (accept_member hs)

end BalancedAssortments.FPTASCostCandidate
