import BalancedAssortments.FPTASCostAutoGroups
import BalancedAssortments.FPTASCostCutoff

namespace BalancedAssortments.FPTASCostCandidate
open KnapsackCostRational FPTASCostKernel FPTASCostOptions FPTASCostCutoff

def candidateCore (δ count cap ρ : Fraction) (fuel : List Unit)
    (groups : List (List KnapsackCostState.Item)) : Option KnapsackCostState.State × ℕ :=
  let result := coreTokens δ count cap fuel groups
  let accepted := accept ρ result.1
  (accepted.1,result.2+accepted.2+4)

lemma candidateCore_decode {n : ℕ} (d : FPTAS.Input n) (τ : ℚ)
    (δ count cap ρ : Fraction) (fuel : List Unit) (groups : List (List KnapsackCostState.Item))
    (hd : δ.Valid) (hdp : 0 < δ.decode) (hn : count.decode = n+1)
    (hc : cap.Valid) (hcd : cap.decode = d.K) (hp : ρ.Valid)
    (hB : fuel.length = (n+1)*⌈(n+1:ℚ)/δ.decode⌉₊)
    (hg : groups.map (List.map KnapsackCostState.Item.decode) = FPTAS.groups d δ.decode τ ρ.decode)
    (hv : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) :
    (candidateCore δ count cap ρ fuel groups).1.map (fun s => FPTAS.stateVector (n := n) s.decode) =
      FPTAS.candidateAt d δ.decode τ ρ.decode := by
  have hcount : 0 < count.decode := by rw [hn]; positivity
  have hcore := core_decode δ count cap fuel.length groups hd hdp hcount hc hv
  rw [hg,hn,hcd,hB] at hcore
  have haccept := accept_decode (old := (core δ count cap fuel.length groups).1) hp
    (fun s hs => core_valid hv hs)
  change _ = _ at haccept
  simp only [candidateCore,coreTokens_eq]
  rw [show (fun s : KnapsackCostState.State => FPTAS.stateVector (n := n) s.decode) =
    (FPTAS.stateVector (n := n)) ∘ KnapsackCostState.State.decode by rfl,← Option.map_map,haccept,hB,hcore]
  dsimp only [FPTAS.candidateAt]
  split_ifs
  · rfl
  · cases Knapsack.solve
      (δ.decode*FPTAS.maxList ((FPTAS.groups d δ.decode τ ρ.decode).flatten.map Knapsack.Item.profit)/(n+1))
      d.K ((n+1)*⌈(n+1:ℚ)/δ.decode⌉₊) (FPTAS.groups d δ.decode τ ρ.decode) <;>
      simp only [Option.filter,Option.map_none,decide_eq_true_eq]
    split_ifs <;> rfl

def candidateCoreCost (N M B b : ℕ) : ℕ :=
  coreCost N M B b +512*(kernelWidth N b+b+1)^2+10

lemma candidateCore_cost (δ count cap ρ : Fraction) (fuel : List Unit)
    (groups : List (List KnapsackCostState.Item)) {b M : ℕ}
    (hd : δ.Width b) (hn : count.Width b) (hc : cap.Width b) (hp : ρ.Width b)
    (hg : ∀ g ∈ groups,g.length ≤ M ∧ ∀ i ∈ g,
      i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b) :
    (candidateCore δ count cap ρ fuel groups).2 ≤ candidateCoreCost groups.length M fuel.length b := by
  have hcore := core_cost δ count cap fuel.length groups hd hn hc hg
  let W := kernelWidth groups.length b+b
  have hw : ∀ s,(core δ count cap fuel.length groups).1 = some s → s.Width W := by
    intro s hs
    exact KnapsackCostState.State.width_mono (core_width hd hn (fun g hg' => (hg g hg').2) hs).1
      (by dsimp [W]; omega)
  have hacc := accept_cost (KnapsackCostState.Fraction.width_mono hp (show b ≤ W by dsimp [W]; omega)) hw
  simp only [candidateCore,coreTokens_eq,candidateCoreCost]
  dsimp only [W] at hacc
  omega

def autoCandidate (δ count cap τ ratio α ρ : Fraction) (fuel : List Unit)
    (products : List (Fraction × Fraction)) : Option KnapsackCostState.State × ℕ :=
  let groups := groupsAuto δ τ ratio α ρ products
  let result := candidateCore δ count cap ρ fuel groups.1
  (result.1,groups.2+result.2+4)

/-- The candidate now has no externally guessed grid horizon and no decoded
Nat cutoff loop: both group grids and the DP use actual token quotas. -/
theorem autoCandidate_decode {n : ℕ} (d : FPTAS.Input n)
    (δ count cap τ ratio α ρ : Fraction) (fuel : List Unit) (rv : Fin (n+1) → Fraction × Fraction)
    (hd : δ.Valid) (hdp : 0 < δ.decode) (hn : count.decode = n+1)
    (hc : cap.Valid) (hcd : cap.decode = d.K)
    (ht : τ.Valid) (hratio : ratio.Valid) (ha : α.Valid) (hp : ρ.Valid)
    (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdecode : ∀ i,(rv i).1.decode = d.r i ∧ (rv i).2.decode = d.v i)
    (had : α.decode = d.α) (hrat : ratio.decode = 1+δ.decode)
    (htp : 0 < τ.decode) (hap : 0 < d.α) (hvp : ∀ i,0 < d.v i)
    (hB : fuel.length = (n+1)*⌈(n+1:ℚ)/δ.decode⌉₊) :
    (autoCandidate δ count cap τ ratio α ρ fuel ((List.finRange (n+1)).map rv)).1.map
      (fun s => FPTAS.stateVector (n := n) s.decode) = FPTAS.candidateAt d δ.decode τ.decode ρ.decode := by
  apply candidateCore_decode d τ.decode δ count cap ρ fuel _ hd hdp hn hc hcd hp hB
  · exact groupsAuto_decode d δ τ ratio α ρ rv ht hd hratio ha hp hprod hdecode had hrat htp hap hvp hdp
  · apply groupsAuto_valid δ τ ratio α ρ _ ht hratio hp (by rwa [had])
    intro pair hpair
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hpair
    exact ⟨(hprod i).1,by simpa only [(hdecode i).2] using hvp i⟩

def autoCandidateCost (B N b Q : ℕ) : ℕ :=
  let H := 4*b*(Q+1)
  N*(autoGroupCost b (Q+1)+4)+1 + candidateCoreCost N (H+2) B (groupWidth H b)+4

theorem autoCandidate_cost (δ count cap τ ratio α ρ : Fraction) (fuel : List Unit)
    (products : List (Fraction × Fraction)) {b : ℕ}
    (hb : 1 ≤ b) (hd : δ.Width b) (hn : count.Width b) (hc : cap.Width b)
    (ht : τ.Width b) (hratio : ratio.Width b) (ha : α.Width b) (hp : ρ.Width b)
    (hdv : δ.Valid) (hdp : 0 < δ.decode)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b) :
    (autoCandidate δ count cap τ ratio α ρ fuel products).2 ≤
      autoCandidateCost fuel.length products.length b (GridBounds.blockLength δ.decode) := by
  let gs := (groupsAuto δ τ ratio α ρ products).1
  let H := 4*b*(GridBounds.blockLength δ.decode+1)
  let g := groupWidth H b
  have hgen := groupsAuto_cost_ceil δ τ ratio α ρ products hb hd ht hratio ha hp hdv hdp hprod
  have hg := groupsAuto_bounds δ τ ratio α ρ products ht hratio ha hp hdv hdp hprod
  have hlen : gs.length = products.length := by simp [gs,groupsAuto_eq]
  have hb' : b ≤ g := by dsimp [g,groupWidth]; omega
  have hfields : ∀ group ∈ gs, group.length ≤ H+2 ∧ ∀ i ∈ group,
      i.value.Width g ∧ i.weight.Width g ∧ i.profit.Width g := by
    intro group hgroup
    refine ⟨(hg group hgroup).1, ?_⟩
    intro i hi
    have hh := (hg group hgroup).2 i hi
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hcore := candidateCore_cost δ count cap ρ fuel gs
    (KnapsackCostState.Fraction.width_mono hd hb') (KnapsackCostState.Fraction.width_mono hn hb')
    (KnapsackCostState.Fraction.width_mono hc hb') (KnapsackCostState.Fraction.width_mono hp hb') hfields
  rw [hlen] at hcore
  simp only [autoCandidate,autoCandidateCost]
  dsimp only [gs,H,g] at *
  omega

theorem autoCandidate_valid {δ count cap τ ratio α ρ : Fraction} {fuel : List Unit}
    {products : List (Fraction × Fraction)} {s : KnapsackCostState.State}
    (ht : τ.Valid) (hratio : ratio.Valid) (hp : ρ.Valid) (hap : 0 < α.decode)
    (hprod : ∀ rv ∈ products, rv.1.Valid ∧ 0 < rv.2.decode)
    (hs : (autoCandidate δ count cap τ ratio α ρ fuel products).1 = some s) : s.Valid := by
  have hg := groupsAuto_valid δ τ ratio α ρ products ht hratio hp hap hprod
  have hm := accept_member hs
  rw [coreTokens_eq] at hm
  exact core_valid hg hm

theorem autoCandidate_width {δ count cap τ ratio α ρ : Fraction} {fuel : List Unit}
    {products : List (Fraction × Fraction)} {s : KnapsackCostState.State} {b : ℕ}
    (hd : δ.Width b) (hn : count.Width b) (ht : τ.Width b) (hratio : ratio.Width b)
    (ha : α.Width b) (hp : ρ.Width b) (hdv : δ.Valid) (hdp : 0 < δ.decode)
    (hprod : ∀ rv ∈ products, rv.1.Width b ∧ rv.2.Width b)
    (hs : (autoCandidate δ count cap τ ratio α ρ fuel products).1 = some s) :
    s.Width (kernelWidth products.length (groupWidth (4*b*(GridBounds.blockLength δ.decode+1)) b)) ∧
      s.choices.length ≤ products.length := by
  let gs := (groupsAuto δ τ ratio α ρ products).1
  let g := groupWidth (4*b*(GridBounds.blockLength δ.decode+1)) b
  have hg := groupsAuto_bounds δ τ ratio α ρ products ht hratio ha hp hdv hdp hprod
  have hlen : gs.length = products.length := by simp [gs,groupsAuto_eq]
  have hb : b ≤ g := by dsimp [g,groupWidth]; omega
  have hm := accept_member hs
  rw [coreTokens_eq] at hm
  have hfields : ∀ group ∈ gs, ∀ i ∈ group, i.value.Width g ∧ i.weight.Width g ∧ i.profit.Width g := by
    intro group hgroup i hi
    have hh := (hg group hgroup).2 i hi
    exact ⟨hh.1,hh.2.1,hh.2.2.1⟩
  have hh := core_width (KnapsackCostState.Fraction.width_mono hd hb)
    (KnapsackCostState.Fraction.width_mono hn hb) hfields hm
  simpa only [hlen] using hh

end BalancedAssortments.FPTASCostCandidate
