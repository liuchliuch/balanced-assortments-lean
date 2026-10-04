import BalancedAssortments.FPTASCostGroups
import BalancedAssortments.FPTASCostSolve

namespace BalancedAssortments.FPTASCostKernel
open ComplexityTimeBinary KnapsackCostRational FPTASCostGrid FPTASCostSeeds

def zero : Fraction := ⟨[],[true]⟩
lemma zero_valid : zero.Valid := by simp [zero,Fraction.Valid,value]
lemma zero_decode : zero.decode = 0 := by simp [zero,Fraction.decode,value]
lemma zero_width : zero.Width 1 := by simp [zero,Fraction.Width]

def maxProfitBits (groups : List (List KnapsackCostState.Item)) : Fraction × ℕ :=
  let ps := groups.flatten.map KnapsackCostState.Item.profit
  let best := foldExtreme false zero ps
  (best.1,best.2+2*groups.flatten.length+groups.length+4)

lemma maxProfitBits_valid {groups : List (List KnapsackCostState.Item)}
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) : (maxProfitBits groups).1.Valid := by
  apply foldExtreme_valid false _ _ zero_valid
  intro p hp
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hp
  obtain ⟨g,hg,hig⟩ := List.mem_flatten.mp hi'
  exact (hi g hg i hig).2.2

lemma maxProfitBits_decode {groups : List (List KnapsackCostState.Item)}
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) :
    (maxProfitBits groups).1.decode =
      FPTAS.maxList (((groups.map (List.map KnapsackCostState.Item.decode)).flatten).map Knapsack.Item.profit) := by
  have hvalid : ∀ p ∈ groups.flatten.map KnapsackCostState.Item.profit, p.Valid := by
    intro p hp
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hp
    obtain ⟨g,hg,hig⟩ := List.mem_flatten.mp hi'
    exact (hi g hg i hig).2.2
  have hh := foldExtreme_decode false zero _ zero_valid hvalid
  simpa only [maxProfitBits,FPTAS.maxList,extremum,↓reduceIte,zero_decode,
    List.map_flatten,List.map_map,Function.comp_def,KnapsackCostState.Item.decode] using hh

lemma maxProfitBits_width {groups : List (List KnapsackCostState.Item)} {b : ℕ}
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.profit.Width b) : (maxProfitBits groups).1.Width (b+1) := by
  apply foldExtreme_width false _ _ (KnapsackCostState.Fraction.width_mono zero_width (by omega))
  intro p hp
  obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hp
  obtain ⟨g,hg,hig⟩ := List.mem_flatten.mp hi'
  exact KnapsackCostState.Fraction.width_mono (hi g hg i hig) (by omega)

lemma maxProfitBits_cost {groups : List (List KnapsackCostState.Item)} {b M : ℕ}
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g, i.profit.Width b) :
    (maxProfitBits groups).2 ≤
      groups.length*M*(512*(b+2)^2+12)+groups.length+5 := by
  have hpw : ∀ p ∈ groups.flatten.map KnapsackCostState.Item.profit, p.Width (b+1) := by
    intro p hp
    obtain ⟨i,hi',rfl⟩ := List.mem_map.mp hp
    obtain ⟨g,hg,hig⟩ := List.mem_flatten.mp hi'
    exact KnapsackCostState.Fraction.width_mono ((hi g hg).2 i hig) (by omega)
  have hf := foldExtreme_cost false zero _
    (KnapsackCostState.Fraction.width_mono zero_width (show 1 ≤ b+1 by omega)) hpw
  have hl : groups.flatten.length ≤ groups.length*M := by
    simpa only [List.flatMap_id] using FPTASCost.flatMap_length_bound groups id M (fun g hg => (hi g hg).1)
  have hm := Nat.mul_le_mul_right (512*(b+2)^2+12) hl
  simp only [maxProfitBits,List.length_map,show b+1+1=b+2 by omega] at *
  nlinarith

/-- One binary knapsack kernel including max-profit selection, construction of θ,
and all scaled-profit preprocessing. Acceptance at ρ is handled by the caller. -/
def core (δ count cap : Fraction) (bound : ℕ) (groups : List (List KnapsackCostState.Item)) :
    Option KnapsackCostState.State × ℕ :=
  let maximum := maxProfitBits groups
  let test := compare zero maximum.1
  if test.1 = .lt then
    let θ := scaleBase δ maximum.1 count
    let result := KnapsackCostState.scaledSolve θ.1 cap bound groups
    (result.1,maximum.2+test.2+θ.2+result.2+8)
  else (none,maximum.2+test.2+4)

/-- Exact kernel refinement, including the no-positive-profit branch. -/
theorem core_decode (δ count cap : Fraction) (bound : ℕ)
    (groups : List (List KnapsackCostState.Item))
    (hd : δ.Valid) (hdp : 0 < δ.decode) (hn : 0 < count.decode) (hc : cap.Valid)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) :
    (core δ count cap bound groups).1.map KnapsackCostState.State.decode =
      let gs := groups.map (List.map KnapsackCostState.Item.decode)
      let pmax := FPTAS.maxList (gs.flatten.map Knapsack.Item.profit)
      if pmax ≤ 0 then none else Knapsack.solve (δ.decode*pmax/count.decode) cap.decode bound gs := by
  have hmvalid := maxProfitBits_valid hi
  have hmdecode := maxProfitBits_decode hi
  have htest := KnapsackCostState.compare_fraction_lt zero_valid hmvalid
  rw [zero_decode,hmdecode] at htest
  dsimp only
  by_cases hp : 0 < FPTAS.maxList (((groups.map (List.map KnapsackCostState.Item.decode)).flatten).map Knapsack.Item.profit)
  · have hlt := htest.mpr hp
    have htheta := scaleBase_valid hd hmvalid hn
    have htpos : 0 < (scaleBase δ (maxProfitBits groups).1 count).1.decode := by
      rw [scaleBase_decode,hmdecode]
      exact div_pos (mul_pos hdp hp) hn
    have hresult := KnapsackCostState.scaledSolve_decode (bound := bound) htheta htpos hc hi
    simp only [core,hlt,↓reduceIte,not_le.mpr hp,↓reduceIte]
    rw [hresult,scaleBase_decode,hmdecode]
  · have hnlt : (compare zero (maxProfitBits groups).1).1 ≠ .lt := fun h => hp (htest.mp h)
    simp only [core,hnlt,↓reduceIte,Option.map_none,le_of_not_gt hp,↓reduceIte]

def coreCost (N M B b : ℕ) : ℕ :=
  N*M*(512*(b+2)^2+12)+N+5 + 512*(b+2)^2 + 8192*(b+2)^2+32 +
    FPTASCost.solverBudget N M B (5*(b+1)) + 8

theorem core_cost (δ count cap : Fraction) (bound : ℕ)
    (groups : List (List KnapsackCostState.Item)) {b M : ℕ}
    (hd : δ.Width b) (hn : count.Width b) (hc : cap.Width b)
    (hi : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g,
      i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b) :
    (core δ count cap bound groups).2 ≤ coreCost groups.length M bound b := by
  have hi' := fun g hg => And.intro (hi g hg).1 (fun i hig => ((hi g hg).2 i hig).2.2)
  have hm := maxProfitBits_cost hi'
  have hmw := maxProfitBits_width (fun g hg i hig => ((hi g hg).2 i hig).2.2)
  have hzw := KnapsackCostState.Fraction.width_mono zero_width (show 1 ≤ b+1 by omega)
  have hcmp := compare_cost hzw hmw
  have hd' := KnapsackCostState.Fraction.width_mono hd (show b ≤ b+1 by omega)
  have hn' := KnapsackCostState.Fraction.width_mono hn (show b ≤ b+1 by omega)
  have htheta := scaleBase_cost hd' hmw hn'
  have htw := scaleBase_width hd' hmw hn'
  have hc' := KnapsackCostState.Fraction.width_mono hc (show b ≤ 5*(b+1) by omega)
  have hi'' : ∀ g ∈ groups, g.length ≤ M ∧ ∀ i ∈ g,
      i.value.Width (5*(b+1)) ∧ i.weight.Width (5*(b+1)) ∧ i.profit.Width (5*(b+1)) := by
    intro g hg
    refine ⟨(hi g hg).1, ?_⟩
    intro i hig
    have hh := (hi g hg).2 i hig
    exact ⟨KnapsackCostState.Fraction.width_mono hh.1 (by omega),
      KnapsackCostState.Fraction.width_mono hh.2.1 (by omega),
      KnapsackCostState.Fraction.width_mono hh.2.2 (by omega)⟩
  have hsolve := KnapsackCostState.scaledSolve_cost (bound := bound) htw hc' hi''
  change _ ≤ FPTASCost.solverBudget groups.length M bound (5*(b+1)) at hsolve
  simp only [core,coreCost]
  simp only [show b+1+1=b+2 by omega] at hcmp htheta
  split_ifs <;> omega

theorem core_valid {δ count cap : Fraction} {bound : ℕ}
    {groups : List (List KnapsackCostState.Item)} {s : KnapsackCostState.State}
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.Valid) (hs : (core δ count cap bound groups).1 = some s) :
    s.Valid := by
  simp only [core] at hs
  split_ifs at hs
  · exact KnapsackCostState.scaledSolve_valid hi hs

def kernelWidth (N b : ℕ) : ℕ := 1+N*(30*(b+1)+1)

theorem core_width {δ count cap : Fraction} {bound : ℕ}
    {groups : List (List KnapsackCostState.Item)} {s : KnapsackCostState.State} {b : ℕ}
    (hd : δ.Width b) (hn : count.Width b)
    (hi : ∀ g ∈ groups, ∀ i ∈ g, i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b)
    (hs : (core δ count cap bound groups).1 = some s) :
    s.Width (kernelWidth groups.length b) ∧ s.choices.length ≤ groups.length := by
  have hmw := maxProfitBits_width (fun g hg i hig => (hi g hg i hig).2.2)
  have hd' := KnapsackCostState.Fraction.width_mono hd (show b ≤ b+1 by omega)
  have hn' := KnapsackCostState.Fraction.width_mono hn (show b ≤ b+1 by omega)
  have htw := scaleBase_width hd' hmw hn'
  have hi' : ∀ g ∈ groups, ∀ i ∈ g,
      i.value.Width (5*(b+1)) ∧ i.weight.Width (5*(b+1)) ∧ i.profit.Width (5*(b+1)) := by
    intro g hg i hig
    have hh := hi g hg i hig
    exact ⟨KnapsackCostState.Fraction.width_mono hh.1 (by omega),
      KnapsackCostState.Fraction.width_mono hh.2.1 (by omega),
      KnapsackCostState.Fraction.width_mono hh.2.2 (by omega)⟩
  simp only [core] at hs
  split_ifs at hs
  · have hh := KnapsackCostState.scaledSolve_width htw hi' hs
    simpa only [kernelWidth,show 6*(5*(b+1))+1=30*(b+1)+1 by omega] using hh

end BalancedAssortments.FPTASCostKernel
