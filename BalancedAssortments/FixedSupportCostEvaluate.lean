import BalancedAssortments.FixedSupportCostOrder
import BalancedAssortments.FixedSupportCostVector

namespace BalancedAssortments.FixedSupportCostEvaluate
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars
open FixedSupportCostOrder FixedSupportCostVector

def items {I : Type*} (α t : Fraction) (rows : List (Scored I)) :
    List ContinuousKnapsackCost.Item × ℕ :=
  mapCost (fun r => let c := capBits α t r.product.2;
    (⟨r.score,c.1⟩,c.2+2)) rows

def evaluateOrdered {I : Type*} (α K t : Fraction) (rows : List (Scored I)) :
    (List (I×Fraction) × Fraction) × ℕ :=
  let it := items α t rows
  let b := budgetBits K t (rows.map (fun r => r.product.2))
  let y := ContinuousKnapsackCost.solve b.1 it.1
  let w := reconstruct t (rows.map (fun r => (r.label,r.product))) y.1
  let obj := objective (rows.map (fun r => r.product.1)) (w.1.map Prod.snd)
  ((w.1,obj.1),it.2+b.2+y.2+w.2+obj.2+12*(rows.length+w.1.length+1))

theorem items_valid {I : Type*} (α t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    ∀ i ∈ (items α t rows).1,ContinuousKnapsackCost.ValidItem i := by
  intro i hi
  simp only [items,mapCost_value,List.mem_map] at hi
  obtain ⟨r,hr',rfl⟩ := hi
  exact ⟨(hr r hr').2,capBits_valid _ _ _ hα ht (hr r hr').1.2⟩

@[simp] theorem items_length {I : Type*} (α t : Fraction) (rows : List (Scored I)) :
    (items α t rows).1.length=rows.length := by simp [items]

theorem items_decode {I : Type*} (α t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    (items α t rows).1.map ContinuousKnapsackCost.decodeItem =
      rows.map (fun r => (⟨decode r.score,min 1 (decode t/(decode α*decode r.product.2))-
        decode t/decode r.product.2⟩ : ContinuousKnapsack.Item)) := by
  simp only [items,mapCost_value,List.map_map,Function.comp_def,ContinuousKnapsackCost.decodeItem]
  apply List.map_congr_left
  intro r hm
  rw [capBits_decode _ _ _ hα ht (hr r hm).1.2]

def rationalAllocation {I : Type*} (α K t : Fraction) (rows : List (Scored I)) : List ℚ :=
  (ContinuousKnapsack.solve
    (decode K-decode t*(rows.map (fun r => 1/decode r.product.2)).sum)
    (rows.map (fun r => ⟨decode r.score,min 1 (decode t/(decode α*decode r.product.2))-
      decode t/decode r.product.2⟩))).1

theorem allocation_decode {I : Type*} (α K t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (hK : Valid K) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    (ContinuousKnapsackCost.solve (budgetBits K t (rows.map (fun r => r.product.2))).1
      (items α t rows).1).1.map decode = rationalAllocation α K t rows := by
  rw [ContinuousKnapsackCost.solve_decode _ _ (budgetBits_valid _ _ _ hK ht)
    (items_valid _ _ _ hα ht hr),items_decode _ _ _ hα ht hr,
    budgetBits_decode _ _ _ hK ht]
  simp only [rationalAllocation,List.map_map,Function.comp_def]

@[simp] theorem evaluateOrdered_length {I : Type*} (α K t : Fraction) (rows : List (Scored I)) :
    (evaluateOrdered α K t rows).1.1.length=rows.length := by simp [evaluateOrdered]

theorem evaluateOrdered_valid {I : Type*} (α K t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (hK : Valid K) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    (∀ w ∈ (evaluateOrdered α K t rows).1.1,Valid w.2) ∧
      Valid (evaluateOrdered α K t rows).1.2 := by
  have hy := ContinuousKnapsackCost.solve_valid _ _ (budgetBits_valid K t (rows.map (fun r => r.product.2)) hK ht)
    (items_valid _ _ _ hα ht hr)
  have hp : ∀ p ∈ rows.map (fun r => (r.label,r.product)),p.2.Valid := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1
  have hw := reconstruct_valid _ _ _ ht hp hy
  refine ⟨hw,?_⟩
  apply objective_valid
  · intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1.1
  · intro w hw'
    obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hw'
    exact hw p hm

theorem evaluateOrdered_decode {I : Type*} (α K t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (hK : Valid K) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    (evaluateOrdered α K t rows).1.1.map (fun p => (p.1,decode p.2)) =
      (rows.zip (rationalAllocation α K t rows)).map
        (fun p => (p.1.label,decode t+decode p.1.product.2*p.2)) := by
  have hy := ContinuousKnapsackCost.solve_valid _ _ (budgetBits_valid K t (rows.map (fun r => r.product.2)) hK ht)
    (items_valid _ _ _ hα ht hr)
  have hp : ∀ p ∈ rows.map (fun r => (r.label,r.product)),p.2.Valid := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1
  change (reconstruct t _ _).1.map _ = _
  rw [reconstruct_decode _ _ _ ht hp hy,← allocation_decode _ _ _ _ hα hK ht hr]
  simp only [List.zip_map_left,List.zip_map_right,List.map_map,Function.comp_def]
  rfl

theorem evaluateOrdered_objective {I : Type*} (α K t : Fraction) (rows : List (Scored I))
    (hα : Valid α) (hK : Valid K) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score) :
    decode (evaluateOrdered α K t rows).1.2 =
      (((rows.map (fun r => r.product.1)).zip ((evaluateOrdered α K t rows).1.1.map Prod.snd)).map
        (fun p => decode p.1*decode p.2)).sum /
        (1+((evaluateOrdered α K t rows).1.1.map (fun p => decode p.2)).sum) := by
  have hw := (evaluateOrdered_valid _ _ _ _ hα hK ht hr).1
  have hp : ∀ p ∈ rows.map (fun r => r.product.1),Valid p := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1.1
  have hw' : ∀ w ∈ (evaluateOrdered α K t rows).1.1.map Prod.snd,Valid w := by
    intro w hw'
    obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hw'
    exact hw p hm
  simpa only [List.map_map,Function.comp_def] using objective_decode _ _ hp hw'

def itemWidth (W : ℕ) := 13*W+7
def budgetWidth (n W : ℕ) := 3*W+4*inverseWidth n W+4
def allocationWidth (n W : ℕ) := budgetWidth n W+n*(2*itemWidth W+2)+itemWidth W+1
def vectorWidth (n W : ℕ) := allocationWidth n W+4*W+3
def evaluationCost (n W : ℕ) :=
  (n*(capCost W W+6)+1)+budgetCost n W W+
  32768*(n+1)*(budgetWidth n W+(n+1)*(2*itemWidth W+2)+itemWidth W+4)^2+
  (n*(coordinateCost W W (allocationWidth n W)+6)+1+4*(2*n+1))+
  objectiveCost n W (vectorWidth n W)+12*(2*n+1)

set_option maxHeartbeats 1200000 in
theorem evaluateOrdered_bounds {I : Type*} (α K t : Fraction) (rows : List (Scored I)) {W : ℕ}
    (hα : Valid α) (hK : Valid K) (ht : Valid t) (hr : ∀ r ∈ rows,r.product.Valid ∧ Valid r.score)
    (hαw : width α≤W) (hKw : width K≤W) (htw : width t≤W)
    (hrw : ∀ r ∈ rows,r.product.Width W ∧ width r.score≤W) :
    (∀ p ∈ (evaluateOrdered α K t rows).1.1,width p.2≤vectorWidth rows.length W) ∧
      width (evaluateOrdered α K t rows).1.2≤objectiveWidth rows.length W (vectorWidth rows.length W) ∧
      (evaluateOrdered α K t rows).2≤evaluationCost rows.length W := by
  let vs := rows.map (fun r => r.product.2)
  let ps := rows.map (fun r => (r.label,r.product))
  let prices := rows.map (fun r => r.product.1)
  let b := (budgetBits K t vs).1
  let it := (items α t rows).1
  let y := (ContinuousKnapsackCost.solve b it).1
  let w := (reconstruct t ps y).1
  have hv : ∀ v ∈ vs,Valid v := by
    intro v hv
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hv
    exact (hr r hm).1.2
  have hvw : ∀ v ∈ vs,width v≤W := by
    intro v hv
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hv
    exact (hrw r hm).1.2
  have hp : ∀ p ∈ ps,p.2.Valid := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1
  have hpw : ∀ p ∈ ps,p.2.Width W := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hrw r hm).1
  have hpr : ∀ p ∈ prices,Valid p := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hr r hm).1.1
  have hprw : ∀ p ∈ prices,width p≤W := by
    intro p hp
    obtain ⟨r,hm,rfl⟩ := List.mem_map.mp hp
    exact (hrw r hm).1.1
  have hi := items_valid α t rows hα ht hr
  have hiw : ∀ i ∈ it,width i.score≤ itemWidth W ∧ width i.cap≤ itemWidth W := by
    intro i hi'
    simp only [it,items,mapCost_value,List.mem_map] at hi'
    obtain ⟨r,hm,rfl⟩ := hi'
    have hs := (hrw r hm).2
    have hc := capBits_width α t r.product.2 hα (hr r hm).1.2 hαw htw (hrw r hm).1.2
    dsimp only [itemWidth]
    constructor <;> dsimp only <;> omega
  have hb : Valid b := budgetBits_valid _ _ _ hK ht
  have hbw : width b≤budgetWidth rows.length W := by
    have hh := budgetBits_width K t vs hv hKw htw hvw
    simp only [vs,List.length_map] at hh
    dsimp only [b,budgetWidth,vs]
    omega
  have hbc : (budgetBits K t vs).2≤budgetCost rows.length W W := by
    simpa only [vs,List.length_map] using budgetBits_cost K t vs hv hKw htw hvw
  have hy := ContinuousKnapsackCost.solve_valid b it hb hi
  have hyw : ∀ x ∈ y,width x≤allocationWidth rows.length W := by
    have hh := ContinuousKnapsackCost.solve_width b it _ _ hbw hiw
    simpa only [it,items_length,allocationWidth] using hh
  have hyc := ContinuousKnapsackCost.solve_cost b it _ _ hbw hiw
  have hyl : y.length=rows.length := by simp [y,it]
  have hwl : w.length=rows.length := by simp [w,ps,hyl]
  have hw := reconstruct_valid t ps y ht hp hy
  have hwr := reconstruct_bounds t ps y htw hpw hyw
  have hww : ∀ p ∈ w,width p.2≤vectorWidth rows.length W := by
    intro p hm
    have hh := hwr.1 p hm
    unfold vectorWidth
    omega
  have hobj := objective_bounds prices (w.map Prod.snd) (n := rows.length) hpr
    (by intro x hx; obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hx; exact hw p hm)
    hprw (by intro x hx; obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hx; exact hww p hm)
    (by simp [prices]) (by simp [hwl])
  have hic := mapCost_cost (fun r : Scored I => let c := capBits α t r.product.2;
      ((⟨r.score,c.1⟩ : ContinuousKnapsackCost.Item),c.2+2)) rows
    (fun r hm => Nat.add_le_add_right (capBits_cost α t r.product.2 hα (hr r hm).1.2 hαw htw (hrw r hm).1.2) 2)
  refine ⟨hww,hobj.1,?_⟩
  have hwr' := hwr.2
  simp only [ps,List.length_map,hyl,min_self] at hwr'
  simp only [it,items_length] at hyc
  change (items α t rows).2+(budgetBits K t vs).2+(ContinuousKnapsackCost.solve b it).2+
    (reconstruct t ps y).2+(objective prices (w.map Prod.snd)).2+12*(rows.length+w.length+1)≤_
  change (items α t rows).2 ≤ _ at hic
  rw [hwl]
  dsimp only [evaluationCost]
  have hoc := hobj.2
  dsimp only [ps,it] at *
  norm_num only [Nat.add_assoc] at hic
  omega

end BalancedAssortments.FixedSupportCostEvaluate
