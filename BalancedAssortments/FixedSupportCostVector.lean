import BalancedAssortments.FixedSupportCostScale
import BalancedAssortments.ContinuousKnapsackCost

namespace BalancedAssortments.FixedSupportCostVector
open ComplexityTimeFractions (decode Valid width zero one zero_valid one_valid zero_decode one_decode)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars

def coordinate (t v y : Fraction) : Fraction × ℕ :=
  let p := multiplyFresh y v
  let s := addFresh p.1 t
  (s.1,p.2+s.2+4)

theorem coordinate_valid (t v y : Fraction) (ht : Valid t) (hv : Valid v) (hy : Valid y) :
    Valid (coordinate t v y).1 := addFresh_valid _ _ (multiplyFresh_valid _ _ hy hv) ht

theorem coordinate_decode (t v y : Fraction) (ht : Valid t) (hv : Valid v) (hy : Valid y) :
    decode (coordinate t v y).1 = decode t+decode v*decode y := by
  simp only [coordinate,addFresh_decode _ _ (multiplyFresh_valid _ _ hy hv) ht,multiplyFresh_decode]
  ring

theorem coordinate_width (t v y : Fraction) {A B C : ℕ}
    (ht : width t≤A) (hv : width v≤B) (hy : width y≤C) :
    width (coordinate t v y).1≤C+2*B+2*A+3 := by
  have hh := addFresh_width (multiplyFresh_width hy hv) ht
  change width (addFresh (multiplyFresh y v).1 t).1 ≤ _
  omega

def coordinateCost (A B C : ℕ) := 1024*(C+B+1)^2+4096*(C+2*B+1+A+1)^2+4

theorem coordinate_cost (t v y : Fraction) {A B C : ℕ}
    (ht : width t≤A) (hv : width v≤B) (hy : width y≤C) :
    (coordinate t v y).2≤coordinateCost A B C := by
  have hp := multiplyFresh_cost hy hv
  have hs := addFresh_cost (multiplyFresh_width hy hv) ht
  dsimp only [coordinate,coordinateCost]
  omega

def reconstruct {I : Type*} (t : Fraction) (rows : List (I×Product))
    (ys : List Fraction) : List (I×Fraction) × ℕ :=
  let out := mapCost (fun p => let w := coordinate t p.1.2.2 p.2; ((p.1.1,w.1),w.2+2)) (rows.zip ys)
  (out.1,out.2+4*(rows.length+ys.length+1))

@[simp] theorem reconstruct_length {I : Type*} (t : Fraction) (rows : List (I×Product))
    (ys : List Fraction) : (reconstruct t rows ys).1.length=min rows.length ys.length := by
  simp [reconstruct]

theorem reconstruct_decode {I : Type*} (t : Fraction) (rows : List (I×Product))
    (ys : List Fraction) (ht : Valid t) (hr : ∀ p ∈ rows,p.2.Valid) (hy : ∀ y ∈ ys,Valid y) :
    (reconstruct t rows ys).1.map (fun p => (p.1,decode p.2)) =
      (rows.zip ys).map (fun p => (p.1.1,decode t+decode p.1.2.2*decode p.2)) := by
  simp only [reconstruct,mapCost_value,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro p hp
  rw [coordinate_decode _ _ _ ht (hr _ (List.of_mem_zip hp).1).2 (hy _ (List.of_mem_zip hp).2)]

theorem reconstruct_valid {I : Type*} (t : Fraction) (rows : List (I×Product))
    (ys : List Fraction) (ht : Valid t) (hr : ∀ p ∈ rows,p.2.Valid) (hy : ∀ y ∈ ys,Valid y) :
    ∀ p ∈ (reconstruct t rows ys).1,Valid p.2 := by
  intro p hp
  simp only [reconstruct,mapCost_value,List.mem_map] at hp
  obtain ⟨q,hq,rfl⟩ := hp
  exact coordinate_valid _ _ _ ht (hr _ (List.of_mem_zip hq).1).2 (hy _ (List.of_mem_zip hq).2)

theorem reconstruct_bounds {I : Type*} (t : Fraction) (rows : List (I×Product))
    (ys : List Fraction) {A B C : ℕ} (ht : width t≤A)
    (hr : ∀ p ∈ rows,p.2.Width B) (hy : ∀ y ∈ ys,width y≤C) :
    (∀ p ∈ (reconstruct t rows ys).1,width p.2≤C+2*B+2*A+3) ∧
      (reconstruct t rows ys).2≤ min rows.length ys.length*(coordinateCost A B C+6)+1+
        4*(rows.length+ys.length+1) := by
  constructor
  · intro p hp
    simp only [reconstruct,mapCost_value,List.mem_map] at hp
    obtain ⟨q,hq,rfl⟩ := hp
    exact coordinate_width _ _ _ ht (hr _ (List.of_mem_zip hq).1).2 (hy _ (List.of_mem_zip hq).2)
  · have hh := mapCost_cost (fun p : (I×Product)×Fraction =>
        let w := coordinate t p.1.2.2 p.2; ((p.1.1,w.1),w.2+2)) (rows.zip ys)
      (fun p hp => Nat.add_le_add_right
        (coordinate_cost _ _ _ ht (hr _ (List.of_mem_zip hp).1).2 (hy _ (List.of_mem_zip hp).2)) 2)
    simpa only [reconstruct,List.length_zip,Nat.add_assoc] using
      Nat.add_le_add_right hh (4*(rows.length+ys.length+1))

def objective (prices weights : List Fraction) : Fraction × ℕ :=
  let products := mapCost (fun p : Fraction×Fraction => multiplyFresh p.2 p.1) (prices.zip weights)
  let num := sumAcc zero products.1
  let den := sumAcc one weights
  let out := divideFresh num.1 den.1
  (out.1,products.2+num.2+den.2+out.2+4*(prices.length+weights.length+1))

theorem objective_valid (prices weights : List Fraction)
    (hp : ∀ p ∈ prices,Valid p) (hw : ∀ w ∈ weights,Valid w) :
    Valid (objective prices weights).1 := by
  apply divideFresh_valid
  · apply sumAcc_valid _ _ zero_valid
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact multiplyFresh_valid _ _ (hw _ (List.of_mem_zip hp').2) (hp _ (List.of_mem_zip hp').1)
  · exact sumAcc_valid _ _ one_valid hw

theorem objective_decode (prices weights : List Fraction)
    (hp : ∀ p ∈ prices,Valid p) (hw : ∀ w ∈ weights,Valid w) :
    decode (objective prices weights).1 =
      ((prices.zip weights).map (fun p => decode p.1*decode p.2)).sum /
        (1+(weights.map decode).sum) := by
  have hv : ∀ x ∈ (mapCost (fun p : Fraction×Fraction => multiplyFresh p.2 p.1)
      (prices.zip weights)).1,Valid x := by
    intro x hx
    rw [mapCost_value] at hx
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp hx
    exact multiplyFresh_valid _ _ (hw _ (List.of_mem_zip hp').2) (hp _ (List.of_mem_zip hp').1)
  simp only [objective,divideFresh_decode,sumAcc_decode _ _ zero_valid hv,
    sumAcc_decode _ _ one_valid hw,zero_decode,one_decode,zero_add]
  simp [mapCost_value,List.map_map,Function.comp_def,multiplyFresh_decode,mul_comm]

def numeratorWidth (n B C : ℕ) := 1+n*(2*(C+2*B+1)+2)
def denominatorWidth (n C : ℕ) := 1+n*(2*C+2)
def objectiveWidth (n B C : ℕ) := numeratorWidth n B C+2*denominatorWidth n C+1
def objectiveCost (n B C : ℕ) :=
  (n*(1024*(C+B+1)^2+4)+1)+
  (n*(4096*(numeratorWidth n B C+(C+2*B+1)+1)^2+4)+1)+
  (n*(4096*(denominatorWidth n C+C+1)^2+4)+1)+
  (1024*(numeratorWidth n B C+denominatorWidth n C+2)^2+64*denominatorWidth n C+34)+
  4*(2*n+1)

theorem objective_bounds (prices weights : List Fraction) {n B C : ℕ}
    (hp : ∀ p ∈ prices,Valid p) (hw : ∀ w ∈ weights,Valid w)
    (hpw : ∀ p ∈ prices,width p≤B) (hww : ∀ w ∈ weights,width w≤C)
    (hpn : prices.length≤n) (hwn : weights.length≤n) :
    width (objective prices weights).1≤objectiveWidth n B C ∧
      (objective prices weights).2≤objectiveCost n B C := by
  let products := (mapCost (fun p : Fraction×Fraction => multiplyFresh p.2 p.1) (prices.zip weights)).1
  have hv : ∀ x ∈ products,Valid x := by
    intro x hx
    simp only [products,mapCost_value,List.mem_map] at hx
    obtain ⟨p,hp',rfl⟩ := hx
    exact multiplyFresh_valid _ _ (hw _ (List.of_mem_zip hp').2) (hp _ (List.of_mem_zip hp').1)
  have hxw : ∀ x ∈ products,width x≤C+2*B+1 := by
    intro x hx
    simp only [products,mapCost_value,List.mem_map] at hx
    obtain ⟨p,hp',rfl⟩ := hx
    exact multiplyFresh_width (hww _ (List.of_mem_zip hp').2) (hpw _ (List.of_mem_zip hp').1)
  have hxn : products.length≤n := by simp only [products,mapCost_length,List.length_zip];omega
  have hz : width zero≤1 := by simp
  have ho : width one≤1 := by simp
  have hnum : width (sumAcc zero products).1≤numeratorWidth n B C := by
    apply (sumAcc_width zero products hz hxw).trans
    unfold numeratorWidth
    gcongr
  have hden : width (sumAcc one weights).1≤denominatorWidth n C := by
    apply (sumAcc_width one weights ho hww).trans
    unfold denominatorWidth
    gcongr
  have hnc : (sumAcc zero products).2≤n*(4096*(numeratorWidth n B C+(C+2*B+1)+1)^2+4)+1 := by
    apply (sumAcc_cost zero products hz hxw).trans
    unfold numeratorWidth
    gcongr
  have hdc : (sumAcc one weights).2≤n*(4096*(denominatorWidth n C+C+1)^2+4)+1 := by
    apply (sumAcc_cost one weights ho hww).trans
    unfold denominatorWidth
    gcongr
  have hprod := mapCost_cost (fun p : Fraction×Fraction => multiplyFresh p.2 p.1) (prices.zip weights)
    (fun p hp => multiplyFresh_cost (hww _ (List.of_mem_zip hp).2) (hpw _ (List.of_mem_zip hp).1))
  have hpc : (mapCost (fun p : Fraction×Fraction => multiplyFresh p.2 p.1) (prices.zip weights)).2≤n*(1024*(C+B+1)^2+4)+1 := by
    apply hprod.trans
    simp only [List.length_zip]
    gcongr
    exact (min_le_left _ _).trans hpn
  have hdiv := divideFresh_cost hnum hden
  have hdw := divideFresh_width_valid hnum hden (sumAcc_valid _ _ one_valid hw)
  constructor
  · exact hdw
  · dsimp only [objective,objectiveCost]
    dsimp only [products] at *
    omega

end BalancedAssortments.FixedSupportCostVector
