import BalancedAssortments.FixedSupportCostScale

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace BalancedAssortments.FixedSupportCostScaleList
open ComplexityTimeFractions (decode Valid width zero)
open FixedSupportCostRational FixedSupportCostLists FixedSupportCostPoints FixedSupportCostScalars FixedSupportCostScale

/-- Every prefix/suffix split, constructed with explicit charged list copying. -/
def prefixSplits {A : Type*} : List A → List (List A × List A) × ℕ
  | [] => ([([],[])],1)
  | x :: xs =>
      let r := prefixSplits xs
      (([],x::xs) :: r.1.map (fun p => (x::p.1,p.2)), r.2+8*r.1.length+4)

@[simp] theorem prefixSplits_length {A : Type*} (xs : List A) :
    (prefixSplits xs).1.length = xs.length+1 := by induction xs <;> simp [prefixSplits, *]

theorem prefixSplits_cost {A : Type*} (xs : List A) :
    (prefixSplits xs).2 ≤ 8*(xs.length+1)^2+1 := by
  induction xs with
  | nil => simp [prefixSplits]
  | cons x xs ih => simp only [prefixSplits,prefixSplits_length,List.length_cons]; nlinarith

theorem prefixSplits_append {A : Type*} (xs : List A) :
    ∀ p ∈ (prefixSplits xs).1, p.1++p.2=xs := by
  induction xs with
  | nil => simp [prefixSplits]
  | cons x xs ih =>
    intro p hp
    simp only [prefixSplits,List.mem_cons,List.mem_map] at hp
    rcases hp with rfl | ⟨q,hq,rfl⟩
    · rfl
    · simp [ih q hq]

theorem prefixSplits_take_drop {A : Type*} (xs : List A) (k : ℕ) (hk : k ≤ xs.length) :
    (xs.take k,xs.drop k) ∈ (prefixSplits xs).1 := by
  induction xs generalizing k with
  | nil =>
    have hk0 : k=0 := by simpa using hk
    subst k
    simp [prefixSplits]
  | cons x xs ih =>
    cases k with
    | zero => simp [prefixSplits]
    | succ k =>
      have hh := ih k (by simpa using hk)
      apply List.mem_cons_of_mem
      exact List.mem_map.mpr ⟨(xs.take k,xs.drop k),hh,by simp⟩

theorem prefixSplits_characterization {A : Type*} (xs : List A) {p : List A × List A}
    (hp : p ∈ (prefixSplits xs).1) :
    p.1=xs.take p.1.length ∧ p.2=xs.drop p.1.length := by
  have he := prefixSplits_append xs p hp
  rw [← he]
  simp

/-- Raw scale candidates for one already-sorted attraction list. No rational
sorting, hashing, or normalization is hidden in the enumeration. -/
def scalePoints (α K : Fraction) (vs : List Fraction) : List Fraction × ℕ :=
  let upper := scaleUpperBits K vs
  let cuts := capCutBits α upper.1 vs
  let splits := prefixSplits vs
  let roots := FPTASCostLoops.cross (fun a p =>
    let root := prefixRootBits α K a p.1 p.2
    (some root.1,root.2)) cuts.1 splits.1
  let filtered := filterCost (within upper.1) roots.1
  (cuts.1++filtered.1,upper.2+cuts.2+splits.2+roots.2+filtered.2+cuts.1.length+8)

def scaleCutWidth (n B : ℕ) : ℕ := 3*(B+upperWidth n B+1)+2

def scaleRootWidth (n B : ℕ) : ℕ := rootWidth n (B+scaleCutWidth n B+1)

def scaleWidth (n B : ℕ) : ℕ := B+upperWidth n B+scaleCutWidth n B+scaleRootWidth n B+1

def scaleCount (n : ℕ) : ℕ := (n+2)*(n+2)

theorem scalePoints_valid (α K : Fraction) (vs : List Fraction)
    (hα : Valid α) (hK : Valid K) (hv : ∀ v ∈ vs,Valid v) :
    ∀ t ∈ (scalePoints α K vs).1, Valid t := by
  have ht := scaleUpperBits_valid K vs hK hv
  have hc := capCutBits_valid α (scaleUpperBits K vs).1 vs hα ht hv
  intro t hm
  rcases List.mem_append.mp hm with hm | hm
  · exact hc t hm
  · rw [filterCost_value] at hm
    have hr := (List.mem_filter.mp hm).1
    rw [FPTASCostLoops.cross_eq] at hr
    obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨p,hp,he⟩ := List.mem_filterMap.mp hr
    have he' : (prefixRootBits α K a p.1 p.2).1=t := Option.some.inj he
    rw [← he']
    exact prefixRootBits_valid α K a p.1 p.2 hK

private theorem root_outputs_length (α K : Fraction) (cuts : List Fraction)
    (splits : List (List Fraction × List Fraction)) :
    (FPTASCostLoops.cross (fun a p => let root := prefixRootBits α K a p.1 p.2;
      (some root.1,root.2)) cuts splits).1.length = cuts.length*splits.length := by
  rw [FPTASCostLoops.cross_eq]
  simp only [List.filterMap_eq_map']
  induction cuts <;> simp [*,Nat.add_mul,Nat.add_comm]

theorem scalePoints_length (α K : Fraction) (vs : List Fraction) :
    (scalePoints α K vs).1.length ≤ scaleCount vs.length := by
  have hc := capCutBits_length α (scaleUpperBits K vs).1 vs
  have hf := List.length_filter_le (fun x => (within (scaleUpperBits K vs).1 x).1)
    (FPTASCostLoops.cross (fun a p => let root := prefixRootBits α K a p.1 p.2;
      (some root.1,root.2)) (capCutBits α (scaleUpperBits K vs).1 vs).1 (prefixSplits vs).1).1
  rw [root_outputs_length,prefixSplits_length] at hf
  simp only [scalePoints,List.length_append,filterCost_value]
  unfold scaleCount
  nlinarith

def scaleCost (n B : ℕ) : ℕ :=
  upperCost n B + cutsCost n (B+upperWidth n B+1) + (8*(n+1)^2+1) +
    ((n+2)*((n+1)*(rootCost n (B+scaleCutWidth n B+1)+5)+5)+1) +
    ((n+2)*(n+1)*(32768*(scaleWidth n B+1)^2+5)+1) + (n+2)+8

/-- Every stage is bounded in its actual raw representation; repeated finite
sums use fresh-oriented arithmetic and introduce only polynomial padding. -/
theorem scalePoints_bounds (α K : Fraction) (vs : List Fraction) {B : ℕ}
    (hα : Valid α) (hK : Valid K) (hv : ∀ v ∈ vs,Valid v)
    (hαw : width α≤B) (hKw : width K≤B) (hvw : ∀ v ∈ vs,width v≤B) :
    (∀ t ∈ (scalePoints α K vs).1,width t≤scaleWidth vs.length B) ∧
      (scalePoints α K vs).2 ≤ scaleCost vs.length B := by
  let n := vs.length
  let U := scaleUpperBits K vs
  let C := capCutBits α U.1 vs
  let P := prefixSplits vs
  let R := FPTASCostLoops.cross (fun a p => let root := prefixRootBits α K a p.1 p.2;
    (some root.1,root.2)) C.1 P.1
  have hU : width U.1≤upperWidth n B ∧ U.2≤upperCost n B := scaleUpperBits_bounds K vs hK hv hKw hvw
  have hC : (∀ t∈C.1,width t≤scaleCutWidth n B) ∧ C.2≤cutsCost n (B+upperWidth n B+1) :=
    capCutBits_bounds α U.1 vs (hαw.trans (by omega)) (hU.1.trans (by omega))
      (fun v hv' => (hvw v hv').trans (by omega))
  have hCl : C.1.length≤n+2 := capCutBits_length α U.1 vs
  have hPl : P.1.length=n+1 := prefixSplits_length vs
  have hPc : P.2≤8*(n+1)^2+1 := prefixSplits_cost vs
  have hroot : ∀ a∈C.1,∀ p∈P.1,
      width (prefixRootBits α K a p.1 p.2).1≤scaleRootWidth n B ∧
      (prefixRootBits α K a p.1 p.2).2≤rootCost n (B+scaleCutWidth n B+1) := by
    intro a ha p hp
    have he := prefixSplits_append vs p hp
    have hl : p.1.length+p.2.length=n := by simpa [n] using congrArg List.length he
    have hpv : ∀ v∈p.1,Valid v := by
      intro v hv'
      apply hv v
      rw [←he]
      exact List.mem_append_left _ hv'
    have hsv : ∀ v∈p.2,Valid v := by
      intro v hv'
      apply hv v
      rw [←he]
      exact List.mem_append_right _ hv'
    have hpw : ∀ v∈p.1,width v≤B+scaleCutWidth n B+1 := by
      intro v hv'
      have hm : v∈vs := by rw [←he]; exact List.mem_append_left _ hv'
      exact (hvw v hm).trans (by omega)
    have hsw : ∀ v∈p.2,width v≤B+scaleCutWidth n B+1 := by
      intro v hv'
      have hm : v∈vs := by rw [←he]; exact List.mem_append_right _ hv'
      exact (hvw v hm).trans (by omega)
    exact prefixRootBits_bounds α K a p.1 p.2 hα hpv hsv
      (hαw.trans (by omega)) (hKw.trans (by omega)) ((hC.1 a ha).trans (by omega)) hpw hsw (by omega) (by omega)
  have hRw : ∀ t∈R.1,width t≤scaleRootWidth n B := by
    intro t ht
    rw [FPTASCostLoops.cross_eq] at ht
    obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨p,hp,he⟩ := List.mem_filterMap.mp ht
    have he' : (prefixRootBits α K a p.1 p.2).1=t := Option.some.inj he
    rw [←he']
    exact (hroot a ha p hp).1
  have hRc : R.2≤(n+2)*((n+1)*(rootCost n (B+scaleCutWidth n B+1)+5)+5)+1 := by
    have hh := FPTASCostLoops.cross_cost
      (fun a p => let root := prefixRootBits α K a p.1 p.2; (some root.1,root.2)) C.1 P.1
      (C := rootCost n (B+scaleCutWidth n B+1))
      (fun a ha p hp => (hroot a ha p hp).2)
    rw [hPl] at hh
    apply hh.trans
    gcongr
  have hRl : R.1.length≤(n+2)*(n+1) := by
    rw [root_outputs_length,hPl]
    exact Nat.mul_le_mul_right _ hCl
  have hW : width U.1≤scaleWidth n B := hU.1.trans (by unfold scaleWidth; omega)
  have hF := filterCost_cost (within U.1) R.1
    (fun t ht => within_cost U.1 t hW ((hRw t ht).trans (by unfold scaleWidth;omega)))
  have hFc : (filterCost (within U.1) R.1).2≤(n+2)*(n+1)*(32768*(scaleWidth n B+1)^2+5)+1 := by
    apply hF.trans
    gcongr
  constructor
  · change ∀ t∈(scalePoints α K vs).1,width t≤scaleWidth n B
    intro t ht
    change t∈C.1++(filterCost (within U.1) R.1).1 at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact (hC.1 t ht).trans (by unfold scaleWidth;omega)
    · rw [filterCost_value] at ht
      exact (hRw t (List.mem_of_mem_filter ht)).trans (by unfold scaleWidth;omega)
  · change U.2+C.2+P.2+R.2+(filterCost (within U.1) R.1).2+C.1.length+8≤scaleCost n B
    unfold scaleCost
    omega

end BalancedAssortments.FixedSupportCostScaleList
