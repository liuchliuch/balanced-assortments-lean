import BalancedAssortments.DirectVerifierCleared
import BalancedAssortments.DirectVerifierSumBits

namespace BalancedAssortments.DirectVerifier
open scoped BigOperators
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions

def maxBits (a b : ZBits) : ZBits×ℕ :=
  let c := zle a b
  (if c.1 then b else a,c.2+2)

lemma maxBits_value (a b : ZBits) : zvalue (maxBits a b).1=max (zvalue a) (zvalue b) := by
  have hc := zle_correct a b
  dsimp only [maxBits]
  by_cases h : (zle a b).1=true
  · simp only [h,if_true]
    exact (max_eq_right (hc.mp h)).symm
  · have hh : zvalue b≤zvalue a := (lt_of_not_ge (fun hh => h (hc.mpr hh))).le
    simp only [Bool.not_eq_true] at h
    simp [h,max_eq_left hh]

lemma maxBits_width (a b : ZBits) : width (maxBits a b).1≤ max (width a) (width b) := by
  dsimp only [maxBits]
  split_ifs
  · exact le_max_right _ _
  · exact le_max_left _ _

def maxFoldBits : List ZBits→ZBits→ZBits×ℕ
  | [],a => (a,1)
  | b::bs,a => let c:=maxBits a b;let r:=maxFoldBits bs c.1;(r.1,c.2+r.2+4)

lemma maxFoldBits_value (xs : List ZBits) (a : ZBits) :
    zvalue (maxFoldBits xs a).1=(xs.map zvalue).foldl max (zvalue a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [maxFoldBits,ih,maxBits_value]

lemma maxFoldBits_width (xs : List ZBits) (a : ZBits) {B : ℕ}
    (ha : width a≤B) (hx : ∀ x ∈ xs,width x≤B) : width (maxFoldBits xs a).1≤B := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    apply ih _ ((maxBits_width a b).trans (max_le ha (hx b (by simp))))
    exact fun x hm => hx x (by simp [hm])

lemma maxFoldBits_cost (xs : List ZBits) (a : ZBits) {B : ℕ}
    (ha : width a≤B) (hx : ∀ x ∈ xs,width x≤B) :
    (maxFoldBits xs a).2≤xs.length*(48*B+28)+1 := by
  induction xs generalizing a with
  | nil => simp [maxFoldBits]
  | cons b bs ih =>
    have hb := hx b (by simp)
    have hh := ih (maxBits a b).1 ((maxBits_width a b).trans (max_le ha hb))
      (fun x hm => hx x (by simp [hm]))
    have hc := zle_cost a b
    dsimp only [maxBits] at hh
    dsimp only [maxFoldBits,maxBits] at ⊢
    simp only [List.length_cons]
    nlinarith [max_le ha hb]

private lemma max_fold_finset (a : ℤ) (xs : List ℤ) :
    xs.foldl max a=(insert a xs.toFinset).max' (Finset.insert_nonempty _ _) := by
  rw [List.foldl_eq_foldr]
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons,List.toFinset_cons]
    simpa only [List.toFinset_cons,Finset.insert_comm a x,ih] using
      (Finset.max'_insert x (insert a xs.toFinset) (Finset.insert_nonempty _ _)).symm

def witnessMaximum {n : ℕ} (p : Fin n→ℤ) : ℤ :=
  (insert 0 (Finset.univ.image p)).max' (Finset.insert_nonempty _ _)

lemma witnessMaximum_mem {n : ℕ} (p : Fin n→ℤ) :
    witnessMaximum p ∈ insert 0 (Finset.univ.image p) := Finset.max'_mem _ _
lemma le_witnessMaximum {n : ℕ} (p : Fin n→ℤ) (i : Fin n) : p i≤witnessMaximum p :=
  Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩))

lemma maxFoldBits_ofFn {n : ℕ} (p : Fin n→ZBits) :
    zvalue (maxFoldBits (List.ofFn p) zzero).1=witnessMaximum (fun i => zvalue (p i)) := by
  rw [maxFoldBits_value,max_fold_finset]
  have hh : ((List.ofFn p).map zvalue).toFinset=Finset.univ.image (fun i => zvalue (p i)) := by
    ext x
    simp [List.mem_ofFn,List.mem_map,Finset.mem_image]
  simp only [hh,zzero,zvalue,value,Nat.cast_zero,sub_zero,witnessMaximum]

def ClearedMax {n : ℕ} (v r : Fin n→Fraction) (α H : Fraction) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) : Prop :=
  (∀ i,0≤p i ∧ p i*(value (v i).den : ℤ)≤q*zvalue (v i).num) ∧
  (sumFold (rankTerms v p) (1,0)).2≤(K : ℤ)*q*(sumFold (rankTerms v p) (1,0)).1 ∧
  (∀ i,i∉A→p i=0) ∧
  (∀ i∈A,zvalue α.num*witnessMaximum p≤p i*(value α.den : ℤ)) ∧
  zvalue H.num*(sumFold (revenueTerms r p) (1,0)).1*(q+∑ i,p i)≤
    (sumFold (revenueTerms r p) (1,0)).2*(value H.den : ℤ)

theorem clearedMax_iff {n : ℕ} (v r : Fin n→Fraction) (α H : Fraction) (K : ℕ)
    (A : Finset (Fin n)) (p : Fin n→ℤ) (q : ℤ) (hα : 0≤zvalue α.num) :
    ClearedMax v r α H K A p q ↔ Cleared v r α H K A p q := by
  constructor
  · rintro ⟨hp,hk,ho,hb,ht⟩
    exact ⟨hp,hk,ho,(balance_max_iff p A _ _ (fun i => (hp i).1) ho hα _
      (witnessMaximum_mem p) (le_witnessMaximum p)).mpr hb,ht⟩
  · rintro ⟨hp,hk,ho,hb,ht⟩
    exact ⟨hp,hk,ho,(balance_max_iff p A _ _ (fun i => (hp i).1) ho hα _
      (witnessMaximum_mem p) (le_witnessMaximum p)).mp hb,ht⟩

end BalancedAssortments.DirectVerifier
