import BalancedAssortments.FixedSupportCostLists

namespace BalancedAssortments.FixedSupportCostMax
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational

/-- The exact objective is cached beside its labeled vector, avoiding repeated
objective arithmetic while scanning the polynomial candidate list. -/
abbrev Result (I : Type*) := List (I × Fraction) × Fraction

def improve {I : Type*} (a b : Result I) : Result I × ℕ :=
  let c := FixedSupportCostRational.le a.2 b.2
  (if c.1 then b else a,c.2+4)

theorem improve_member {I : Type*} (a b : Result I) : (improve a b).1=a ∨ (improve a b).1=b := by
  dsimp only [improve]
  split_ifs <;> simp

theorem improve_dominates {I : Type*} (a b : Result I) (ha : Valid a.2) (hb : Valid b.2) :
    decode a.2≤decode (improve a b).1.2 ∧ decode b.2≤decode (improve a b).1.2 := by
  have hc := le_correct a.2 b.2 ha hb
  dsimp only [improve]
  split_ifs with he
  · exact ⟨hc.mp he,le_rfl⟩
  · exact ⟨le_rfl,(lt_of_not_ge (fun h => he (hc.mpr h))).le⟩

theorem improve_valid {I : Type*} (a b : Result I) (ha : Valid a.2) (hb : Valid b.2) :
    Valid (improve a b).1.2 := by
  rcases improve_member a b with he | he <;> simp_all

theorem improve_width {I : Type*} (a b : Result I) {W : ℕ}
    (ha : width a.2≤W) (hb : width b.2≤W) : width (improve a b).1.2≤W := by
  rcases improve_member a b with he | he <;> simp_all

theorem improve_cost {I : Type*} (a b : Result I) {W : ℕ}
    (ha : width a.2≤W) (hb : width b.2≤W) :
    (improve a b).2≤2048*(2*W+1)^2+4 := by
  have hh := le_cost ha hb
  simpa only [improve,two_mul] using Nat.add_le_add_right hh 4

def scan {I : Type*} : Result I → List (Result I) → Result I × ℕ
  | a,[] => (a,1)
  | a,b::bs =>
      let c := improve a b
      let r := scan c.1 bs
      (r.1,c.2+r.2+4)

theorem scan_member {I : Type*} (a : Result I) (xs : List (Result I)) :
    (scan a xs).1=a ∨ (scan a xs).1∈xs := by
  induction xs generalizing a with
  | nil => simp [scan]
  | cons b bs ih =>
    rcases ih (improve a b).1 with he | he
    · rcases improve_member a b with hab | hab
      · exact Or.inl (he.trans hab)
      · exact Or.inr (List.mem_cons.mpr (Or.inl (he.trans hab)))
    · exact Or.inr (List.mem_cons_of_mem _ he)

theorem scan_dominates {I : Type*} (a : Result I) (xs : List (Result I))
    (ha : Valid a.2) (hx : ∀ x∈xs,Valid x.2) :
    decode a.2≤decode (scan a xs).1.2 ∧ ∀ x∈xs,decode x.2≤decode (scan a xs).1.2 := by
  induction xs generalizing a with
  | nil => simp [scan]
  | cons b bs ih =>
    have hb := hx b (by simp)
    have ht := ih (improve a b).1 (improve_valid a b ha hb) (fun x hm => hx x (by simp [hm]))
    have hc := improve_dominates a b ha hb
    refine ⟨hc.1.trans ht.1,?_⟩
    intro x hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact hc.2.trans ht.1
    · exact ht.2 x hm

theorem scan_width_cost {I : Type*} (a : Result I) (xs : List (Result I)) {W : ℕ}
    (ha : width a.2≤W) (hx : ∀ x∈xs,width x.2≤W) :
    width (scan a xs).1.2≤W ∧ (scan a xs).2≤xs.length*(2048*(2*W+1)^2+8)+1 := by
  induction xs generalizing a with
  | nil => simpa [scan] using ha
  | cons b bs ih =>
    have hb := hx b (by simp)
    have ht := ih (improve a b).1 (improve_width a b ha hb) (fun x hm => hx x (by simp [hm]))
    have hc := improve_cost a b ha hb
    refine ⟨ht.1,?_⟩
    simp only [scan,List.length_cons]
    nlinarith [ht.2]

def best {I : Type*} : List (Result I) → Option (Result I) × ℕ
  | [] => (none,1)
  | a::xs => let r := scan a xs; (some r.1,r.2+2)

theorem best_some_iff {I : Type*} (xs : List (Result I)) : (best xs).1≠none ↔ xs≠[] := by
  cases xs <;> simp [best]

theorem best_member {I : Type*} (xs : List (Result I)) {out : Result I} (h : (best xs).1=some out) : out∈xs := by
  cases xs with
  | nil => simp [best] at h
  | cons a xs =>
    have he : (scan a xs).1=out := Option.some.inj h
    rw [←he]
    exact List.mem_cons.mpr (scan_member a xs)

theorem best_dominates {I : Type*} (xs : List (Result I)) (hv : ∀ x∈xs,Valid x.2)
    {out : Result I} (h : (best xs).1=some out) : ∀ x∈xs,decode x.2≤decode out.2 := by
  cases xs with
  | nil => simp
  | cons a xs =>
    have he : (scan a xs).1=out := Option.some.inj h
    rw [←he]
    have hh := scan_dominates a xs (hv a (by simp)) (fun x hx => hv x (by simp [hx]))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh.1
    · exact hh.2 x hx

theorem best_cost {I : Type*} (xs : List (Result I)) {W : ℕ} (hx : ∀ x∈xs,width x.2≤W) :
    (best xs).2≤xs.length*(2048*(2*W+1)^2+8)+3 := by
  cases xs with
  | nil => simp [best]
  | cons a xs =>
    have hh := (scan_width_cost a xs (hx a (by simp)) (fun x hm => hx x (by simp [hm]))).2
    simp only [best,List.length_cons]
    nlinarith

end BalancedAssortments.FixedSupportCostMax
