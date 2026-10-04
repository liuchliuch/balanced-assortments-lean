import BalancedAssortments.NPCNFThreeBits

namespace BalancedAssortments.NPCNF.Encoding
open ComplexityTimeBinary

def maxBits : List (List Bool) → List Bool × ℕ
  | [] => ([],1)
  | x::xs =>
      let tail := maxBits xs
      let cmp := compareBits x tail.1
      (if cmp.1 = .lt then tail.1 else x,tail.2+cmp.2+4)

lemma maxBits_decode (xs : List (List Bool)) : value (maxBits xs).1 = maxLabel (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hh := compareBits_correct x (maxBits xs).1
    rw [ih] at hh
    cases he : (compareBits x (maxBits xs).1).1 <;>
      simp only [he,comparisonMeaning] at hh <;>
      simp [maxBits,he,maxLabel,ih,max_eq_left,max_eq_right,hh,hh.le]

lemma maxBits_width {xs : List (List Bool)} {b : ℕ} (h : ∀ x ∈ xs,x.length ≤ b) :
    (maxBits xs).1.length ≤ b := by
  induction xs with
  | nil => simp [maxBits]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [maxBits]
    split_ifs <;> assumption

lemma maxBits_cost {xs : List (List Bool)} {b : ℕ} (h : ∀ x ∈ xs,x.length ≤ b) :
    (maxBits xs).2 ≤ xs.length*(20*(b+1))+1 := by
  induction xs with
  | nil => simp [maxBits]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs : ∀ y ∈ xs,y.length ≤ b := fun y hy => h y (by simp [hy])
    have ht := ih hxs
    have hw := maxBits_width hxs
    have hm : max x.length (maxBits xs).1.length ≤ b := max_le hx hw
    simp only [maxBits,compareBits_cost,List.length_cons]
    nlinarith

def freshBits (catalog : List (List Bool)) : List Bool × ℕ :=
  let maximum := maxBits catalog
  let next := addCarry maximum.1 [true] false
  (next.1,maximum.2+next.2+4)

lemma freshBits_decode (input : Raw) : value (freshBits input.catalog).1 = freshStart input.decode := by
  simp only [freshBits,addCarry_value,value,Bool.toNat_true,Bool.toNat_false,Nat.mul_zero,
    Nat.add_zero,maxBits_decode,freshStart,Raw.decode]

lemma freshBits_width {xs : List (List Bool)} {b : ℕ} (h : ∀ x ∈ xs,x.length ≤ b) :
    (freshBits xs).1.length ≤ b+2 := by
  have hm := maxBits_width h
  simp only [freshBits,addCarry_length,List.length_cons,List.length_nil]
  omega

lemma freshBits_cost {xs : List (List Bool)} {b : ℕ} (h : ∀ x ∈ xs,x.length ≤ b) :
    (freshBits xs).2 ≤ (xs.length+1)*(20*(b+1))+5 := by
  have hc := maxBits_cost h
  have hw := maxBits_width h
  have hm : max (maxBits xs).1.length 1 ≤ b+1 := by omega
  simp only [freshBits,addCarry_cost,List.length_cons,List.length_nil]
  simp only [Nat.zero_add]
  nlinarith

/-- Output catalog construction scans only actual output literals. -/
def rawLabels (F : BitFormula) : List (List Bool) := F.flatten.map BitLiteral.labelBits

def catalogueBits (F : BitFormula) : Raw × ℕ :=
  let labels := rawLabels F
  let catalog := dedupLabels labels
  (⟨catalog.1,F⟩,catalog.2+2*F.flatten.length+F.length+4)

lemma catalogueBits_decode (F : BitFormula) : (catalogueBits F).1.decode = catalogue (F.map (List.map BitLiteral.decode)) := by
  simp only [catalogueBits,Raw.decode,catalogue,variableCatalog,variableLabels,dedupLabels_decode,
    rawLabels,List.map_map,List.map_flatten]
  simp only [Function.comp_def,List.map_map,BitLiteral.decode]

def reduceRaw (input : Raw) : Raw × ℕ :=
  let start := freshBits input.catalog
  let result := bitFormula start.1 input.formula
  let catalogued := catalogueBits result.1.1
  (catalogued.1,start.2+result.2+catalogued.2+8)

/-- Refinement of the entire raw-binary conversion, including fresh labels and
reconstruction of a finite duplicate-free output variable catalog. -/
theorem reduceRaw_decode (input : Raw) : (reduceRaw input).1.decode = reduceThree input.decode := by
  have h := congrArg Prod.fst (bitFormula_decode (freshBits input.catalog).1 input.formula)
  rw [freshBits_decode] at h
  change (catalogueBits (bitFormula (freshBits input.catalog).1 input.formula).1.1).1.decode = _
  rw [catalogueBits_decode]
  change catalogue _ = catalogue _
  apply congrArg catalogue
  exact h

theorem reduceRaw_valid (input : Raw) : (reduceRaw input).1.decode.Valid := by
  rw [reduceRaw_decode]
  exact reduceThree_valid _

theorem reduceRaw_three (input : Raw) : ThreeCNF (reduceRaw input).1.decode.formula := by
  rw [reduceRaw_decode]
  exact reduceThree_three _

theorem reduceRaw_sat_iff {input : Raw} (h : input.decode.Valid) :
    (reduceRaw input).1.decode.Sat ↔ input.decode.Sat := by
  rw [reduceRaw_decode]
  exact reduceThree_sat_iff h

end BalancedAssortments.NPCNF.Encoding
