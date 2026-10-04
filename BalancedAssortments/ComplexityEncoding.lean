import Mathlib

/-! Explicit binary-size bounds for the Subset Sum reduction. These are output
encoding theorems, not a claim of membership in NP or a machine-time bound. -/
namespace BalancedAssortments.ComplexityEncoding

/-- A self-delimiting binary representation: unary bit-length followed by a zero
separator and the ordinary little-endian binary digits. -/
def encodeNat (n : ℕ) : List Bool := List.replicate n.size true ++ false :: n.bits

@[simp] theorem encodeNat_length (n : ℕ) : (encodeNat n).length = 2 * n.size + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]
  omega

def encodeFields (xs : List ℕ) : List Bool := xs.flatMap encodeNat

lemma encodeFields_length_le (xs : List ℕ) (b : ℕ) (h : ∀ x ∈ xs, x.size ≤ b) :
    (encodeFields xs).length ≤ xs.length * (2 * b + 1) := by
  induction xs with
  | nil => simp [encodeFields]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun y hy => h y (by simp [hy]))
    simp only [encodeFields, List.flatMap_cons, List.length_append, encodeNat_length,
      List.length_cons] at *
    nlinarith

/-- Multiplication by the largest coefficient in the reduction adds at most three bits. -/
theorem size_le_target_plus_three {B x : ℕ} (hx : x ≤ 5 * B) :
    x.size ≤ B.size + 3 := by
  apply Nat.size_le.mpr
  have hB := Nat.lt_size_self B
  rw [pow_add]
  norm_num
  nlinarith [Nat.two_pow_pos B.size]

/-- A product is encoded by price numerator/denominator and attraction numerator/denominator. -/
def anchorFields (B : ℕ) : List ℕ := [5 * B, 1, 1, 1]
def itemFields (B a : ℕ) : List ℕ := [3 * B + a, 1, B, a]

lemma anchor_fields_bound {B : ℕ} (hB : 0 < B) :
    ∀ x ∈ anchorFields B, x.size ≤ B.size + 3 := by
  intro x hx
  simp only [anchorFields, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    apply size_le_target_plus_three <;> omega

lemma item_fields_bound {B a : ℕ} (hB : 0 < B) (ha : a ≤ B) :
    ∀ x ∈ itemFields B a, x.size ≤ B.size + 3 := by
  intro x hx
  simp only [itemFields, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    apply size_le_target_plus_three <;> omega

lemma anchor_encoded_length {B : ℕ} (hB : 0 < B) :
    (encodeFields (anchorFields B)).length ≤ 4 * (2 * (B.size + 3) + 1) := by
  simpa [anchorFields] using encodeFields_length_le (anchorFields B) (B.size + 3)
    (anchor_fields_bound hB)

lemma item_encoded_length {B a : ℕ} (hB : 0 < B) (ha : a ≤ B) :
    (encodeFields (itemFields B a)).length ≤ 4 * (2 * (B.size + 3) + 1) := by
  simpa [itemFields] using encodeFields_length_le (itemFields B a) (B.size + 3)
    (item_fields_bound hB ha)

/-- The substantive output fields, including K, alpha and target. The number of
products is recoverable from the fixed four-field groups; a list container stores
its length separately. -/
def reductionFields (B : ℕ) (items : List ℕ) : List ℕ :=
  [2, 1, 1, 3 * B, 1] ++ anchorFields B ++ items.flatMap (itemFields B)

lemma reductionFields_length (B : ℕ) (items : List ℕ) :
    (reductionFields B items).length = 9 + 4 * items.length := by
  induction items with
  | nil => simp [reductionFields, anchorFields]
  | cons a items ih =>
    simp only [reductionFields, List.length_append, List.flatMap_cons, List.length_cons,
      List.length_nil, anchorFields, itemFields] at *
    omega

lemma reduction_fields_bound {B : ℕ} (hB : 0 < B) (items : List ℕ)
    (ha : ∀ a ∈ items, a ≤ B) :
    ∀ x ∈ reductionFields B items, x.size ≤ B.size + 3 := by
  intro x hx
  simp only [reductionFields, List.mem_append] at hx
  rcases hx with (hx | hx) | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;>
      apply size_le_target_plus_three <;> omega
  · exact anchor_fields_bound hB x hx
  · obtain ⟨a, hai, hxa⟩ := List.mem_flatMap.mp hx
    exact item_fields_bound hB (ha a hai) x hxa

/-- Linear number of output fields and a polynomial (indeed bilinear) binary-size bound. -/
theorem reduction_encoded_length {B : ℕ} (hB : 0 < B) (items : List ℕ)
    (ha : ∀ a ∈ items, a ≤ B) :
    (encodeFields (reductionFields B items)).length ≤
      (9 + 4 * items.length) * (2 * B.size + 7) := by
  have h := encodeFields_length_le (reductionFields B items) (B.size + 3)
    (reduction_fields_bound hB items ha)
  rw [reductionFields_length] at h
  convert h using 1

lemma fields_count_le_bits (xs : List ℕ) : xs.length ≤ (encodeFields xs).length := by
  induction xs with
  | nil => simp [encodeFields]
  | cons x xs ih =>
    simp only [encodeFields, List.flatMap_cons, List.length_append, encodeNat_length,
      List.length_cons] at *
    omega

/-- Bit length of the original Subset Sum data, with a self-delimiting field for B. -/
def inputLength (B : ℕ) (items : List ℕ) : ℕ := (encodeFields (B :: items)).length

lemma target_size_le_input (B : ℕ) (items : List ℕ) : B.size ≤ inputLength B items := by
  simp only [inputLength, encodeFields, List.flatMap_cons, List.length_append, encodeNat_length]
  omega

lemma item_count_le_input (B : ℕ) (items : List ℕ) : items.length ≤ inputLength B items := by
  have h := fields_count_le_bits (B :: items)
  simp only [List.length_cons] at h
  unfold inputLength
  omega

/-- An explicit quadratic bound in the actual serialized source length, including
preprocessing by deletion of oversized items. -/
theorem reduction_output_quadratic {B : ℕ} (hB : 0 < B) (items : List ℕ) :
    (encodeFields (reductionFields B (items.filter (· ≤ B)))).length ≤
      (9 + 4 * inputLength B items) * (2 * inputLength B items + 7) := by
  have hout := reduction_encoded_length hB (items.filter (· ≤ B))
    (fun a ha => by simpa using (List.mem_filter.mp ha).2)
  have hcount : (items.filter (· ≤ B)).length ≤ inputLength B items :=
    (List.length_filter_le _ _).trans (item_count_le_input B items)
  have hsize := target_size_le_input B items
  exact hout.trans (Nat.mul_le_mul (by omega) (by omega))

/-- Complete output: the source's fixed legal two-product no-instance when no
item survives preprocessing. -/
def fixedNoFields : List ℕ := [2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1]

def completeReductionBits (B : ℕ) (items : List ℕ) : List Bool :=
  let retained := items.filter (· ≤ B)
  if retained = [] then encodeFields fixedNoFields else encodeFields (reductionFields B retained)

lemma fixed_no_size : (encodeFields fixedNoFields).length = 43 := by
  have htwo : Nat.size 2 = 2 := by simpa using (Nat.size_pow (n := 1))
  simp [encodeFields, fixedNoFields, htwo]

/-- Both preprocessing branches have the same explicit quadratic output bound. -/
theorem complete_reduction_output_quadratic {B : ℕ} (hB : 0 < B) (items : List ℕ) :
    (completeReductionBits B items).length ≤
      (9 + 4 * inputLength B items) * (2 * inputLength B items + 7) := by
  unfold completeReductionBits
  dsimp only
  split_ifs
  · rw [fixed_no_size]
    nlinarith
  · exact reduction_output_quadratic hB items

/-- Decode the four natural fields as two rationals. This is a partial decoder,
rejecting any list with the wrong arity. -/
def decodeProduct : List ℕ → Option (ℚ × ℚ)
  | [rn, rd, vn, vd] => some ((rn : ℚ) / rd, (vn : ℚ) / vd)
  | _ => none

@[simp] theorem decode_anchor (B : ℕ) :
    decodeProduct (anchorFields B) = some (5 * (B : ℚ), 1) := by
  simp [decodeProduct, anchorFields]

@[simp] theorem decode_item (B a : ℕ) :
    decodeProduct (itemFields B a) = some (3 * (B : ℚ) + a, (B : ℚ) / a) := by
  simp [decodeProduct, itemFields]

end BalancedAssortments.ComplexityEncoding
