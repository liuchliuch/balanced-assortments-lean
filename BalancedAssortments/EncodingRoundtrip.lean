import BalancedAssortments.ComplexityEncoding

/-! Executable parsers and actual roundtrip correctness for the binary fields
used by the reduction. This proves serialization correctness, not machine time. -/
namespace BalancedAssortments.ComplexityEncoding

def decodeBits (xs : List Bool) : ℕ := xs.foldr Nat.bit 0

@[simp] theorem decodeBits_bits (n : ℕ) : decodeBits n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [decodeBits]
  | bit b n h ih =>
    simp only [Nat.bits_append_bit n b h, decodeBits, List.foldr_cons]
    exact congrArg (Nat.bit b) ih

/-- Read a unary length header, rejecting an unterminated header. -/
def readUnary : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: xs => some (0, xs)
  | true :: xs => (readUnary xs).map fun p => (p.1 + 1, p.2)

@[simp] theorem readUnary_prefix (k : ℕ) (xs : List Bool) :
    readUnary (List.replicate k true ++ false :: xs) = some (k, xs) := by
  induction k with
  | zero => simp [readUnary]
  | succ k ih => simp [List.replicate_succ, readUnary, ih]

/-- Parse one self-delimiting natural-number field and return the unused suffix. -/
def decodeNat (xs : List Bool) : Option (ℕ × List Bool) := do
  let (k, rest) ← readUnary xs
  if k ≤ rest.length then some (decodeBits (rest.take k), rest.drop k) else none

@[simp] theorem decodeNat_encode_append (n : ℕ) (tail : List Bool) :
    decodeNat (encodeNat n ++ tail) = some (n, tail) := by
  unfold encodeNat decodeNat
  simp only [List.append_assoc, List.cons_append, readUnary_prefix]
  simp [← Nat.size_eq_bits_len, List.take_append, List.drop_append]

@[simp] theorem decodeNat_encode (n : ℕ) : decodeNat (encodeNat n) = some (n, []) := by
  simpa using decodeNat_encode_append n []

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro a b hab
  have h := congrArg decodeNat hab
  simpa using h

/-- Parse at most `fuel` fields, consuming the entire bitstream. -/
def decodeFieldsAux : ℕ → List Bool → Option (List ℕ)
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, [] => some []
  | fuel + 1, bit :: bits => do
      let (n, rest) ← decodeNat (bit :: bits)
      let ns ← decodeFieldsAux fuel rest
      some (n :: ns)

theorem decodeFieldsAux_encode (xs : List ℕ) (fuel : ℕ) (hf : xs.length ≤ fuel) :
    decodeFieldsAux fuel (encodeFields xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> simp [encodeFields, decodeFieldsAux]
  | cons n ns ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hne : encodeNat n ++ encodeFields ns ≠ [] := by
        have hlen := encodeNat_length n
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_nil] at this
        omega
      have hdec := decodeNat_encode_append n (encodeFields ns)
      have hi := ih fuel (by simpa using hf)
      change decodeFieldsAux (fuel + 1) (encodeNat n ++ encodeFields ns) = some (n :: ns)
      cases he : encodeNat n ++ encodeFields ns with
      | nil => exact False.elim (hne he)
      | cons b bs =>
        rw [he] at hdec
        simp [decodeFieldsAux, hdec, hi]

/-- Bit length is always enough fuel: every encoded field uses at least one bit. -/
def decodeFields (bits : List Bool) : Option (List ℕ) := decodeFieldsAux bits.length bits

@[simp] theorem decodeFields_encode (xs : List ℕ) :
    decodeFields (encodeFields xs) = some xs :=
  decodeFieldsAux_encode xs _ (fields_count_le_bits xs)

theorem encodeFields_injective : Function.Injective encodeFields := by
  intro xs ys h
  have hh := congrArg decodeFields h
  simpa using hh

/-- The actual preprocessed reduction fields are recovered by the bit parser,
including the paper's fixed legal no-instance branch. -/
theorem completeReductionBits_decode (B : ℕ) (items : List ℕ) :
    decodeFields (completeReductionBits B items) =
      some (if items.filter (· ≤ B) = [] then fixedNoFields
        else reductionFields B (items.filter (· ≤ B))) := by
  unfold completeReductionBits
  dsimp only
  split_ifs <;> simp


/-- Decode the complete four-field product list. Wrong arity is rejected;
legal-instance positivity is a separate semantic obligation. -/
def decodeProducts : List ℕ → Option (List (ℚ × ℚ))
  | [] => some []
  | rn :: rd :: vn :: vd :: rest => do
      let ps ← decodeProducts rest
      some (((rn : ℚ) / rd, (vn : ℚ) / vd) :: ps)
  | _ => none

@[simp] theorem decode_item_list (B : ℕ) (items : List ℕ) :
    decodeProducts (items.flatMap (itemFields B)) =
      some (items.map fun (a : ℕ) => (3 * (B : ℚ) + (a : ℚ), (B : ℚ) / (a : ℚ))) := by
  induction items with
  | nil => simp [decodeProducts]
  | cons a items ih => simp [itemFields, decodeProducts, ih]

structure DecodedInstance where
  K : ℕ
  α : ℚ
  target : ℚ
  products : List (ℚ × ℚ)
  deriving DecidableEq, Repr

/-- The header is K, balance numerator/denominator, target numerator/denominator. -/
def decodeInstanceFields : List ℕ → Option DecodedInstance
  | K :: an :: ad :: hn :: hd :: rest => do
      let ps ← decodeProducts rest
      some ⟨K, (an : ℚ) / ad, (hn : ℚ) / hd, ps⟩
  | _ => none

def decodeInstanceBits (bits : List Bool) : Option DecodedInstance := do
  let fields ← decodeFields bits
  decodeInstanceFields fields

@[simp] theorem decode_reduction_fields (B : ℕ) (items : List ℕ) :
    decodeInstanceFields (reductionFields B items) =
      some ⟨2, 1, 3 * (B : ℚ), (5 * (B : ℚ), 1) ::
        (items.map fun (a : ℕ) => (3 * (B : ℚ) + (a : ℚ), (B : ℚ) / (a : ℚ)))⟩ := by
  simp [decodeInstanceFields, reductionFields, anchorFields, decodeProducts]

@[simp] theorem decode_fixed_no_fields :
    decodeInstanceFields fixedNoFields = some ⟨2, 1, 2, [(1, 1), (1, 1)]⟩ := by
  norm_num [decodeInstanceFields, fixedNoFields, decodeProducts]

/-- Full bits-to-instance roundtrip for both reduction branches, yielding the
paper's actual prices, attractiveness values, balance, capacity, and threshold. -/
theorem completeReductionBits_instance (B : ℕ) (items : List ℕ) :
    decodeInstanceBits (completeReductionBits B items) =
      some (if items.filter (· ≤ B) = [] then
        ⟨2, 1, 2, [(1, 1), (1, 1)]⟩ else
        ⟨2, 1, 3 * (B : ℚ), (5 * (B : ℚ), 1) ::
          ((items.filter (· ≤ B)).map fun (a : ℕ) => (3 * (B : ℚ) + (a : ℚ), (B : ℚ) / (a : ℚ)))⟩) := by
  unfold decodeInstanceBits
  rw [completeReductionBits_decode]
  split_ifs <;> simp


/-- Basic legal-instance conditions for the decoded assortment input. -/
def LegalDecoded (d : DecodedInstance) : Prop :=
  0 < d.α ∧ d.α ≤ 1 ∧ 1 ≤ d.K ∧ d.K ≤ d.products.length ∧
    ∀ p ∈ d.products, 0 < p.1 ∧ 0 < p.2

theorem completeReductionBits_legal {B : ℕ} (hB : 0 < B) (items : List ℕ)
    (hi : ∀ a ∈ items, 0 < a) :
    ∃ d, decodeInstanceBits (completeReductionBits B items) = some d ∧ LegalDecoded d := by
  rw [completeReductionBits_instance]
  split_ifs with he
  · refine ⟨_, rfl, ?_⟩
    norm_num [LegalDecoded]
  · refine ⟨_, rfl, ?_⟩
    dsimp only [LegalDecoded]
    refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩
    · have hn : 1 ≤ (items.filter (· ≤ B)).length := List.length_pos_iff.mpr he
      simp only [List.length_cons, List.length_map]
      omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · constructor
        · positivity
        · norm_num
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
        have hap : 0 < a := hi a (List.mem_filter.mp ha).1
        constructor
        · positivity
        · exact div_pos (by exact_mod_cast hB) (by exact_mod_cast hap)


/-- Header parsing consumes exactly its unary header and one separator bit. -/
theorem readUnary_length {xs rest : List Bool} {k : ℕ}
    (h : readUnary xs = some (k, rest)) : k + 1 + rest.length = xs.length := by
  induction xs generalizing k rest with
  | nil => simp [readUnary] at h
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [readUnary, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp [Nat.add_comm]
    | true =>
      cases hr : readUnary xs with
      | none => simp [readUnary, hr] at h
      | some p =>
        rcases p with ⟨m, ys⟩
        simp only [readUnary, hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hk, rfl⟩
        have hh := ih hr
        simp only [List.length_cons]
        omega

/-- Raw-bit field parser: keeps the payload bits and performs no binary-value
arithmetic. This is the interface used by a bit-operation reduction machine. -/
def decodeRawNat (xs : List Bool) : Option (List Bool × List Bool) := do
  let (k, rest) ← readUnary xs
  if k ≤ rest.length then some (rest.take k, rest.drop k) else none

@[simp] theorem decodeRawNat_encode_append (n : ℕ) (tail : List Bool) :
    decodeRawNat (encodeNat n ++ tail) = some (n.bits, tail) := by
  unfold encodeNat decodeRawNat
  simp only [List.append_assoc, List.cons_append, readUnary_prefix]
  simp [← Nat.size_eq_bits_len]

/-- A successful raw field parse strictly shortens the input, and the payload
and suffix together never exceed its original bit length. -/
theorem decodeRawNat_lengths {xs payload rest : List Bool}
    (h : decodeRawNat xs = some (payload, rest)) :
    payload.length + rest.length < xs.length := by
  unfold decodeRawNat at h
  cases hu : readUnary xs with
  | none => simp [hu] at h
  | some p =>
    rcases p with ⟨k, ys⟩
    simp only [hu] at h
    change (if k ≤ ys.length then some (ys.take k, ys.drop k) else none) = some (payload, rest) at h
    split_ifs at h with hk
    · have hh := readUnary_length hu
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [List.length_take, List.length_drop]
      omega

def decodeRawFieldsAux : ℕ → List Bool → Option (List (List Bool))
  | 0, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, [] => some []
  | fuel + 1, bit :: bits => do
      let (payload, rest) ← decodeRawNat (bit :: bits)
      let fields ← decodeRawFieldsAux fuel rest
      some (payload :: fields)

theorem decodeRawFieldsAux_encode (xs : List ℕ) (fuel : ℕ) (hf : xs.length ≤ fuel) :
    decodeRawFieldsAux fuel (encodeFields xs) = some (xs.map Nat.bits) := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> simp [encodeFields, decodeRawFieldsAux]
  | cons n ns ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hne : encodeNat n ++ encodeFields ns ≠ [] := by
        have hlen := encodeNat_length n
        intro he
        have := congrArg List.length he
        simp only [List.length_append, List.length_nil] at this
        omega
      have hdec := decodeRawNat_encode_append n (encodeFields ns)
      have hi := ih fuel (by simpa using hf)
      change decodeRawFieldsAux (fuel + 1) (encodeNat n ++ encodeFields ns) =
        some ((n :: ns).map Nat.bits)
      cases he : encodeNat n ++ encodeFields ns with
      | nil => exact False.elim (hne he)
      | cons b bs =>
        rw [he] at hdec
        simp [decodeRawFieldsAux, hdec, hi]

def decodeRawFields (bits : List Bool) : Option (List (List Bool)) :=
  decodeRawFieldsAux bits.length bits

@[simp] theorem decodeRawFields_encode (xs : List ℕ) :
    decodeRawFields (encodeFields xs) = some (xs.map Nat.bits) :=
  decodeRawFieldsAux_encode xs _ (fields_count_le_bits xs)

end BalancedAssortments.ComplexityEncoding
