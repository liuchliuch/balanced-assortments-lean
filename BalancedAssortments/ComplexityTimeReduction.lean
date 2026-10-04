import BalancedAssortments.ComplexityTimeBinary
import BalancedAssortments.ComplexityEncoding

namespace BalancedAssortments.ComplexityTimeReduction
open ComplexityTimeBinary ComplexityEncoding

/-- Remove redundant high-order zero bits, charging constant list work per bit. -/
def normalize : List Bool → List Bool × ℕ
  | [] => ([], 1)
  | b :: bs =>
      let r := normalize bs
      if b = false ∧ r.1 = [] then ([], r.2+4) else (b::r.1, r.2+4)

theorem normalize_value (xs : List Bool) : value (normalize xs).1 = value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [normalize]
    split_ifs with h
    · rcases h with ⟨rfl, he⟩
      simp [he, value] at ih ⊢
      omega
    · simp [value, ih]

theorem normalize_standard (xs : List Bool) : (normalize xs).1 = (value xs).bits := by
  induction xs with
  | nil => simp [normalize, value]
  | cons b bs ih =>
    simp only [normalize]
    split_ifs with h
    · rcases h with ⟨rfl, he⟩
      have hz : value bs = 0 := by
        have hh := normalize_value bs
        simp [he, value] at hh
        exact hh.symm
      simp [value, hz]
    · rw [ih]
      have hn : value bs = 0 → b = true := by
        intro hz
        simp only [ih, hz, Nat.zero_bits] at h
        cases b <;> simp_all
      have hb := Nat.bits_append_bit (value bs) b hn
      simpa [Nat.bit_val, value, Nat.add_comm] using hb.symm

theorem normalize_length (xs : List Bool) : (normalize xs).1.length ≤ xs.length := by
  induction xs with
  | nil => simp [normalize]
  | cons b bs ih => simp only [normalize]; split_ifs <;> simp_all <;> omega

theorem normalize_cost (xs : List Bool) : (normalize xs).2 = 4*xs.length+1 := by
  induction xs with
  | nil => simp [normalize]
  | cons b bs ih => simp only [normalize]; split_ifs <;> simp_all <;> omega

/-- Serialize an actual bit string, including its self-delimiting unary length.
Normalization and all list traversals are included in the cost. -/
def serializeField (xs : List Bool) : List Bool × ℕ :=
  let r := normalize xs
  (r.1.map (fun _ => true) ++ false :: r.1, r.2 + 3*r.1.length+2)

theorem serializeField_correct (xs : List Bool) :
    (serializeField xs).1 = encodeNat (value xs) := by
  simp [serializeField, normalize_standard, encodeNat, List.map_const', Nat.size_eq_bits_len]

theorem serializeField_cost (xs : List Bool) :
    (serializeField xs).2 ≤ 7*xs.length+3 := by
  have hl := normalize_length xs
  simp only [serializeField, normalize_cost]
  omega

theorem serializeField_length (xs : List Bool) :
    (serializeField xs).1.length ≤ 2*xs.length+1 := by
  have hl := normalize_length xs
  simp only [serializeField, List.length_append, List.length_map, List.length_cons]
  omega

/-- Serialize every field, charging traversal of the emitted prefix when it is
appended to the recursively produced suffix. -/
def serializeFields : List (List Bool) → List Bool × ℕ
  | [] => ([], 1)
  | x :: xs =>
      let f := serializeField x
      let r := serializeFields xs
      (f.1 ++ r.1, f.2+r.2+f.1.length+2)

theorem serializeFields_correct (xs : List (List Bool)) :
    (serializeFields xs).1 = encodeFields (xs.map value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [serializeFields, serializeField_correct, ih, encodeFields]

/-- Linear serialization time in total field-bit length, with per-field overhead. -/
theorem serializeFields_cost (xs : List (List Bool)) :
    (serializeFields xs).2 ≤ 9*(xs.map List.length).sum+6*xs.length+1 := by
  induction xs with
  | nil => simp [serializeFields]
  | cons x xs ih =>
    have hc := serializeField_cost x
    have hl := serializeField_length x
    simp only [serializeFields, List.map_cons, List.sum_cons, List.length_cons]
    omega

theorem serializeFields_cost_uniform (xs : List (List Bool)) (L : ℕ)
    (h : ∀ x ∈ xs, x.length ≤ L) :
    (serializeFields xs).2 ≤ (9*L+6)*xs.length+1 := by
  induction xs with
  | nil => simp [serializeFields]
  | cons x xs ih =>
    have hx := h x (by simp)
    have hi := ih (fun y hy => h y (by simp [hy]))
    have hc := serializeField_cost x
    have hl := serializeField_length x
    simp only [serializeFields, List.length_cons]
    nlinarith

theorem leBits_eq_decide (x y : List Bool) :
    leBits x y = decide (value x ≤ value y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact leBits_correct x y

/-- Actual oversized-item preprocessing uses the bit comparator. -/
def filterBits (B : List Bool) : List (List Bool) → List (List Bool) × ℕ
  | [] => ([], 1)
  | x :: xs =>
      let c := compareBits x B
      let r := filterBits B xs
      if c.1 = .gt then (r.1, c.2+r.2+4) else (x::r.1, c.2+r.2+4)

theorem filterBits_result (B : List Bool) (xs : List (List Bool)) :
    (filterBits B xs).1 = xs.filter (fun x => decide (value x ≤ value B)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [filterBits]
    have hc := leBits_eq_decide x B
    unfold leBits at hc
    split_ifs with h
    · simp [h] at hc
      simp [List.filter_cons, not_le.mpr hc, ih]
    · have hn : ((compareBits x B).1 != Ordering.gt) = true := by simp [h]
      rw [hn] at hc
      simp [List.filter_cons, ← hc, ih]

theorem filterBits_length (B : List Bool) (xs : List (List Bool)) :
    (filterBits B xs).1.length ≤ xs.length := by
  rw [filterBits_result]
  exact List.length_filter_le _ _

theorem filterBits_mem (B : List Bool) (xs : List (List Bool)) (x : List Bool)
    (hx : x ∈ (filterBits B xs).1) : x ∈ xs := by
  rw [filterBits_result] at hx
  exact (List.mem_filter.mp hx).1

theorem filterBits_cost (B : List Bool) (xs : List (List Bool)) (L : ℕ)
    (hB : B.length ≤ L) (hx : ∀ x ∈ xs, x.length ≤ L) :
    (filterBits B xs).2 ≤ (16*L+5)*xs.length+1 := by
  induction xs with
  | nil => simp [filterBits]
  | cons x xs ih =>
    have hi := ih (fun y hy => hx y (by simp [hy]))
    have hh := hx x (by simp)
    have hc : (compareBits x B).2 ≤ 16*L+1 := by rw [compareBits_cost]; omega
    simp only [filterBits]
    split_ifs <;> simp only [List.length_cons] <;> nlinarith

/-- Item products, using only the bit adder for the price field. -/
def generateItems (B triple : List Bool) : List (List Bool) → List (List Bool) × ℕ
  | [] => ([], 1)
  | x :: xs =>
      let p := addCarry triple x false
      let r := generateItems B triple xs
      ([p.1, [true], B, x] ++ r.1, p.2+r.2+8)

theorem generateItems_values (B triple : List Bool) (xs : List (List Bool))
    (ht : value triple = 3*value B) :
    ((generateItems B triple xs).1.map value) =
      (xs.map value).flatMap (itemFields (value B)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [generateItems, List.map_append, addCarry_value, ht, ih, itemFields, value]

theorem generateItems_length (B triple : List Bool) (xs : List (List Bool)) :
    (generateItems B triple xs).1.length = 4*xs.length := by
  induction xs with
  | nil => simp [generateItems]
  | cons x xs ih => simp [generateItems, ih]; omega

theorem generateItems_field_bound (B triple : List Bool) (xs : List (List Bool)) (L : ℕ)
    (hB : B.length ≤ L) (ht : triple.length ≤ L+2)
    (hx : ∀ x ∈ xs, x.length ≤ L) :
    ∀ x ∈ (generateItems B triple xs).1, x.length ≤ L+3 := by
  induction xs with
  | nil => simp [generateItems]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hi := ih (fun y hy => hx y (by simp [hy]))
    intro y hy
    simp only [generateItems, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with (rfl | rfl | rfl | rfl) | hy
    · rw [addCarry_length]; omega
    · simp
    · omega
    · omega
    · exact hi y hy

theorem generateItems_cost (B triple : List Bool) (xs : List (List Bool)) (L : ℕ)
    (ht : triple.length ≤ L+2) (hx : ∀ x ∈ xs, x.length ≤ L) :
    (generateItems B triple xs).2 ≤ (16*L+41)*xs.length+1 := by
  induction xs with
  | nil => simp [generateItems]
  | cons x xs ih =>
    have hxx := hx x (by simp)
    have hi := ih (fun y hy => hx y (by simp [hy]))
    have hc : (addCarry triple x false).2 ≤ 16*(L+2)+1 := by rw [addCarry_cost]; omega
    simp only [generateItems, List.length_cons]
    nlinarith

/-- Build all raw rational fields. Multiplication by three and five is implemented
with bit shifts and one ripple-carry addition each. -/
def makeFields (B : List Bool) (xs : List (List Bool)) : List (List Bool) × ℕ :=
  let triple := addCarry B (false::B) false
  let quintuple := addCarry B (false::false::B) false
  let r := generateItems B triple.1 xs
  ([[false,true], [true], [true], triple.1, [true], quintuple.1, [true], [true], [true]] ++ r.1,
    triple.2+quintuple.2+r.2+20)

theorem triple_value (B : List Bool) : value (addCarry B (false::B) false).1 = 3*value B := by
  simp [addCarry_value, value]
  omega

theorem quintuple_value (B : List Bool) :
    value (addCarry B (false::false::B) false).1 = 5*value B := by
  simp [addCarry_value, value]
  omega

theorem makeFields_values (B : List Bool) (xs : List (List Bool)) :
    (makeFields B xs).1.map value = reductionFields (value B) (xs.map value) := by
  simp [makeFields, triple_value, quintuple_value, generateItems_values B _ xs (triple_value B),
    reductionFields, anchorFields, value]

theorem makeFields_length (B : List Bool) (xs : List (List Bool)) :
    (makeFields B xs).1.length = 9+4*xs.length := by
  simp [makeFields, generateItems_length]
  omega

theorem makeFields_bound (B : List Bool) (xs : List (List Bool)) (L : ℕ)
    (hB : B.length ≤ L) (hx : ∀ x ∈ xs, x.length ≤ L) :
    ∀ x ∈ (makeFields B xs).1, x.length ≤ L+3 := by
  have ht : (addCarry B (false::B) false).1.length ≤ L+2 := by rw [addCarry_length]; simp; omega
  have hq : (addCarry B (false::false::B) false).1.length ≤ L+3 := by rw [addCarry_length]; simp; omega
  have hi := generateItems_field_bound B _ xs L hB ht hx
  intro x h
  simp only [makeFields, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with hp | h
  · rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      (try simp only [List.length_cons, List.length_nil]) <;> omega
  · exact hi x h

theorem makeFields_cost (B : List Bool) (xs : List (List Bool)) (L : ℕ)
    (hB : B.length ≤ L) (hx : ∀ x ∈ xs, x.length ≤ L) :
    (makeFields B xs).2 ≤ (16*L+41)*xs.length+32*L+100 := by
  have ht : (addCarry B (false::B) false).1.length ≤ L+2 := by rw [addCarry_length]; simp; omega
  have hc := generateItems_cost B _ xs L ht hx
  have htC : (addCarry B (false::B) false).2 ≤ 16*(L+1)+1 := by rw [addCarry_cost]; simp; omega
  have hqC : (addCarry B (false::false::B) false).2 ≤ 16*(L+2)+1 := by rw [addCarry_cost]; simp; omega
  simp only [makeFields]
  nlinarith

/-- Complete concrete binary reduction. The counter is ghost instrumentation;
all substantive operations on integer data occur on bit lists. -/
def runReduction (B : List Bool) (xs : List (List Bool)) : List Bool × ℕ :=
  let kept := filterBits B xs
  if kept.1 = [] then (encodeFields fixedNoFields, kept.2+47)
  else
    let fields := makeFields B kept.1
    let out := serializeFields fields.1
    (out.1, kept.2+fields.2+out.2+4)

theorem filterBits_standard (B : ℕ) (items : List ℕ) :
    (filterBits B.bits (items.map Nat.bits)).1 =
      (items.filter (· ≤ B)).map Nat.bits := by
  rw [filterBits_result, List.filter_map]
  simp [Function.comp_def]

/-- Exact output agreement with the fully parsed binary encoding, both branches. -/
theorem runReduction_correct (B : ℕ) (items : List ℕ) :
    (runReduction B.bits (items.map Nat.bits)).1 = completeReductionBits B items := by
  unfold runReduction completeReductionBits
  dsimp only
  rw [filterBits_standard]
  by_cases he : items.filter (· ≤ B) = []
  · simp [he]
  · have hn : (items.filter (· ≤ B)).map Nat.bits ≠ [] := by simpa using he
    simp only [he, hn, ↓reduceIte]
    rw [serializeFields_correct, makeFields_values]
    simp [Function.comp_def]

/-- Explicit quadratic bound in number of fields and maximum input field width. -/
theorem runReduction_cost (B : List Bool) (xs : List (List Bool)) (L : ℕ)
    (hB : B.length ≤ L) (hx : ∀ x ∈ xs, x.length ≤ L) :
    (runReduction B xs).2 ≤ 1000*(xs.length+1)*(L+1) := by
  have hf := filterBits_cost B xs L hB hx
  have hn := filterBits_length B xs
  have hk : ∀ x ∈ (filterBits B xs).1, x.length ≤ L :=
    fun x hx' => hx x (filterBits_mem B xs x hx')
  unfold runReduction
  dsimp only
  split_ifs
  · nlinarith
  · have hm := makeFields_cost B (filterBits B xs).1 L hB hk
    have hs := serializeFields_cost_uniform (makeFields B (filterBits B xs).1).1 (L+3)
      (makeFields_bound B (filterBits B xs).1 L hB hk)
    rw [makeFields_length] at hs
    have hnL := Nat.mul_le_mul_right L hn
    nlinarith

theorem size_le_encoded_fields (xs : List ℕ) (x : ℕ) (hx : x ∈ xs) :
    x.size ≤ (encodeFields xs).length := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    simp only [List.mem_cons] at hx
    simp only [encodeFields, List.flatMap_cons, List.length_append, encodeNat_length]
    rcases hx with rfl | hx
    · omega
    · have h := ih hx
      unfold encodeFields at h
      omega

/-- Actual bit-operation bound in the self-delimiting source serialization length.
No arithmetic oracle is counted as one step: preprocessing, arithmetic, trimming,
and output serialization are the concrete bit-list routines above. -/
theorem runReduction_binary_polynomial (B : ℕ) (items : List ℕ) :
    (runReduction B.bits (items.map Nat.bits)).1 = completeReductionBits B items ∧
    (runReduction B.bits (items.map Nat.bits)).2 ≤
      1000 * (inputLength B items + 1)^2 := by
  refine ⟨runReduction_correct B items, ?_⟩
  have hB : B.bits.length ≤ inputLength B items := by
    rw [Nat.size_eq_bits_len]
    exact target_size_le_input B items
  have hi : ∀ x ∈ items.map Nat.bits, x.length ≤ inputLength B items := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [Nat.size_eq_bits_len]
    exact size_le_encoded_fields (B::items) a (by simp [ha])
  have h := runReduction_cost B.bits (items.map Nat.bits) (inputLength B items) hB hi
  simp only [List.length_map] at h
  have hc := item_count_le_input B items
  have hcL := Nat.mul_le_mul_right (inputLength B items + 1) hc
  nlinarith

end BalancedAssortments.ComplexityTimeReduction
