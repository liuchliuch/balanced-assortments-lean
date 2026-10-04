import BalancedAssortments.EncodingRoundtrip

/-! An instrumented parser using only bit/list pattern matching and constructors.
Header lengths are represented by lists, never decoded as binary integers.
The natural-number second components are cost annotations, erased from the
parsed result; each inspected bit or constructed list cell is charged constant
cost, and no numeric-value arithmetic is performed by the parser. -/
namespace BalancedAssortments.EncodingTime
open ComplexityEncoding

def scanHeader : List Bool → Option (List Bool × List Bool) × ℕ
  | [] => (none, 1)
  | false :: xs => (some ([], xs), 2)
  | true :: xs =>
      let p := scanHeader xs
      (p.1.map (fun h => (true :: h.1, h.2)), p.2 + 4)

theorem scanHeader_correct (xs : List Bool) :
    (scanHeader xs).1.map (fun h => (h.1.length, h.2)) = readUnary xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [scanHeader, readUnary, Option.map_map, Function.comp_def, ← ih]

theorem scanHeader_cost (xs : List Bool) : (scanHeader xs).2 ≤ 4 * xs.length + 2 := by
  induction xs with
  | nil => simp [scanHeader]
  | cons b xs ih => cases b <;> simp only [scanHeader, List.length_cons] <;> omega

/-- Consume one payload bit for each unary header marker. -/
def consume : List Bool → List Bool → Option (List Bool × List Bool) × ℕ
  | [], xs => (some ([], xs), 1)
  | _ :: _, [] => (none, 1)
  | _ :: hs, b :: bs =>
      let p := consume hs bs
      (p.1.map (fun r => (b :: r.1, r.2)), p.2 + 4)

theorem consume_correct (hs xs : List Bool) :
    (consume hs xs).1 = if hs.length ≤ xs.length then
      some (xs.take hs.length, xs.drop hs.length) else none := by
  induction hs generalizing xs with
  | nil => simp [consume]
  | cons h hs ih =>
    cases xs with
    | nil => simp [consume]
    | cons b bs => simp [consume, ih, List.take_succ_cons, List.drop_succ_cons]

theorem consume_cost (hs xs : List Bool) : (consume hs xs).2 ≤ 4 * hs.length + 1 := by
  induction hs generalizing xs with
  | nil => simp [consume]
  | cons h hs ih =>
    cases xs with
    | nil => simp [consume]
    | cons b bs => have hh := ih bs; simp only [consume, List.length_cons]; omega

def parseField (xs : List Bool) : Option (List Bool × List Bool) × ℕ :=
  let h := scanHeader xs
  match h.1 with
  | none => (none, h.2 + 2)
  | some (header, rest) =>
      let p := consume header rest
      (p.1, h.2 + p.2 + 2)

theorem parseField_correct (xs : List Bool) : (parseField xs).1 = decodeRawNat xs := by
  have hh := scanHeader_correct xs
  unfold parseField decodeRawNat
  cases he : (scanHeader xs).1 with
  | none => simp [he] at hh; simp [he, ← hh]
  | some h =>
    rcases h with ⟨header, rest⟩
    simp only [he, Option.map_some] at hh
    simp [he, ← hh, consume_correct]

theorem parseField_cost (xs : List Bool) : (parseField xs).2 ≤ 8 * xs.length + 5 := by
  have hc := scanHeader_cost xs
  unfold parseField
  cases he : (scanHeader xs).1 with
  | none => simp only [he]; omega
  | some h =>
    rcases h with ⟨header, rest⟩
    have hh := scanHeader_correct xs
    rw [he] at hh
    have hl := readUnary_length hh.symm
    dsimp only at hl
    have hp := consume_cost header rest
    simp only [he]
    omega

/-- The original bit list supplies fuel, avoiding an uncharged numeric counter. -/
def parseAux : List Bool → List Bool → Option (List (List Bool)) × ℕ
  | [], [] => (some [], 1)
  | [], _ :: _ => (none, 1)
  | _ :: _, [] => (some [], 1)
  | _ :: fuel, b :: bs =>
      let p := parseField (b :: bs)
      match p.1 with
      | none => (none, p.2 + 3)
      | some (payload, rest) =>
          let r := parseAux fuel rest
          (r.1.map (payload :: ·), p.2 + r.2 + 3)

theorem parseAux_correct (fuel xs : List Bool) :
    (parseAux fuel xs).1 = decodeRawFieldsAux fuel.length xs := by
  induction fuel generalizing xs with
  | nil => cases xs <;> rfl
  | cons f fuel ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      simp only [parseAux, List.length_cons, decodeRawFieldsAux]
      rw [← parseField_correct]
      cases he : (parseField (b :: bs)).1 with
      | none => simp
      | some p =>
        rcases p with ⟨payload, rest⟩
        simp only [ih]
        change Option.map (fun fields => payload :: fields) (decodeRawFieldsAux fuel.length rest) =
          (decodeRawFieldsAux fuel.length rest).bind (fun fields => some (payload :: fields))
        cases hh : decodeRawFieldsAux fuel.length rest <;> rfl

theorem parseAux_cost (fuel xs : List Bool) (L : ℕ) (hx : xs.length ≤ L) :
    (parseAux fuel xs).2 ≤ 20 * (fuel.length + 1) * (L + 1) := by
  induction fuel generalizing xs with
  | nil => cases xs <;> simp [parseAux] <;> omega
  | cons f fuel ih =>
    cases xs with
    | nil => simp [parseAux]; nlinarith
    | cons b bs =>
      have hp := parseField_cost (b :: bs)
      simp only [parseAux]
      cases he : (parseField (b :: bs)).1 with
      | none => simp only [he]; simp only [List.length_cons] at *; nlinarith
      | some p =>
        rcases p with ⟨payload, rest⟩
        have hrest := decodeRawNat_lengths (by rw [← parseField_correct]; exact he)
        have hi := ih rest (by omega : rest.length ≤ L)
        simp only [he, List.length_cons] at *
        nlinarith

def parse (xs : List Bool) : Option (List (List Bool)) × ℕ := parseAux xs xs

theorem parse_correct (xs : List Bool) : (parse xs).1 = decodeRawFields xs :=
  parseAux_correct xs xs

theorem parse_cost (xs : List Bool) : (parse xs).2 ≤ 20 * (xs.length + 1)^2 := by
  have hh := parseAux_cost xs xs xs.length le_rfl
  simpa [parse, pow_two, Nat.mul_assoc] using hh

theorem parse_encoded (xs : List ℕ) :
    (parse (encodeFields xs)).1 = some (xs.map Nat.bits) ∧
      (parse (encodeFields xs)).2 ≤ 20 * ((encodeFields xs).length + 1)^2 := by
  exact ⟨by rw [parse_correct, decodeRawFields_encode], parse_cost _⟩

end BalancedAssortments.EncodingTime
