import BalancedAssortments.NPCNFThreeCost

/-! A total polynomial-time many-one reduction on original Boolean input strings.
Malformed framing, invalid catalog membership, and duplicate semantic labels are
mapped to one fixed valid unsatisfiable three-CNF instance. -/
namespace BalancedAssortments.NPCNF.Encoding

def CNFLanguage (bits : List Bool) : Prop :=
  ∃ input : Raw,(parse bits).1 = some input ∧ input.decode.Valid ∧ input.decode.Sat

def ThreeCNFLanguage (bits : List Bool) : Prop :=
  ∃ input : Raw,(parse bits).1 = some input ∧ input.decode.Valid ∧
    ThreeCNF input.decode.formula ∧ input.decode.Sat

lemma CNFLanguage_encode (input : Raw) : CNFLanguage (encode input) ↔ input.decode.Valid ∧ input.decode.Sat := by
  simp [CNFLanguage,parse_encode]

lemma ThreeCNFLanguage_encode (input : Raw) :
    ThreeCNFLanguage (encode input) ↔ input.decode.Valid ∧ ThreeCNF input.decode.formula ∧ input.decode.Sat := by
  simp [ThreeCNFLanguage,parse_encode]

def unsatRaw : Raw := ⟨[],[[]]⟩

lemma unsatRaw_valid : unsatRaw.decode.Valid := by simp [Catalogued.Valid,unsatRaw,Raw.decode]
lemma unsatRaw_three : ThreeCNF unsatRaw.decode.formula := by simp [ThreeCNF,unsatRaw,Raw.decode]
lemma unsatRaw_unsat : ¬ unsatRaw.decode.Sat := by
  apply empty_clause_unsat
  simp [unsatRaw,Raw.decode]

lemma unsatRaw_measure : rawMeasure unsatRaw = 7 := by decide +kernel

/-- Every field, validation comparison, fresh-label allocation and output bit is
constructed by the preceding explicit bit/list routines. -/
def reduceBits (bits : List Bool) : List Bool × ℕ :=
  let parsed := parse bits
  match parsed.1 with
  | none =>
      let out := emit unsatRaw
      (out.1,parsed.2+out.2+4)
  | some input =>
      let checked := validate input
      if checked.1 then
        let transformed := reduceRaw input
        let out := emit transformed.1
        (out.1,parsed.2+checked.2+transformed.2+out.2+8)
      else
        let out := emit unsatRaw
        (out.1,parsed.2+checked.2+out.2+8)

/-- Satisfiability preservation for every original bit string, including invalid
inputs and every empty/short-clause case. -/
theorem reduceBits_correct (bits : List Bool) :
    ThreeCNFLanguage (reduceBits bits).1 ↔ CNFLanguage bits := by
  unfold reduceBits
  cases hp : (parse bits).1 with
  | none => simp [hp,emit_eq,ThreeCNFLanguage_encode,unsatRaw_unsat,CNFLanguage]
  | some input =>
    simp only [hp]
    have hsrc : CNFLanguage bits ↔ input.decode.Valid ∧ input.decode.Sat := by simp [CNFLanguage,hp]
    rw [hsrc]
    by_cases hv : (validate input).1 = true
    · have hvalid := (validate_correct input).mp hv
      simp only [hv,↓reduceIte,emit_eq,ThreeCNFLanguage_encode]
      rw [reduceRaw_sat_iff hvalid]
      simp only [reduceRaw_valid,reduceRaw_three,hvalid,true_and]
    · have hfalse : (validate input).1 = false := Bool.eq_false_iff.mpr hv
      have hinvalid : ¬ input.decode.Valid := fun h => hv ((validate_correct input).mpr h)
      simp [hfalse,emit_eq,ThreeCNFLanguage_encode,unsatRaw_unsat,hinvalid]

theorem reduceBits_valid_output (bits : List Bool) :
    ∃ out : Raw,(parse (reduceBits bits).1).1 = some out ∧ out.decode.Valid ∧ ThreeCNF out.decode.formula := by
  unfold reduceBits
  cases hp : (parse bits).1 with
  | none => exact ⟨unsatRaw,by simp [hp,emit_eq,parse_encode],unsatRaw_valid,unsatRaw_three⟩
  | some input =>
    simp only [hp]
    by_cases hv : (validate input).1 = true
    · refine ⟨(reduceRaw input).1,?_,reduceRaw_valid input,reduceRaw_three input⟩
      simp [hv,emit_eq,parse_encode]
    · exact ⟨unsatRaw,by simp [Bool.eq_false_iff.mpr hv,emit_eq,parse_encode],unsatRaw_valid,unsatRaw_three⟩

/-- Explicit total output-bit bound; no well-formedness or dimensional promise
is assumed about the source string. -/
theorem reduceBits_length (bits : List Bool) : (reduceBits bits).1.length ≤ 512*(bits.length+1)^2 := by
  have hfixed := emit_length unsatRaw
  rw [unsatRaw_measure] at hfixed
  have hone : 0 < (bits.length+1)^2 := by positivity
  unfold reduceBits
  cases hp : (parse bits).1 with
  | none => simp only [hp]; nlinarith
  | some input =>
    simp only [hp]
    have hsize := parsed_rawMeasure_bound hp
    have hout := reduceRaw_measure input
    have hem := emit_length (reduceRaw input).1
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 2
    split_ifs <;> simp only <;> nlinarith

/-- Fully charged bit/list polynomial time on arbitrary original input strings.
The cubic polynomial includes parsing, validation, conversion and serialization. -/
theorem reduceBits_cost (bits : List Bool) : (reduceBits bits).2 ≤ 65536*(bits.length+1)^3 := by
  have hpCost := parse_cost bits
  have hfixed := emit_cost unsatRaw
  rw [unsatRaw_measure] at hfixed
  have hone : 0 < (bits.length+1)^3 := by positivity
  have hpow : (bits.length+1)^2 ≤ (bits.length+1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  unfold reduceBits
  cases hp : (parse bits).1 with
  | none => simp only [hp]; omega
  | some input =>
    simp only [hp]
    have hsize := parsed_rawMeasure_bound hp
    have hv := validate_cost input
    have hr := reduceRaw_cost input
    have hs := reduceRaw_measure input
    have he := emit_cost (reduceRaw input).1
    have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 2
    have hcube := Nat.pow_le_pow_left (Nat.add_le_add_right hsize 1) 3
    split_ifs <;> simp only <;> omega

end BalancedAssortments.NPCNF.Encoding
