import BalancedAssortments.NPCNFValidation
import BalancedAssortments.ComplexityTimeSourceParsing

namespace BalancedAssortments.NPCNF.Encoding

lemma parseCatalog_sound (xs catalog rest : List (List Bool))
    (h : (parseCatalog xs).1 = some (catalog,rest)) : catalogFields catalog++rest = xs := by
  fun_induction parseCatalog xs generalizing catalog rest
  · simp_all [catalogFields]
  · rename_i x xs tail ih
    subst tail
    cases ht : (parseCatalog xs).1 with
    | none => simp [ht] at h
    | some pair =>
      obtain ⟨vars,remaining⟩ := pair
      simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simpa only [catalogFields,List.cons_append] using congrArg ([true]::x::·) (ih _ _ ht)
  · simp_all

lemma parseClause_sound (xs : List (List Bool)) (clause : BitClause) (rest : List (List Bool))
    (h : (parseClause xs).1 = some (clause,rest)) : clauseFields clause++rest = xs := by
  fun_induction parseClause xs generalizing clause rest
  · simp_all [clauseFields]
  · rename_i sign x xs tail ih
    subst tail
    cases ht : (parseClause xs).1 with
    | none => simp [ht] at h
    | some pair =>
      obtain ⟨clause',remaining⟩ := pair
      simp only [ht,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      simpa only [clauseFields,List.cons_append] using congrArg ([sign]::x::·) (ih _ _ ht)
  · simp_all

lemma parseCatalog_cost (xs : List (List Bool)) : (parseCatalog xs).2 ≤ 8*xs.length+2 := by
  fun_induction parseCatalog xs
  · simp
  · rename_i x xs tail ih
    subst tail
    simp only [List.length_cons]
    omega
  · simp

lemma parseClause_cost (xs : List (List Bool)) : (parseClause xs).2 ≤ 8*xs.length+2 := by
  fun_induction parseClause xs
  · simp
  · rename_i sign x xs tail ih
    subst tail
    simp only [List.length_cons]
    omega
  · simp

lemma parseFormula_sound (fuel xs : List (List Bool)) (F : BitFormula) (rest : List (List Bool))
    (h : (parseFormula fuel xs).1 = some (F,rest)) : formulaFields F++rest = xs := by
  induction fuel generalizing xs F rest with
  | nil => simp [parseFormula] at h
  | cons f fuel ih =>
    cases xs with
    | nil => simp [parseFormula] at h
    | cons tag xs =>
      cases tag with
      | nil => simp [parseFormula] at h
      | cons sign more =>
        cases more with
        | cons b bs => simp [parseFormula] at h
        | nil =>
          cases sign with
          | false => simp [parseFormula] at h; rcases h with ⟨rfl,rfl⟩; rfl
          | true =>
            cases hp : (parseClause xs).1 with
            | none => simp [parseFormula,hp] at h
            | some pair =>
              obtain ⟨c,remaining⟩ := pair
              cases ht : (parseFormula fuel remaining).1 with
              | none => simp [parseFormula,hp,ht] at h
              | some tail =>
                obtain ⟨cs,r⟩ := tail
                simp [parseFormula,hp,ht] at h
                rcases h with ⟨rfl,rfl⟩
                have hc := parseClause_sound xs c remaining hp
                have hr := ih remaining cs r ht
                simp only [formulaFields,List.cons_append,List.append_assoc,hr,hc]

lemma parseFormula_cost (fuel xs : List (List Bool)) (L : ℕ) (hx : xs.length ≤ L) :
    (parseFormula fuel xs).2 ≤ fuel.length*(8*L+12)+2 := by
  induction fuel generalizing xs with
  | nil => simp [parseFormula]
  | cons f fuel ih =>
    cases xs with
    | nil => simp [parseFormula]
    | cons tag xs =>
      cases tag with
      | nil => simp [parseFormula]
      | cons sign more =>
        cases more with
        | cons b bs => simp [parseFormula]
        | nil =>
          cases sign with
          | false => simp [parseFormula]
          | true =>
            have hc := parseClause_cost xs
            have hlen : xs.length ≤ L := by simp only [List.length_cons] at hx; omega
            cases hp : (parseClause xs).1 with
            | none => simp only [parseFormula,hp,List.length_cons]; nlinarith
            | some pair =>
              obtain ⟨c,remaining⟩ := pair
              have he := parseClause_sound xs c remaining hp
              have hrlen : remaining.length ≤ L := by
                have hh := congrArg List.length he
                simp only [List.length_append] at hh
                omega
              have ht := ih remaining hrlen
              simp only [parseFormula,hp,List.length_cons]
              nlinarith

lemma pack_sound (xs : List (List Bool)) (input : Raw) (h : (pack xs).1 = some input) : fields input = xs := by
  unfold pack at h
  cases hc : (parseCatalog xs).1 with
  | none => simp [hc] at h
  | some pair =>
    obtain ⟨catalog,rest⟩ := pair
    cases hf : (parseFormula xs rest).1 with
    | none => simp [hc,hf] at h
    | some pair =>
      obtain ⟨formula,remaining⟩ := pair
      cases remaining with
      | cons b bs => simp [hc,hf] at h
      | nil =>
        simp [hc,hf] at h
        subst input
        have hcat := parseCatalog_sound xs catalog rest hc
        have hform := parseFormula_sound xs rest formula [] hf
        simp only [List.append_nil] at hform
        simpa only [fields,← hform] using hcat

lemma pack_cost (xs : List (List Bool)) : (pack xs).2 ≤ 32*(xs.length+1)^2 := by
  have hcat := parseCatalog_cost xs
  unfold pack
  cases hc : (parseCatalog xs).1 with
  | none => simp only [hc]; nlinarith
  | some pair =>
    obtain ⟨catalog,rest⟩ := pair
    have he := parseCatalog_sound xs catalog rest hc
    have hlen : rest.length ≤ xs.length := by
      have hh := congrArg List.length he
      simp only [List.length_append] at hh
      omega
    have hf := parseFormula_cost xs rest xs.length hlen
    simp only [hc]
    nlinarith

/-- Original serialized input controls all stored structural records and label
bits, even on successful parsing of noncanonical padded encodings. -/
theorem parse_measure (bits : List Bool) (input : Raw) (h : (parse bits).1 = some input) :
    ComplexityTimeSourceParsing.fieldVolume (fields input) ≤ bits.length := by
  unfold parse at h
  cases hr : (EncodingTime.parse bits).1 with
  | none => simp [hr] at h
  | some xs =>
    have hp : (pack xs).1 = some input := by simpa [hr] using h
    rw [pack_sound xs input hp]
    exact ComplexityTimeSourceParsing.parse_volume bits xs hr

/-- Total parser bound, including malformed and out-of-grammar strings. -/
theorem parse_cost (bits : List Bool) : (parse bits).2 ≤ 64*(bits.length+1)^2 := by
  have hr := EncodingTime.parse_cost bits
  have hpos : 0 < (bits.length+1)^2 := by positivity
  unfold parse
  cases he : (EncodingTime.parse bits).1 with
  | none => simp only [he]; nlinarith
  | some xs =>
    have hv := ComplexityTimeSourceParsing.parse_volume bits xs he
    have hc := ComplexityTimeSourceParsing.field_count_le_volume xs
    have hp := pack_cost xs
    have hsq := Nat.pow_le_pow_left (show xs.length+1 ≤ bits.length+1 by omega) 2
    simp only [he]
    nlinarith

end BalancedAssortments.NPCNF.Encoding
