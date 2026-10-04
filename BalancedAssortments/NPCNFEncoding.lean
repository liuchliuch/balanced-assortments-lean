import BalancedAssortments.NPCNFBasic
import BalancedAssortments.EncodingTime
import BalancedAssortments.ComplexityTimeBinary

/-! A total binary grammar for catalogued CNF. All structural dimensions are
read from actual tagged records; binary label magnitudes never control loops.
Raw variable bit strings may have leading zeroes. -/
namespace BalancedAssortments.NPCNF.Encoding
open ComplexityTimeBinary

structure BitLiteral where
  labelBits : List Bool
  positive : Bool
  deriving DecidableEq, Repr

abbrev BitClause := List BitLiteral
abbrev BitFormula := List BitClause

structure Raw where
  catalog : List (List Bool)
  formula : BitFormula
  deriving DecidableEq, Repr

def BitLiteral.decode (l : BitLiteral) : Literal := ⟨value l.labelBits,l.positive⟩
def Raw.decode (input : Raw) : Catalogued :=
  ⟨input.catalog.map value,input.formula.map (List.map BitLiteral.decode)⟩

/-- Catalog fields: true,label pairs; false ends the catalog. -/
def catalogFields : List (List Bool) → List (List Bool)
  | [] => [[false]]
  | x::xs => [true]::x::catalogFields xs

/-- Clause fields: one-bit polarity,label pairs; an empty field ends a clause. -/
def clauseFields : BitClause → List (List Bool)
  | [] => [[]]
  | l::ls => [l.positive]::l.labelBits::clauseFields ls

/-- Formula fields: true begins each clause; false ends the formula. -/
def formulaFields : BitFormula → List (List Bool)
  | [] => [[false]]
  | c::cs => [true]::(clauseFields c ++ formulaFields cs)

def fields (input : Raw) : List (List Bool) := catalogFields input.catalog ++ formulaFields input.formula

/-- State-sensitive tags distinguish zero variable labels from delimiters. -/
def parseCatalog : List (List Bool) → Option (List (List Bool) × List (List Bool)) × ℕ
  | [false]::rest => (some ([],rest),2)
  | [true]::x::rest =>
      let tail := parseCatalog rest
      (tail.1.map (fun p => (x::p.1,p.2)),tail.2+6)
  | _ => (none,2)

def parseClause : List (List Bool) → Option (BitClause × List (List Bool)) × ℕ
  | []::rest => (some ([],rest),2)
  | [sign]::x::rest =>
      let tail := parseClause rest
      (tail.1.map (fun p => (⟨x,sign⟩::p.1,p.2)),tail.2+6)
  | _ => (none,2)

/-- A structural fuel list prevents malformed inputs from influencing an
unbounded recursion. Each recursive step consumes an actual formula tag. -/
def parseFormula : List (List Bool) → List (List Bool) → Option (BitFormula × List (List Bool)) × ℕ
  | [], _ => (none,1)
  | _::fuel, [false]::rest => (some ([],rest),2)
  | _::fuel, [true]::rest =>
      let clause := parseClause rest
      match clause.1 with
      | none => (none,clause.2+4)
      | some (c,remaining) =>
          let tail := parseFormula fuel remaining
          (tail.1.map (fun p => (c::p.1,p.2)),clause.2+tail.2+6)
  | _, _ => (none,2)

def pack (xs : List (List Bool)) : Option Raw × ℕ :=
  let catalog := parseCatalog xs
  match catalog.1 with
  | none => (none,catalog.2+4)
  | some (vars,rest) =>
      let formula := parseFormula xs rest
      (match formula.1 with
        | some (clauses,[]) => some ⟨vars,clauses⟩
        | _ => none,catalog.2+formula.2+6)

def parse (bits : List Bool) : Option Raw × ℕ :=
  let raw := EncodingTime.parse bits
  match raw.1 with
  | none => (none,raw.2+4)
  | some xs => let result := pack xs; (result.1,raw.2+result.2+4)

lemma parseCatalog_fields (catalog : List (List Bool)) (rest : List (List Bool)) :
    (parseCatalog (catalogFields catalog ++ rest)).1 = some (catalog,rest) := by
  induction catalog with
  | nil => rfl
  | cons x xs ih => simp [catalogFields,parseCatalog,ih]

lemma parseClause_fields (clause : BitClause) (rest : List (List Bool)) :
    (parseClause (clauseFields clause ++ rest)).1 = some (clause,rest) := by
  induction clause with
  | nil => rfl
  | cons l ls ih => simp [clauseFields,parseClause,ih]

lemma parseFormula_fields (formula : BitFormula) (rest fuel : List (List Bool))
    (hf : formula.length+1 ≤ fuel.length) :
    (parseFormula fuel (formulaFields formula ++ rest)).1 = some (formula,rest) := by
  induction formula generalizing fuel with
  | nil => cases fuel <;> simp_all [formulaFields,parseFormula]
  | cons c cs ih =>
    cases fuel with
    | nil => simp at hf
    | cons x xs =>
      have htail : cs.length+1 ≤ xs.length := by simpa using hf
      simp only [formulaFields,List.cons_append,List.append_assoc,parseFormula,parseClause_fields]
      rw [ih xs htail]
      rfl

lemma clauseFields_length (c : BitClause) : (clauseFields c).length = 2*c.length+1 := by
  induction c <;> simp_all [clauseFields] <;> omega
lemma formulaFields_length (F : BitFormula) :
    (formulaFields F).length = 2*(F.map List.length).sum+2*F.length+1 := by
  induction F <;> simp_all [formulaFields,clauseFields_length] <;> omega

lemma pack_fields (input : Raw) : (pack (fields input)).1 = some input := by
  have hf : input.formula.length+1 ≤ (fields input).length := by
    simp only [fields,List.length_append,formulaFields_length]
    omega
  have hh := parseFormula_fields input.formula [] (fields input) hf
  simp only [List.append_nil] at hh
  dsimp only [fields] at hh
  simp only [pack,fields,parseCatalog_fields,hh]

/-- Raw field framing matches the already-certified bounded binary parser. -/
def encodePayload (bits : List Bool) : List Bool := List.replicate bits.length true ++ false::bits

def encodeFields (xs : List (List Bool)) : List Bool := xs.flatMap encodePayload

def encode (input : Raw) : List Bool := encodeFields (fields input)

lemma encodePayload_length (bits : List Bool) : (encodePayload bits).length = 2*bits.length+1 := by
  simp [encodePayload]; omega

lemma encodeFields_length (xs : List (List Bool)) :
    (encodeFields xs).length = (xs.map (fun bits => 2*bits.length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeFields,ih,encodePayload_length]

lemma field_count_le_encoding (xs : List (List Bool)) : xs.length ≤ (encodeFields xs).length := by
  rw [encodeFields_length]
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega

lemma decodePayload_append (payload rest : List Bool) :
    ComplexityEncoding.decodeRawNat (encodePayload payload++rest) = some (payload,rest) := by
  unfold encodePayload ComplexityEncoding.decodeRawNat
  simp only [List.append_assoc,List.cons_append,ComplexityEncoding.readUnary_prefix]
  simp

lemma decodeRawFieldsAux_encode (xs : List (List Bool)) (fuel : ℕ) (hf : xs.length ≤ fuel) :
    ComplexityEncoding.decodeRawFieldsAux fuel (encodeFields xs) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> simp [encodeFields,ComplexityEncoding.decodeRawFieldsAux]
  | cons x xs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hne : encodePayload x++encodeFields xs ≠ [] := by
        intro he
        have hh := congrArg List.length he
        simp only [List.length_append,encodePayload_length,List.length_nil] at hh
        omega
      have hdec := decodePayload_append x (encodeFields xs)
      have ht := ih fuel (by simpa using hf)
      change ComplexityEncoding.decodeRawFieldsAux (fuel+1) (encodePayload x++encodeFields xs) = some (x::xs)
      cases he : encodePayload x++encodeFields xs with
      | nil => exact False.elim (hne he)
      | cons b bs =>
        rw [he] at hdec
        simp [ComplexityEncoding.decodeRawFieldsAux,hdec,ht]

lemma parseFields_encode (xs : List (List Bool)) : (EncodingTime.parse (encodeFields xs)).1 = some xs := by
  rw [EncodingTime.parse_correct]
  exact decodeRawFieldsAux_encode xs _ (field_count_le_encoding xs)

/-- Bit-level parsing roundtrip for every raw catalogued CNF, including empty
catalogs/formulas/clauses, zero labels and noncanonical padded label bit strings. -/
theorem parse_encode (input : Raw) : (parse (encode input)).1 = some input := by
  simp only [parse,encode,parseFields_encode,pack_fields]

end BalancedAssortments.NPCNF.Encoding
