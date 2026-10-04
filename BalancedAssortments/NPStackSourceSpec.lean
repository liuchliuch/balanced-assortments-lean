import BalancedAssortments.NPStackSourceHeader
import BalancedAssortments.NPSATSubsetSumReduction
import BalancedAssortments.NPStackFieldsParsing

namespace BalancedAssortments.NPStackSourceReduction
open NPStack ComplexityTimeBinary ComplexitySourceModel NPSATSubsetSum

/-- Specification predicate only; the finite program implements positivity by
normalization followed by an empty-stack test. -/
def allPositive (fs : List (List Bool)) : Bool := fs.all (fun b => decide (0<value b))
lemma allPositive_correct (fs : List (List Bool)) : allPositive fs=true ↔ ∀ b ∈ fs,0<value b := by
  simp [allPositive]

def loopSpec (B : ℕ) (done : List ℕ) (bits : List Bool) : List Bool :=
  match (EncodingTime.parse bits).1 with
  | none => fixedNoSource
  | some fs =>
    if allPositive fs then
      let items := (fs.map value).reverse++done
      if items=[] then fixedNoSource else sourceEncoding B items
    else fixedNoSource

def reductionSpec (bits : List Bool) : List Bool :=
  match (EncodingTime.parse bits).1 with
  | some (b::fs) =>
    if 0<value b ∧ allPositive fs=true ∧ fs≠[] then
      sourceEncoding (value b) (fs.map value).reverse
    else fixedNoSource
  | _ => fixedNoSource

lemma loopSpec_nil (B : ℕ) (done : List ℕ) : loopSpec B done []=
    if done=[] then fixedNoSource else sourceEncoding B done := by
  simp [loopSpec,NPStackFields.parse_nil,allPositive]

lemma loopSpec_field (B : ℕ) (done : List ℕ) (bits payload rest : List Bool)
    (hne : bits≠[]) (hp : (EncodingTime.parseField bits).1=some (payload,rest)) :
    loopSpec B done bits=if 0<value payload then loopSpec B (value payload::done) rest else fixedNoSource := by
  have he := NPStackFields.parse_after_field bits payload rest hne hp
  unfold loopSpec
  rw [he]
  cases ht : (EncodingTime.parse rest).1 with
  | none => simp [ht]
  | some fs =>
    simp only [ht,Option.map_some,allPositive,List.all_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    by_cases hpv : 0<value payload <;> simp [hpv]

lemma loopSpec_bad (B : ℕ) (done : List ℕ) (bits : List Bool) (hne : bits≠[])
    (hp : (EncodingTime.parseField bits).1=none) : loopSpec B done bits=fixedNoSource := by
  have he : (EncodingTime.parse bits).1=none := by
    cases bits with
    | nil => contradiction
    | cons b bs => simp [EncodingTime.parse,EncodingTime.parseAux,hp]
  simp [loopSpec,he]

lemma positive_subset_sum_empty (B : ℕ) (hB : 0<B) : ¬ ListSubsetSum [] B := by
  rintro ⟨xs,hxs,h⟩
  have hx : xs=[] := List.sublist_nil.mp hxs
  simp [hx] at h
  omega

/-- The alternative direct reduction retains oversized positive items. It has
exactly the same source theorem conclusion and maps all invalid formats to a
fixed legal no-instance in the full signed source wire schema. -/
theorem reductionSpec_correct (bits : List Bool) :
    ComplexityTimeSourceParsing.SourceLanguage (reductionSpec bits) ↔ PositiveSubsetSumLanguage bits := by
  unfold reductionSpec PositiveSubsetSumLanguage
  cases hp : (EncodingTime.parse bits).1 with
  | none => simp [hp,fixedNoSource_not_mem]
  | some fields =>
    cases fields with
    | nil => simp [hp,fixedNoSource_not_mem]
    | cons b fs =>
      simp only [hp]
      by_cases hb : 0<value b
      · by_cases ha : allPositive fs=true
        · by_cases hn : fs=[]
          · subst fs
            simp [fixedNoSource_not_mem,positive_subset_sum_empty _ hb]
          · have hv := (allPositive_correct fs).mp ha
            have hvm : ∀ a ∈ fs.map value,0<a := by simpa using hv
            have hnm : fs.map value≠[] := by simpa using hn
            have he := reversed_sourceEncoding_language (value b) (fs.map value) hb hvm hnm
            simpa [hb,ha,hn] using he.trans (and_iff_right hv).symm
        · have hnv : ¬∀ x∈fs,0<value x := fun h => ha ((allPositive_correct fs).mpr h)
          simp [ha,fixedNoSource_not_mem,hnv]
      · simp [hb,fixedNoSource_not_mem]

lemma reductionSpec_field (bits payload rest : List Bool) (hne : bits≠[])
    (hp : (EncodingTime.parseField bits).1=some (payload,rest)) :
    reductionSpec bits=if 0<value payload then loopSpec (value payload) [] rest else fixedNoSource := by
  have he := NPStackFields.parse_after_field bits payload rest hne hp
  unfold reductionSpec
  rw [he]
  cases ht : (EncodingTime.parse rest).1 with
  | none => simp [loopSpec,ht]
  | some fs =>
    simp only [Option.map_some]
    by_cases hv : 0<value payload <;> by_cases ha : allPositive fs=true <;>
      by_cases hn : fs=[] <;> simp_all [loopSpec]

lemma reductionSpec_bad (bits : List Bool) (hp : (EncodingTime.parseField bits).1=none) :
    reductionSpec bits=fixedNoSource := by
  cases bits with
  | nil => simp [reductionSpec,NPStackFields.parse_nil]
  | cons b bs => simp [reductionSpec,EncodingTime.parse,EncodingTime.parseAux,hp]

/-- Every output decodes to a legal model instance, including all invalid-input
branches. The target language is never reached through an ill-formed no-instance. -/
theorem reductionSpec_legal (bits : List Bool) :
    ∃ s,(ComplexityTimeSourceParsing.parseSource (reductionSpec bits)).1=some s ∧
      ComplexityTimeSourceParsing.LegalSource s := by
  have hfixed : ∃ s,(ComplexityTimeSourceParsing.parseSource fixedNoSource).1=some s ∧
      ComplexityTimeSourceParsing.LegalSource s :=
    ⟨model 1 [2],sourceEncoding_parses 1 [2],fixedNoSource_legal⟩
  unfold reductionSpec
  cases hp : (EncodingTime.parse bits).1 with
  | none => exact hfixed
  | some fs =>
    cases fs with
    | nil => exact hfixed
    | cons b fs =>
      dsimp only
      split_ifs with h
      · have hv := (allPositive_correct fs).mp h.2.1
        have hitems : ∀ a∈(fs.map value).reverse,0<a := by
          intro a ha
          obtain ⟨x,hx,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp ha)
          exact hv x hx
        exact ⟨model (value b) (fs.map value).reverse,sourceEncoding_parses _ _,
          model_legal _ _ h.1 hitems (by simpa using h.2.2)⟩
      · exact hfixed

end BalancedAssortments.NPStackSourceReduction
