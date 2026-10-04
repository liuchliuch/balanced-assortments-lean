import BalancedAssortments.NPStackSourcePolynomial
import BalancedAssortments.ComplexityTimeFixedSourceLanguage

namespace BalancedAssortments.NPStackSourceReduction
open ComplexityTimeBinary ComplexityTimeFractions ComplexityTimeSourceParsing ComplexitySourceModel

lemma reductionSpec_model (bits : List Bool) :
    ∃B items,(parseSource (reductionSpec bits)).1=some (model B items) := by
  have hfixed : ∃B items,(parseSource fixedNoSource).1=some (model B items) :=
    ⟨1,[2],sourceEncoding_parses 1 [2]⟩
  unfold reductionSpec
  cases hp : (EncodingTime.parse bits).1 with
  | none => exact hfixed
  | some fs =>
    cases fs with
    | nil => exact hfixed
    | cons b fs =>
      dsimp only
      split_ifs
      · exact ⟨value b,(fs.map value).reverse,sourceEncoding_parses _ _⟩
      · exact hfixed

/-- Every output of the actual total Subset Sum reduction, including every
malformed-input and fixed-no branch, has rank two and perfect balance. -/
theorem reductionSpec_parameters (bits : List Bool) :
    ∃s,(parseSource (reductionSpec bits)).1=some s ∧ LegalSource s ∧
      value s.capacity=2 ∧ decode s.alpha=1 := by
  obtain ⟨B,items,hp⟩ := reductionSpec_model bits
  obtain ⟨s,hs,hlegal⟩ := reductionSpec_legal bits
  have he : s=model B items := Option.some.inj (hs.symm.trans hp)
  subst s
  refine ⟨model B items,hp,hlegal,?_,?_⟩
  · simp [model]
  · simp [model]

theorem reductionSpec_fixed (bits : List Bool) : FixedParameters (reductionSpec bits) := by
  obtain ⟨s,hp,hl,hk,ha⟩ := reductionSpec_parameters bits
  exact ⟨s,hp,hk,ha⟩

theorem positiveSubsetSum_reduces_fixedSource :
    NPStack.PolyManyOne NPSATSubsetSum.PositiveSubsetSumLanguage FixedSourceLanguage := by
  refine ⟨reductionSpec,⟨polynomialReduction⟩,?_⟩
  intro bits
  constructor
  · intro h
    exact ⟨(reductionSpec_correct bits).mpr h,reductionSpec_fixed bits⟩
  · intro h
    exact (reductionSpec_correct bits).mp h.1

end BalancedAssortments.NPStackSourceReduction
