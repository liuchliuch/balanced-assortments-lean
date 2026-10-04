import BalancedAssortments.ComplexitySourcePolicyLanguage
import BalancedAssortments.NPStackSourceMembership
import BalancedAssortments.NPStackSourceFixedMembership

/-! Conventional NP membership for the original randomized-assortment policy
languages. The compact formulation is related by a proved exact equivalence,
not used as a silently substituted decision problem. -/
namespace BalancedAssortments.ComplexityTimeSourceParsing

theorem policyLanguage_inNP : NPMachine.InNP {word | PolicyLanguage word} := by
  have he : {word | PolicyLanguage word}={word | SourceLanguage word} := by
    ext word
    exact policyLanguage_iff_source word
  rw [he]
  exact NPStack.SourceVerifier.sourceLanguage_inNP

theorem fixedPolicyLanguage_inNP : NPMachine.InNP {word | FixedPolicyLanguage word} := by
  have he : {word | FixedPolicyLanguage word}={word | FixedSourceLanguage word} := by
    ext word
    exact fixedPolicyLanguage_iff_source word
  rw [he]
  exact NPStack.SourceVerifier.Fixed.fixedSourceLanguage_inNP
end BalancedAssortments.ComplexityTimeSourceParsing
