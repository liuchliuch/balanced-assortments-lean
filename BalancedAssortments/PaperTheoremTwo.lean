import BalancedAssortments.CookLevinStackPolynomialReduction
import BalancedAssortments.NPCNFStackPolynomialReduction
import BalancedAssortments.NPSATStackPolynomialReduction
import BalancedAssortments.NPStackSourceFixedParameters
import BalancedAssortments.NPPolynomialComposition
import BalancedAssortments.ComplexityPolicyMembership

/-! Theorem 2 of Deng–Li–Liu, with all complexity dependencies closed.
NP uses actual finite-state finite-alphabet one-tape nondeterministic machines;
reductions use finite deterministic primitive Boolean-stack programs and their
proved polynomial concrete-machine simulation. The source decision predicate
is the original randomized MNL policy problem with exact aggregate balance. -/
namespace BalancedAssortments.PaperTheoremTwo
open NPStack ComplexityTimeSourceParsing

theorem np_reduces_fixed_source (L : Set (List Bool)) (hL : NPMachine.InNP L) :
    PolyManyOne L FixedSourceLanguage :=
  (((CookLevin.StackTableau.np_to_cnf L hL).trans NPCNF.StackReduction.cnf_to_three_cnf).trans
    NPSATStackReduction.three_cnf_reduces_positiveSubsetSum).trans
      NPStackSourceReduction.positiveSubsetSum_reduces_fixedSource

theorem fixed_source_npComplete : NPComplete FixedSourceLanguage :=
  ⟨SourceVerifier.Fixed.fixedSourceLanguage_inNP,np_reduces_fixed_source⟩

theorem np_reduces_source (L : Set (List Bool)) (hL : NPMachine.InNP L) :
    PolyManyOne L SourceLanguage :=
  (((CookLevin.StackTableau.np_to_cnf L hL).trans NPCNF.StackReduction.cnf_to_three_cnf).trans
    NPSATStackReduction.three_cnf_reduces_positiveSubsetSum).trans
      NPStackSourceReduction.positiveSubsetSum_reduces_source

theorem source_npComplete : NPComplete SourceLanguage :=
  ⟨SourceVerifier.sourceLanguage_inNP,np_reduces_source⟩

/-- Original randomized-assortment threshold decision is NP-complete even
when cardinality K=2 and balance alpha=1 are fixed numerically. All legal
redundant rational encodings are included, not only canonical gadget outputs. -/
theorem fixed_policy_npComplete : NPComplete FixedPolicyLanguage := by
  have he : (FixedPolicyLanguage : Set (List Bool))=FixedSourceLanguage := by
    ext word
    exact fixedPolicyLanguage_iff_source word
  rw [he]
  exact fixed_source_npComplete

/-- The unrestricted original policy language is NP-complete as well. -/
theorem policy_npComplete : NPComplete PolicyLanguage := by
  have he : (PolicyLanguage : Set (List Bool))=SourceLanguage := by
    ext word
    exact policyLanguage_iff_source word
  rw [he]
  exact source_npComplete
end BalancedAssortments.PaperTheoremTwo
