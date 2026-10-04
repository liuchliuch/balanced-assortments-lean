import BalancedAssortments.ComplexityTimeTotalVerifier

namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeFractions

/-- Numerical header restriction. All legal redundant bit/fraction encodings
are retained; this is not a syntactic canonical-encoding restriction. -/
def FixedParameters (bits : List Bool) : Prop :=
  ∃s,(parseSource bits).1=some s ∧ value s.capacity=2 ∧ decode s.alpha=1

def FixedSourceLanguage (bits : List Bool) : Prop := SourceLanguage bits ∧ FixedParameters bits

lemma fixedSourceLanguage_iff (bits : List Bool) :
    FixedSourceLanguage bits ↔ ∃s,(parseSource bits).1=some s ∧ LegalSource s ∧ SourceYes s ∧
      value s.capacity=2 ∧ decode s.alpha=1 := by
  constructor
  · rintro ⟨⟨s,hs,hlegal,hyes⟩,t,ht,hk,ha⟩
    have he : t=s := Option.some.inj (ht.symm.trans hs)
    subst t
    exact ⟨s,hs,hlegal,hyes,hk,ha⟩
  · rintro ⟨s,hs,hlegal,hyes,hk,ha⟩
    exact ⟨⟨s,hs,hlegal,hyes⟩,s,hs,hk,ha⟩

end BalancedAssortments.ComplexityTimeSourceParsing
