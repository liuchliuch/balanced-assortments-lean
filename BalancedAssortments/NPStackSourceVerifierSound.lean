import BalancedAssortments.NPStackSourceVerifierProgramCorrect
import BalancedAssortments.NPStackSourceVerifierSemantics
import BalancedAssortments.NPStackSourceFramingSound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

/-- Soundness of every accepting execution of the literal finite verifier,
including arbitrary guessed certificate words and redundant signed encodings. -/
theorem concrete_source_sound (word : List Bool) (fields : List (List Bool)) (candidate : List Bool)
    {T : ℕ} {out : Config SourceVerifier.Stack (Whole.State Balance.LoopState)}
    (hp : (EncodingTime.parse word).1=some fields)
    (hr : Run Whole.concreteProgram T (Framing.bodyInput Whole.concreteProgram fields candidate) out)
    (ha : accepts Whole.concreteProgram out) : SourceLanguage word := by
  obtain ⟨sh,ch,rs,hs,hc,hrows,hh,hrank,hrev,hbal⟩ := Whole.accepted_conditions (NPStackFields.dataFields fields) candidate hr ha
  have hfields := Whole.dataFields_injective hs
  have hmask := RowsValid_masks rs _ hrows
  have hconditions : semanticConditions sh ch rs := by
    simpa only [semanticConditions,Whole.scalarStart,Whole.rowEnd,Whole.afterHeader,Whole.afterRank,
      Whole.afterRevenue,Whole.balanceTriples,header_effect,finalRegisters] using
      And.intro hrows (And.intro hh (And.intro hrank (And.intro hrev hbal)))
  have hv := (semanticConditions_iff sh ch rs hmask).mp hconditions
  have hpack : (packSource fields).1=some (parsedSource sh rs) := by
    rw [hfields]
    exact packSource_records sh rs
  have hparse : (parseSource word).1=some (parsedSource sh rs) := by
    simp [parseSource,hp,hpack]
  exact ⟨parsedSource sh rs,hparse,verifyParsed_sound _ _ hv⟩

/-- The actual finite nondeterministic guess-and-verify machine has no false
accepting branch on the exact original raw source language. -/
theorem guessed_source_sound (word : List Bool) {T : ℕ}
    {out : Config Framing.Stack (Guess.State (Framing.State (Whole.State Balance.LoopState)))}
    (hr : Run (Framing.guessedProgram Whole.concreteProgram) T
      (initial (Framing.guessedProgram Whole.concreteProgram) word) out)
    (ha : accepts (Framing.guessedProgram Whole.concreteProgram) out) : SourceLanguage word := by
  obtain ⟨fields,candidate,t,e,hp,he,hh⟩ := Framing.guessed_sound Whole.concreteProgram word hr ha
  exact concrete_source_sound word fields candidate hp he hh

end BalancedAssortments.NPStack.SourceVerifier
