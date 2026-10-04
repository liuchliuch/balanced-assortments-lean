import BalancedAssortments.NPStackSourceVerifierProgramComplete
import BalancedAssortments.NPStackSourceVerifierGrammarPair
import BalancedAssortments.NPStackSourceVerifierSound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

lemma conditions_run (sh : Fin 8→List Bool) (ch : Fin 2→List Bool) (rs : List NPStackSourcePairing.PairRecord)
    (h : semanticConditions sh ch rs) :
    ∃ T out,Run Whole.concreteProgram T ⟨Whole.concreteProgram.start,Whole.inputStore sh ch rs⟩ out ∧
      accepts Whole.concreteProgram out := by
  have h' : RowsValid (rs.map decodeRow) (Whole.initialRegisters sh ch) ∧
      (eval VerifierCommands.headerCommand (Whole.scalarStart sh ch rs)).1=true ∧
      (eval VerifierCommands.rankCommand (Whole.afterHeader (Whole.scalarStart sh ch rs))).1=true ∧
      (eval VerifierCommands.revenueCommand (Whole.afterRank (Whole.scalarStart sh ch rs))).1=true ∧
      ∃ finish,Balance.loopValue (Whole.afterRevenue (Whole.scalarStart sh ch rs)) (Whole.balanceTriples rs)=some finish := by
    simpa only [semanticConditions,Whole.scalarStart,Whole.rowEnd,Whole.afterHeader,Whole.afterRank,
      Whole.afterRevenue,Whole.balanceTriples,header_effect,finalRegisters] using h
  obtain ⟨hv,h1,h2,h3,finish,hb⟩:=h'
  exact Whole.conditions_complete sh ch rs hv h1 h2 h3 hb

lemma accepted_shape (s : Source) (c : Certificate) (h : (verifyParsed s c).1=true) :
    c.numerators.length=s.products.length := by
  rw [←streamingVerifyParsed_eq] at h
  by_cases hs : shapeGuard s c=true
  · exact ((shapeGuard_correct s c).mp hs).1
  · simp [streamingVerifyParsed,hs] at h

/-- Completeness preserves the exact parsed source and certificate payloads;
no re-encoding, normalization, or canonical-sign hypothesis is needed. -/
theorem parsed_concrete_complete (sf cf : List (List Bool)) (s : Source) (c : Certificate)
    (hs : (packSource sf).1=some s) (hc : (packCertificate cf).1=some c)
    (hacc : (verifyParsed s c).1=true) :
    ∃ T out,Run Whole.concreteProgram T
      (Framing.bodyInput Whole.concreteProgram sf (NPStackFields.dataFields cf)) out ∧
      accepts Whole.concreteProgram out := by
  obtain ⟨sh,ch,rs,hsf,hcf,hps,hpc,hm⟩:=parsed_fields_pair sf cf s c hs hc (accepted_shape s c hacc)
  have hcond : semanticConditions sh ch rs := (semanticConditions_iff sh ch rs hm).mpr (by simpa [hps,hpc] using hacc)
  obtain ⟨T,out,hr,ha⟩:=conditions_run sh ch rs hcond
  refine ⟨T,out,?_,ha⟩
  simpa [Framing.bodyInput,Framing.typedStore,Whole.inputStore,hsf,hcf,NPStackSourcePairing.sourceStream,NPStackSourcePairing.certificateStream,NPStackFields.dataFields,List.flatMap_append] using hr

end BalancedAssortments.NPStack.SourceVerifier
