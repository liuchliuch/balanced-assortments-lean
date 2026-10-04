import BalancedAssortments.NPStackSourceVerifierPolynomial

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

noncomputable def sourceBodyPolynomial : Polynomial ℕ :=
  wholePolynomial.comp (Polynomial.X+wireCertificatePolynomial+1)

lemma sourceBodyPolynomial_eval (n : ℕ) :
    sourceBodyPolynomial.eval n=wholeBudget (n+wireCertificatePolynomial.eval n+1)
      (n+wireCertificatePolynomial.eval n+1) := by
  simp [sourceBodyPolynomial,Polynomial.eval_comp,wholePolynomial_eval]

/-- A source yes-instance has an actual accepting finite-stack branch whose
entire primitive transition count is bounded in its original wire length. -/
theorem source_polynomial_branch (word : List Bool) (h : SourceLanguage word) :
    ∃ fields,(EncodingTime.parse word).1=some fields ∧
      ∃ candidate,candidate.length≤wireCertificatePolynomial.eval word.length ∧
      ∃ T≤sourceBodyPolynomial.eval word.length,∃ out,
        Run Whole.concreteProgram T (Framing.bodyInput Whole.concreteProgram fields candidate) out ∧
        accepts Whole.concreteProgram out := by
  obtain ⟨sf,cf,s,c,hparse,hps,hpc,hacc,hcert,hvolume⟩:=short_tagged_witness word h
  obtain ⟨sh,ch,rs,hsf,hcf,hsource,hcertificate,hm⟩:=parsed_fields_pair sf cf s c hps hpc (accepted_shape s c hacc)
  let B:=word.length+wireCertificatePolynomial.eval word.length+1
  have hB : 1≤B := by dsimp [B];omega
  obtain ⟨hsh,hch,hrecords,hn⟩:=paired_fields_bound sf cf sh ch rs hsf hcf hvolume
  have hconditions : semanticConditions sh ch rs := (semanticConditions_iff sh ch rs hm).mpr (by simpa [hsource,hcertificate] using hacc)
  obtain ⟨T,hT,out,hr,ha⟩:=conditions_bounded sh ch rs B hB hsh hch hrecords hconditions
  refine ⟨sf,hparse,NPStackFields.dataFields cf,hcert,T,?_,out,?_,ha⟩
  · rw [sourceBodyPolynomial_eval]
    exact hT.trans (wholeBudget_mono_n hn)
  · simpa [Framing.bodyInput,Framing.typedStore,Whole.inputStore,hsf,hcf,
      NPStackSourcePairing.sourceStream,NPStackSourcePairing.certificateStream,NPStackFields.dataFields,List.flatMap_append] using hr

/-- Membership in NP for the exact original raw source language, using the
literal finite Boolean-stack verifier and the proved one-tape compiler. -/
theorem sourceLanguage_inNP : NPMachine.InNP {word | SourceLanguage word} := by
  apply Framing.recognition_inNP Whole.concreteProgram wireCertificatePolynomial sourceBodyPolynomial
  · intro word fields candidate t out hp hr ha
    exact concrete_source_sound word fields candidate hp hr ha
  · intro word h
    exact source_polynomial_branch word h

end BalancedAssortments.NPStack.SourceVerifier
