import BalancedAssortments.NPStackSourceFixedState
import BalancedAssortments.NPStackSourceMembership

namespace BalancedAssortments.NPStack.SourceVerifier.Fixed
open NPStack DirectVerifier ComplexityTimeVerifier ComplexityTimeSourceParsing VerifierControl

/-- Every accepted branch of the literal restricted verifier satisfies both the
original raw decision language and the numeric K=2, alpha=1 restriction. -/
theorem concrete_fixed_sound (word : List Bool) (fields : List (List Bool)) (candidate : List Bool)
    {T : ℕ} {out : Config SourceVerifier.Stack State}
    (hp : (EncodingTime.parse word).1=some fields)
    (hr : Run program T (Framing.bodyInput program fields candidate) out)
    (ha : accepts program out) : FixedSourceLanguage word := by
  obtain ⟨t,u,middle,hfirst,hrest,_⟩ := accepting_segments hr ha
  obtain ⟨e,he,heacc,hprojection,_⟩ := hfirst
  have hm : middle=e.stk := funext hprojection
  obtain ⟨s,hs,hiff⟩ := whole_final_guard word fields candidate hp he heacc
  rw [hm,hs] at hrest
  exact ⟨concrete_source_sound word fields candidate hp he heacc,hiff.mp (guard_suffix_sound s hrest ha)⟩

/-- A literal stack transition can increase a stored bitstring by at most one.
Thus the appended guard needs only a quadratic polynomial in the already
bounded whole-verifier run, independently of represented numeric values. -/
lemma output_register_width (fields : List (List Bool)) (candidate : List Bool)
    {T : ℕ} {out : Config SourceVerifier.Stack (Whole.State Balance.LoopState)} (s : Registers)
    (hr : Run Whole.concreteProgram T (Framing.bodyInput Whole.concreteProgram fields candidate) out)
    (hs : out.stk=Whole.globalStore s []) : ∀ k, width (s k)+1≤T+1 := by
  intro k
  have hp := hr.stack_length (Whole.globalArithmeticMap (.reg k false))
  have hn := hr.stack_length (Whole.globalArithmeticMap (.reg k true))
  rw [hs,Whole.global_projection] at hp hn
  change (s k).1.length≤0+T at hp
  change (s k).2.length≤0+T at hn
  unfold width
  omega

noncomputable def fixedBodyPolynomial : Polynomial ℕ :=
  sourceBodyPolynomial + Polynomial.C (costCoefficient command)*(sourceBodyPolynomial+1)^2+1

lemma fixedBodyPolynomial_eval (n : ℕ) :
    fixedBodyPolynomial.eval n=sourceBodyPolynomial.eval n+
      costCoefficient command*(sourceBodyPolynomial.eval n+1)^2+1 := by
  simp [fixedBodyPolynomial]

/-- An actual bounded accepting branch, on the exact original wire input,
including arbitrary legal redundant representations of the fixed parameters. -/
theorem fixed_polynomial_branch (word : List Bool) (h : FixedSourceLanguage word) :
    ∃ fields,(EncodingTime.parse word).1=some fields ∧
      ∃ candidate,candidate.length≤wireCertificatePolynomial.eval word.length ∧
      ∃ T≤fixedBodyPolynomial.eval word.length,∃ out,
        Run program T (Framing.bodyInput program fields candidate) out ∧ accepts program out := by
  obtain ⟨fields,hp,candidate,hc,T,hT,out,hr,ha⟩ := source_polynomial_branch word h.1
  obtain ⟨s,hs,hiff⟩ := whole_final_guard word fields candidate hp hr ha
  obtain ⟨t,ht,last,hlast,hlastacc⟩ := append_complete s hr ha hs (hiff.mpr h.2)
  have hguard := budget_quadratic command s (output_register_width fields candidate s hr hs)
  refine ⟨fields,hp,candidate,hc,t,?_,last,hlast,hlastacc⟩
  rw [fixedBodyPolynomial_eval]
  have hsq : (T+1)^2≤(sourceBodyPolynomial.eval word.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have hmul := Nat.mul_le_mul_left (costCoefficient command) hsq
  omega

/-- NP membership uses the actual finite nondeterministic guess/framing/verifier
program and its concrete one-tape simulation, rather than subset closure. -/
theorem fixedSourceLanguage_inNP : NPMachine.InNP {word | FixedSourceLanguage word} := by
  apply Framing.recognition_inNP program wireCertificatePolynomial fixedBodyPolynomial
  · intro word fields candidate t out hp hr ha
    exact concrete_fixed_sound word fields candidate hp hr ha
  · intro word h
    exact fixed_polynomial_branch word h

end BalancedAssortments.NPStack.SourceVerifier.Fixed
