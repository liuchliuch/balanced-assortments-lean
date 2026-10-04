import BalancedAssortments.NPStackCompositionCorrect

namespace BalancedAssortments.NPStack

lemma polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a≤b) : p.eval a≤p.eval b := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h i)

noncomputable def compositionClock (p q : Polynomial ℕ) : Polynomial ℕ :=
  p+q.comp (Polynomial.X+p)+4*(Polynomial.X+p)+5

lemma compositionClock_eval (p q : Polynomial ℕ) (n : ℕ) :
    (compositionClock p q).eval n=p.eval n+q.eval (n+p.eval n)+4*(n+p.eval n)+5 := by
  simp [compositionClock,Polynomial.eval_comp]

/-- A certified finite transducer for the composition. Its explicit clock
includes the actual transfer and the second program's larger input. -/
noncomputable def PolynomialProgram.comp {f g : List Bool→List Bool} (p : PolynomialProgram f) (q : PolynomialProgram g) :
    PolynomialProgram (g∘f) where
  code := {
    K := Composition.Stack p.code.K q.code.K
    Q := Composition.Label p.code.Q q.code.Q
    program := Composition.program p.code.program q.code.program }
  noChoice := Composition.noChoice p.noChoice q.noChoice
  clock := compositionClock p.clock q.clock
  computes := by
    intro bits
    have h := Composition.outputs_compose p.code.program q.code.program bits (f bits) (g (f bits))
      (p.computes bits) (q.computes (f bits))
    obtain ⟨t,ht,c,hr,ha,hout⟩ := h
    have hl := p.output_length bits
    have hq := polynomial_eval_mono q.clock hl
    refine ⟨t,?_,c,hr,ha,hout⟩
    rw [compositionClock_eval]
    omega

theorem PolyComputable.comp {f g : List Bool→List Bool} (hf : PolyComputable f) (hg : PolyComputable g) :
    PolyComputable (g∘f) := by
  obtain ⟨p⟩ := hf
  obtain ⟨q⟩ := hg
  exact ⟨p.comp q⟩

/-- Closure is proved by finite instruction composition, not by assuming
that mathematically composed functions inherit an annotated time bound. -/
theorem PolyManyOne.trans {A B C : Set (List Bool)} (hAB : PolyManyOne A B) (hBC : PolyManyOne B C) :
    PolyManyOne A C := by
  obtain ⟨f,hf,he⟩ := hAB
  obtain ⟨g,hg,hgE⟩ := hBC
  exact ⟨g∘f,hf.comp hg,fun bits => (he bits).trans (hgE (f bits))⟩

end BalancedAssortments.NPStack
