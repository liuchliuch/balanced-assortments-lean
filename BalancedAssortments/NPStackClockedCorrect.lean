import BalancedAssortments.NPStackClockedSeed

namespace BalancedAssortments.NPStack.Clocked
open NPStack NPStack.Macros

noncomputable def wrapperClock (clockTime sourceTime : Polynomial ℕ) (fallback : List Bool) : Polynomial ℕ :=
  clockTime+6*Polynomial.X+9*sourceTime+Polynomial.C (fallback.length+20)

lemma wrapperClock_eval (a b : Polynomial ℕ) (fallback : List Bool) (n : ℕ) :
    (wrapperClock a b fallback).eval n=a.eval n+6*n+9*b.eval n+fallback.length+20 := by
  simp [wrapperClock,Nat.add_assoc]

/-- Clock generation, physical-fuel copy, timeout execution and fallback cleanup
are all actual finite primitive runs. Only valid inputs need a source-time
bound; all other inputs are required to have the designated fallback meaning. -/
theorem computes (P : FiniteProgram) (f : List Bool → List Bool) (Good : List Bool → Prop)
    (sourceTime : Polynomial ℕ) (fallback : List Bool)
    (clock : PolynomialProgram (fun word=>List.replicate (sourceTime.eval word.length) false))
    (hP : NoChoice P.program)
    (sound : ∀ word t c,Run P.program t (initial P.program word) c → accepts P.program c → c.stk P.program.outputStack=f word)
    (complete : ∀ word,Good word → OutputsIn P.program word (f word) (sourceTime.eval word.length))
    (other : ∀ word,¬Good word → f word=fallback) (word : List Bool) :
    OutputsIn (program P clock.code fallback) word (f word)
      ((wrapperClock clock.clock sourceTime fallback).eval word.length) := by
  let fuel := List.replicate (sourceTime.eval word.length) false
  have hlen : fuel.length=sourceTime.eval word.length := List.length_replicate
  obtain ⟨ct,hct,cc,hcr,hca,hco⟩ := clock.computes word
  have hseed := seed_run P clock.code fallback word fuel hcr hca hco
  obtain ⟨t,ht,e,b,hr,hb,hsound⟩ := Timeout.bounded_halt P.program (initial P.program word) fuel
  have htimed := timed_run P clock.code fallback hr cc.stk []
  have hpre := hseed.trans htimed
  let s := store cc.stk e.stk []
  have hinit : ((initial P.program word).stk P.program.outputStack).length≤word.length := by
    by_cases he : P.program.outputStack=P.program.inputStack
    · simp [initial,he]
    · simp [initial,Function.update_apply,he]
  cases b with
  | true =>
    obtain ⟨u,hu,d,hd,haccept,he⟩ := hsound rfl
    have hstep : Step (program P clock.code fallback) ⟨.timed e.pc,s⟩ ⟨.accept,s⟩ := by
      simp [Step,successors,program,code,returnCode,hb]
    refine ⟨ct+5*word.length+5*fuel.length+7+t+1,?_,⟨.accept,s⟩,?_,rfl,?_⟩
    · rw [wrapperClock_eval]
      omega
    · exact hpre.trans (Run.one hstep)
    · change e.stk (.inl P.program.outputStack)=f word
      rw [he]
      exact sound word u d hd haccept
  | false =>
    have hbad : ¬Good word := by
      intro hg
      obtain ⟨u,hu,d,hd,haccept,hout⟩ := complete word hg
      have hu' : u≤fuel.length := by omega
      obtain ⟨hknown,ha⟩ := Timeout.accepts_complete hd haccept fuel hu'
      exact rejecting_run_excludes_acceptance
        (noChoice_deterministic (Timeout.program_noChoice hP)) hr hb hknown ha
    have hstep : Step (program P clock.code fallback) ⟨.timed e.pc,s⟩ ⟨.clear,s⟩ := by
      simp [Step,successors,program,code,returnCode,hb]
    have hf := fallback_run P clock.code fallback s
    have hsize : (s (output P clock.code)).length≤word.length+t := by
      have hh := hr.stack_length (.inl P.program.outputStack)
      change (e.stk (.inl P.program.outputStack)).length≤((initial P.program word).stk P.program.outputStack).length+t at hh
      exact hh.trans (Nat.add_le_add_right hinit t)
    refine ⟨ct+5*word.length+5*fuel.length+7+t+1+((s (output P clock.code)).length+fallback.length+2),?_,
      ⟨.accept,Function.update s (output P clock.code) fallback⟩,?_,rfl,?_⟩
    · rw [wrapperClock_eval]
      omega
    · convert hpre.trans (Run.succ hstep hf) using 1 <;> omega
    · change (Function.update s (output P clock.code) fallback) (output P clock.code)=f word
      rw [Function.update_self,other word hbad]

noncomputable def polynomialProgram (P : FiniteProgram) (f : List Bool → List Bool) (Good : List Bool → Prop)
    (sourceTime : Polynomial ℕ) (fallback : List Bool)
    (clock : PolynomialProgram (fun word=>List.replicate (sourceTime.eval word.length) false))
    (hP : NoChoice P.program)
    (sound : ∀ word t c,Run P.program t (initial P.program word) c → accepts P.program c → c.stk P.program.outputStack=f word)
    (complete : ∀ word,Good word → OutputsIn P.program word (f word) (sourceTime.eval word.length))
    (other : ∀ word,¬Good word → f word=fallback) : PolynomialProgram f where
  code := finiteProgram P clock.code fallback
  noChoice := program_noChoice P clock.code fallback hP clock.noChoice
  clock := wrapperClock clock.clock sourceTime fallback
  computes := computes P f Good sourceTime fallback clock hP sound complete other

/-- The timeout closure uses the already compiled finite unary-clock generator.
Thus it closes a genuine operational polynomial-program obligation, rather
than postulating a semantic clock around an arbitrary function. -/
theorem polyComputable (P : FiniteProgram) (f : List Bool → List Bool) (Good : List Bool → Prop)
    (sourceTime : Polynomial ℕ) (fallback : List Bool) (hP : NoChoice P.program)
    (sound : ∀ word t c,Run P.program t (initial P.program word) c → accepts P.program c → c.stk P.program.outputStack=f word)
    (complete : ∀ word,Good word → OutputsIn P.program word (f word) (sourceTime.eval word.length))
    (other : ∀ word,¬Good word → f word=fallback) : PolyComputable f := by
  obtain ⟨clock⟩ := CookLevin.StackClock.every_polynomial_clock sourceTime
  exact ⟨polynomialProgram P f Good sourceTime fallback clock hP sound complete other⟩

end BalancedAssortments.NPStack.Clocked
