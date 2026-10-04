import BalancedAssortments.NPStackSourceFraming

namespace BalancedAssortments.NPStack.SourceVerifier.Framing
open NPStack

lemma parser_reject_code {Q : Type*} (P : Program SourceVerifier.Stack Q) (q : NPStackFields.State)
    (h : NPStackFields.program.code q=.halt false) : (program P).code (.parser q)=.halt false := by
  by_cases he : q=.accept
  · subst q;cases h
  · have hc : (program P).code (.parser q)=(NPStackFields.program.code q).rename parserMap State.parser := by
      cases q <;> simp_all [program]
    rw [hc,h]
    rfl

/-- Malformed raw sources cannot reach an accepting body through a parser
failure, even when the supplied body is nondeterministic. -/
lemma malformed_excludes_acceptance {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool)
    (hp : (EncodingTime.parse word).1=none) {T : ℕ} {d : Config Stack (State Q)}
    (hr : Run (program P) T (rawInput P word candidate) d) (ha : accepts (program P) d) : False := by
  obtain ⟨t,_,e,he,hh⟩ := NPStackFields.parse_reject word [] hp
  have hrel : Relocated parserMap State.parser (NPStackFields.cfg .probe word [] [] [] []) (rawInput P word candidate) :=
    ⟨rfl,by intro k;fin_cases k <;> rfl⟩
  obtain ⟨e',hpref,hout,_⟩ := he.relocate_deterministic NPStackFields.program_noChoice parserMap State.parser
    parserMap_injective (parser_extends P) hrel
  have hh' : (program P).code e'.pc=.halt false := by
    rw [hout.1]
    exact parser_reject_code P e.pc hh
  obtain ⟨u,_,hu⟩ := hpref.factor_halted hr ha
  have heq := hu.from_halted hh'
  rw [heq.2,ha] at hh'
  cases hh'

/-- Every accepted framed execution has a successfully parsed raw source and
an actual accepting run of the literal two-stream body on the unchanged guessed
tagged certificate. There is no raw-certificate parser or semantic callback. -/
theorem framed_sound {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool)
    {T : ℕ} {d : Config Stack (State Q)}
    (hr : Run (program P) T (Guess.twoInput (program P) certificate word candidate) d)
    (ha : accepts (program P) d) :
    ∃ fields t e,(EncodingTime.parse word).1=some fields ∧ Run P t (bodyInput P fields candidate) e ∧ accepts P e := by
  rw [twoInput_raw] at hr
  cases hp : (EncodingTime.parse word).1 with
  | none => exact False.elim (malformed_excludes_acceptance P word candidate hp hr ha)
  | some fields =>
    obtain ⟨t,_,ht⟩ := (parser_prefix P word candidate fields hp).factor_halted hr ha
    obtain ⟨e,he,hrel,_⟩ := ht.reflect Sum.inl State.body Sum.inl_injective (body_code P)
      (c:=bodyInput P fields candidate) ⟨rfl,fun _ => rfl⟩
    exact ⟨fields,t,e,rfl,he,accepts_reflect Sum.inl State.body (body_code P) hrel ha⟩

def guessedProgram {Q : Type*} (P : Program SourceVerifier.Stack Q) := Guess.program (program P) certificate

theorem guessed_complete {Q : Type*} (P : Program SourceVerifier.Stack Q) (word candidate : List Bool)
    (fields : List (List Bool)) (hp : (EncodingTime.parse word).1=some fields)
    {T : ℕ} {e : Config SourceVerifier.Stack Q}
    (hr : Run P T (bodyInput P fields candidate) e) (ha : accepts P e) :
    ∃ t ≤ 10*word.length+3*candidate.length+T+4,∃ d,
      Run (guessedProgram P) t (initial (guessedProgram P) word) d ∧ accepts (guessedProgram P) d := by
  obtain ⟨u,hu,d,hd,hh⟩ := framed_complete P word candidate fields hp hr ha
  obtain ⟨hguess,haccept⟩ := Guess.candidate_complete (program P) certificate (certificate_ne_input P) word candidate hd hh
  exact ⟨3*candidate.length+1+u,by omega,_,hguess,haccept⟩

theorem guessed_sound {Q : Type*} (P : Program SourceVerifier.Stack Q) (word : List Bool)
    {T : ℕ} {d : Config Stack (Guess.State (State Q))}
    (hr : Run (guessedProgram P) T (initial (guessedProgram P) word) d) (ha : accepts (guessedProgram P) d) :
    ∃ fields candidate t e,(EncodingTime.parse word).1=some fields ∧
      Run P t (bodyInput P fields candidate) e ∧ accepts P e := by
  obtain ⟨candidate,u,c,hc,hh⟩ := Guess.accepting_candidate (program P) certificate (certificate_ne_input P) word hr ha
  obtain ⟨fields,t,e,hp,he,haccept⟩ := framed_sound P word candidate hc hh
  exact ⟨fields,candidate,t,e,hp,he,haccept⟩

/-- Full literal source-membership wrapper: raw source parsing, nondeterministic
tagged-certificate guessing, finite verifier execution, and finite one-tape
compilation. The hypotheses refer exclusively to actual finite body runs. -/
theorem recognition_inNP {Q : Type*} [Fintype Q] (P : Program SourceVerifier.Stack Q)
    (candidateClock bodyClock : Polynomial ℕ) (L : Set (List Bool))
    (sound : ∀ word fields candidate t e,(EncodingTime.parse word).1=some fields →
      Run P t (bodyInput P fields candidate) e → accepts P e → word∈L)
    (complete : ∀ word,word∈L → ∃ fields,(EncodingTime.parse word).1=some fields ∧
      ∃ candidate,candidate.length ≤ candidateClock.eval word.length ∧ ∃ t ≤ bodyClock.eval word.length,
      ∃ e,Run P t (bodyInput P fields candidate) e ∧ accepts P e) : NPMachine.InNP L := by
  apply Guess.recognition_inNP (program P) certificate (certificate_ne_input P)
    candidateClock (10*Polynomial.X+3+bodyClock) L
  · intro word candidate t e hr ha
    obtain ⟨fields,u,d,hp,hd,hh⟩ := framed_sound P word candidate hr ha
    exact sound word fields candidate u d hp hd hh
  · intro word hw
    obtain ⟨fields,hp,candidate,hcandidate,t,ht,e,hr,ha⟩ := complete word hw
    obtain ⟨u,hu,d,hd,hh⟩ := framed_complete P word candidate fields hp hr ha
    refine ⟨candidate,hcandidate,u,?_,d,hd,hh⟩
    simp
    omega

end BalancedAssortments.NPStack.SourceVerifier.Framing
