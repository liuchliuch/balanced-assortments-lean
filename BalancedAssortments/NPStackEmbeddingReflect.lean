import BalancedAssortments.NPStackEmbeddingSound

namespace BalancedAssortments.NPStack
variable {K Q K' Q' : Type*} [DecidableEq K] [DecidableEq K']

/-- Reflection of arbitrary runs when the embedded code preserves halt labels
as well as stepping instructions. Nondeterministic choices are retained. -/
theorem Run.reflect {P : Program K Q} {R : Program K' Q'}
    (fk : K→K') (fq : Q→Q') (hinj : Function.Injective fk)
    (hcode : ∀ q,R.code (fq q)=(P.code q).rename fk fq)
    {t : ℕ} {c : Config K Q} {c' d' : Config K' Q'}
    (h : Run R t c' d') (hc : Relocated fk fq c c') :
    ∃ d,Run P t c d ∧ Relocated fk fq d d' ∧ Frame fk c' d' := by
  induction h generalizing c with
  | zero c' => exact ⟨c,.zero c,hc,fun _ _ => rfl⟩
  | @succ t c' mid d' hs hr ih =>
    have hn : ∀ b,P.code c.pc≠.halt b := by
      intro b hb
      have he : R.code c'.pc=.halt b := by rw [hc.1,hcode,hb];rfl
      exact halted_no_step he hs
    obtain ⟨next,hnext,hrel,hframe⟩ := hs.reflect fk fq hinj (fun q _ => hcode q) hc hn
    obtain ⟨last,hlast,hlrel,hlframe⟩ := ih hrel
    exact ⟨last,.succ hnext hlast,hlrel,fun k hk => (hlframe k hk).trans (hframe k hk)⟩

lemma accepts_reflect {P : Program K Q} {R : Program K' Q'}
    (fk : K→K') (fq : Q→Q') (hcode : ∀ q,R.code (fq q)=(P.code q).rename fk fq)
    {c : Config K Q} {c' : Config K' Q'} (hc : Relocated fk fq c c')
    (ha : accepts R c') : accepts P c := by
  unfold accepts at *
  rw [hc.1,hcode] at ha
  cases hi : P.code c.pc <;> simp only [hi,Instr.rename] at ha
  · simpa using ha
  all_goals cases ha

end BalancedAssortments.NPStack
