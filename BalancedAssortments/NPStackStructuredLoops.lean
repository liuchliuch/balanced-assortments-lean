import BalancedAssortments.NPStackStructuredUnary

namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]

/-- A loop rule for an explicit finite body block, with a real operational Exec
witness at every iteration. The invariant and bound occur only in the proof; the
compiled program inspects one physical counter bit per iteration. -/
theorem loop_false_bounded (counter : K) (body onTrue : Block K)
    (Inv : ℕ → Store K → Prop) (C : ℕ)
    (hbody : ∀ i s rest,Inv i s → s counter=false::rest →
      ∃ u t,t≤C ∧ Exec body (Function.update s counter rest) u t ∧ u counter=rest ∧ Inv (i+1) u)
    (m i : ℕ) (s : Store K) (hs : Inv i s) (hc : s counter=List.replicate m false) :
    ∃ u t,t ≤ m*(C+2)+1 ∧ Exec (.loop counter body onTrue) s u t ∧ u counter=[] ∧ Inv (i+m) u := by
  induction m generalizing i s with
  | zero =>
    refine ⟨s,1,by simp,Exec.loop_nil hc,?_,?_⟩
    · simpa using hc
    · simpa using hs
  | succ m ih =>
    have hh : s counter=false::List.replicate m false := by simpa only [List.replicate_succ] using hc
    obtain ⟨u,a,ha,he,huc,hu⟩ := hbody i s (List.replicate m false) hs hh
    obtain ⟨v,b,hb,hr,hvc,hv⟩ := ih (i+1) u hu huc
    refine ⟨v,a+b+2,?_,Exec.loop_false hh he hr,hvc,?_⟩
    · simp only [Nat.add_mul,Nat.one_mul];omega
    · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hv

noncomputable def forFuel (fuel scratch counter : K) (body : Block K) : Block K :=
  .seq (.atom (copyAtom fuel scratch counter)) (.loop counter body body)

/-- Reusable counted loop with preserved fuel and restored empty scratch/counter.
The finite body is supplied as syntax and expanded to primitive bytecode. -/
theorem forFuel_bounded (fuel scratch counter : K) (body : Block K)
    (hi : Function.Injective (Macros.copyMap fuel scratch counter))
    (Inv : ℕ → Store K → Prop) (C m : ℕ) (s : Store K)
    (hf : s fuel=List.replicate m false) (hscratch : s scratch=[]) (hcounter : s counter=[])
    (hstart : Inv 0 (Function.update s counter (List.replicate m false)))
    (hbody : ∀ i s rest,Inv i s → s counter=false::rest →
      ∃ u t,t≤C ∧ Exec body (Function.update s counter rest) u t ∧ u counter=rest ∧ Inv (i+1) u) :
    ∃ u t,t≤5*m+m*(C+2)+4 ∧ Exec (forFuel fuel scratch counter body) s u t ∧ u counter=[] ∧ Inv m u := by
  have hh := copyAtom_run fuel scratch counter hi s hscratch
  rw [hf,hcounter,List.append_nil,List.length_replicate] at hh
  let copied := Function.update s counter (List.replicate m false)
  have hcopied : copied counter=List.replicate m false := by simp [copied]
  obtain ⟨u,t,ht,hr,huc,hu⟩ := loop_false_bounded counter body body Inv C hbody m 0 copied hstart hcopied
  refine ⟨u,(5*m+2)+t+1,by omega,Exec.seq hh hr,huc,?_⟩
  simpa only [Nat.zero_add] using hu

end BalancedAssortments.NPStack.Structured
