import BalancedAssortments.NPStackMachine

namespace BalancedAssortments.NPStack
variable {K Q : Type*} [DecidableEq K]

/-- Follow the first available primitive successor for exactly the given fuel.
This helper is for proving concrete finite instruction blocks by reduction;
it introduces no operational instruction or semantic callback. -/
def firstRun (P : Program K Q) : ℕ → Config K Q → Option (Config K Q)
  | 0,c => some c
  | n+1,c => match successors P c with
    | [] => none
    | d::_ => firstRun P n d

lemma firstRun_sound (P : Program K Q) (n : ℕ) (c d : Config K Q)
    (h : firstRun P n c=some d) : Run P n c d := by
  induction n generalizing c with
  | zero => simp only [firstRun,Option.some.injEq] at h;subst d;exact Run.zero _
  | succ n ih =>
    simp only [firstRun] at h
    cases hs : successors P c with
    | nil => simp [hs] at h
    | cons e es =>
      have he : Step P c e := by simp [Step,hs]
      exact Run.succ he (ih e (by simpa [hs] using h))

end BalancedAssortments.NPStack
