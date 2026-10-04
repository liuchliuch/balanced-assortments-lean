import BalancedAssortments.FPTASCostAutoCandidate

namespace BalancedAssortments.KnapsackCostState
open KnapsackCostRational

lemma runRows_choices_length {cap : Fraction} {scores : List (List Bool)} {states : List State}
    {groups : List (List Item)} {depth : ℕ} (hs : ∀ s ∈ states,s.choices.length = depth) :
    ∀ s ∈ (runRows cap scores states groups).1,s.choices.length = depth+groups.length := by
  induction groups generalizing states depth with
  | nil => simpa using hs
  | cons g gs ih =>
    have hnext : ∀ s ∈ (advance cap scores states g).1,s.choices.length = depth+1 := by
      intro s hsm
      obtain ⟨prev,hprev,i,hi,rfl⟩ := advance_member hsm
      simp [extend,hs prev hprev]
    have hh := ih hnext
    simpa only [runRows,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

lemma solve_choices_length {cap : Fraction} {bound : ℕ} {groups : List (List Item)} {s : State}
    (hs : (solve cap bound groups).1 = some s) : s.choices.length = groups.length := by
  have hm : s ∈ (table cap bound groups).1 := (selectMax_member hs).resolve_right (by simp)
  have hh := runRows_choices_length (cap := cap) (scores := (KnapsackCostRange.scoreRange bound).1)
    (states := [initial]) (depth := 0)
    (by intro s hs; simp only [List.mem_singleton] at hs; subst s; rfl) s hm
  simpa only [Nat.zero_add] using hh

lemma scaledSolve_choices_length {θ cap : Fraction} {bound : ℕ} {groups : List (List Item)} {s : State}
    (hs : (scaledSolve θ cap bound groups).1 = some s) : s.choices.length = groups.length := by
  have hh := solve_choices_length hs
  simpa only [prepareGroups_eq,List.length_map] using hh

end BalancedAssortments.KnapsackCostState

namespace BalancedAssortments.FPTASCostCandidate
open KnapsackCostRational FPTASCostKernel FPTASCostCutoff FPTASCostOptions

lemma core_choices_length {δ count cap : Fraction} {bound : ℕ}
    {groups : List (List KnapsackCostState.Item)} {s : KnapsackCostState.State}
    (hs : (core δ count cap bound groups).1 = some s) : s.choices.length = groups.length := by
  simp only [core] at hs
  split_ifs at hs
  exact KnapsackCostState.scaledSolve_choices_length hs

/-- Exact reconstruction dimension, without positivity or feasibility assumptions:
one option is appended in every group transition, including zero options. -/
theorem autoCandidate_choices_length {δ count cap τ ratio α ρ : Fraction} {fuel : List Unit}
    {products : List (Fraction × Fraction)} {s : KnapsackCostState.State}
    (hs : (autoCandidate δ count cap τ ratio α ρ fuel products).1 = some s) :
    s.choices.length = products.length := by
  have hm := accept_member hs
  rw [coreTokens_eq] at hm
  have hh := core_choices_length hm
  simpa only [groupsAuto_eq,List.length_map] using hh

end BalancedAssortments.FPTASCostCandidate
