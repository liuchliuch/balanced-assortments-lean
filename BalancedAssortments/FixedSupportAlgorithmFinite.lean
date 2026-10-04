import BalancedAssortments.FixedSupportAlgorithm

namespace BalancedAssortments.FixedSupportAlgorithm

theorem inverseSum_pos {n : ℕ} (hn : 0 < n) (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) :
    0 < inverseSum v := by
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact Finset.sum_pos (fun i _ => one_div_pos.mpr (hv i)) Finset.univ_nonempty

theorem scaleUpper_le_coordinate {n : ℕ} (v : Fin n → ℚ) (K : ℚ) (i : Fin n) :
    scaleUpper v K ≤ v i :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

theorem scaleUpper_le_budgetQuotient {n : ℕ} (v : Fin n → ℚ) (K : ℚ) :
    scaleUpper v K ≤ K / inverseSum v := Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem scaleUpper_pos {n : ℕ} (hn : 0 < n) (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    {K : ℚ} (hK : 0 < K) : 0 < scaleUpper v K := by
  have hm := (insert (K / inverseSum v) (Finset.univ.image v)).min'_mem (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with he | hm
  · change 0 < scaleUpper v K
    rw [show scaleUpper v K = K / inverseSum v from he]
    exact div_pos hK (inverseSum_pos hn v hv)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    change 0 < scaleUpper v K
    change v i = scaleUpper v K at hi
    rw [← hi]
    exact hv i

theorem scoreSamples_bounds {n : ℕ} (r v : Fin n → ℚ) {ρ : ℚ} (hρ : ρ ∈ scoreSamples r v) :
    0 ≤ ρ ∧ ρ ≤ revenueUpper r :=
  regimeSamples_bounds (affineCritical_bounds (revenueUpper_nonneg r) (scoreLines r v)) hρ

theorem capCuts_bounds {n : ℕ} (v : Fin n → ℚ) (α : ℚ) {T t : ℚ}
    (hT : 0 ≤ T) (ht : t ∈ capCuts v α T) : 0 ≤ t ∧ t ≤ T := by
  simp only [capCuts, Finset.mem_insert, Finset.mem_filter] at ht
  rcases ht with rfl | rfl | ⟨_, ht⟩
  · exact ⟨le_rfl, hT⟩
  · exact ⟨hT, le_rfl⟩
  · exact ht

theorem scaleSamples_bounds {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ)
    (hT : 0 ≤ scaleUpper v K) {t : ℚ} (ht : t ∈ scaleSamples r v α K ρ) :
    0 ≤ t ∧ t ≤ scaleUpper v K := by
  rcases Finset.mem_union.mp ht with ht | ht
  · exact capCuts_bounds v α hT ht
  · exact (Finset.mem_filter.mp ht).2

@[simp] theorem zero_mem_scoreSamples {n : ℕ} (r v : Fin n → ℚ) :
    0 ∈ scoreSamples r v := by
  apply Finset.mem_union_left
  simp [affineCritical]

@[simp] theorem zero_mem_scaleSamples {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ) :
    0 ∈ scaleSamples r v α K ρ := by
  apply Finset.mem_union_left
  simp [capCuts]

@[simp] theorem upper_mem_scaleSamples {n : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ) :
    scaleUpper v K ∈ scaleSamples r v α K ρ := by
  apply Finset.mem_union_left
  simp [capCuts]

theorem mem_candidates {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) (p : ℚ × ℚ) :
    p ∈ candidates r v α K ↔ p.1 ∈ scoreSamples r v ∧ p.2 ∈ scaleSamples r v α K p.1 := by
  rcases p with ⟨ρ, t⟩
  simp [candidates]

@[simp] theorem zero_mem_candidates {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) :
    (0, 0) ∈ candidates r v α K := by rw [mem_candidates]; simp

theorem candidates_length {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) :
    (candidates r v α K).length ≤ ((n + n^2 + 2) + (n + n^2 + 2)^2) * (n + 2)^2 := by
  unfold candidates
  rw [List.length_flatMap]
  have hs : (((scoreSamples r v).sort (· ≤ ·)).map
      (fun ρ => (((scaleSamples r v α K ρ).sort (· ≤ ·)).map (fun t => (ρ, t))).length)).sum ≤
      ((scoreSamples r v).sort (· ≤ ·)).length * (n + 2)^2 := by
    have hh := List.sum_le_card_nsmul
      (((scoreSamples r v).sort (· ≤ ·)).map
        (fun ρ => (((scaleSamples r v α K ρ).sort (· ≤ ·)).map (fun t => (ρ, t))).length))
      ((n + 2)^2) (by
        intro x hx
        obtain ⟨ρ, _, rfl⟩ := List.mem_map.mp hx
        simpa using scaleSamples_card r v α K ρ)
    simpa using hh
  exact hs.trans (Nat.mul_le_mul_right _ (by simpa using scoreSamples_card r v))

def pickBest {A : Type*} (f : A → ℚ) (a b : A) : A := if f a ≤ f b then b else a

private theorem fold_best_dominates {A : Type*} (f : A → ℚ) (xs : List A) (a : A) :
    f a ≤ f (xs.foldl (pickBest f) a) ∧ ∀ x ∈ xs, f x ≤ f (xs.foldl (pickBest f) a) := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    have hh := ih (pickBest f a b)
    have ha : f a ≤ f (pickBest f a b) := by unfold pickBest; split_ifs <;> simp_all
    have hb : f b ≤ f (pickBest f a b) := by
      unfold pickBest
      split_ifs with hh
      · exact le_rfl
      · exact (lt_of_not_ge hh).le
    refine ⟨ha.trans hh.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hb.trans hh.1
    · exact hh.2 x hx

private theorem fold_best_mem {A : Type*} (f : A → ℚ) (xs : List A) (a : A) :
    xs.foldl (pickBest f) a = a ∨ xs.foldl (pickBest f) a ∈ xs := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    rcases ih (pickBest f a b) with hh | hh
    · rw [List.foldl_cons, hh]
      unfold pickBest
      split_ifs
      · exact Or.inr (by simp)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ hh)

theorem bestCandidate_mem {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ) :
    bestCandidate r v α K ∈ candidates r v α K := by
  rcases fold_best_mem (fun p => fractionalRevenue r (candidateVector r v α K p))
    (candidates r v α K) (0, 0) with hh | hh
  · change bestCandidate r v α K = (0, 0) at hh
    rw [hh]
    exact zero_mem_candidates r v α K
  · exact hh

theorem optimize_dominates_candidates {n : ℕ} (r v : Fin n → ℚ) (α K : ℚ)
    {p : ℚ × ℚ} (hp : p ∈ candidates r v α K) :
    fractionalRevenue r (candidateVector r v α K p) ≤ fractionalRevenue r (optimize r v α K) :=
  (fold_best_dominates (fun p => fractionalRevenue r (candidateVector r v α K p))
    (candidates r v α K) (0, 0)).2 p hp

end BalancedAssortments.FixedSupportAlgorithm
