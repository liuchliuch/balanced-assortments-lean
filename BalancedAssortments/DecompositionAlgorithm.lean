import BalancedAssortments.DecompositionGreedy

namespace BalancedAssortments.Decomposition

/-- Select all integral ones, then fill the remaining capacity from positive
coordinates in index order. Sorting the indices makes this executable. -/
def greedySet {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : Finset (Fin n) :=
  ones z ∪ (((positive z \ ones z).sort (· ≤ ·)).take (K - (ones z).card)).toFinset

theorem greedySet_valid {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) : PeelSet K z (greedySet K z) := by
  let O := ones z
  let P := positive z
  let l := (P \ O).sort (· ≤ ·)
  let T := (l.take (K - O.card)).toFinset
  have hOP : O ⊆ P := by
    intro i hi
    have hz : z i = 1 := (Finset.mem_filter.mp hi).2
    simp [P, positive, hz]
  have hO : O.card ≤ K := by
    obtain ⟨S, hs⟩ := exists_peelSet h
    exact (Finset.card_le_card hs.1).trans hs.2.2.1
  have hT : T ⊆ P \ O := by
    intro i hi
    exact (Finset.mem_sort _).mp (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  have hd : Disjoint O T := by
    apply Finset.disjoint_left.mpr
    intro i hi hit
    exact (Finset.mem_sdiff.mp (hT hit)).2 hi
  have hlen : l.length = P.card - O.card := by
    simp [l, Finset.card_sdiff, Finset.inter_eq_left.mpr hOP]
  have hcard : (O ∪ T).card = O.card + min (K - O.card) (P.card - O.card) := by
    rw [Finset.card_union_of_disjoint hd]
    congr 1
    rw [show T.card = (l.take (K - O.card)).length from
      List.toFinset_card_of_nodup ((Finset.sort_nodup _ _).take)]
    simp [hlen]
  change PeelSet K z (O ∪ T)
  refine ⟨Finset.subset_union_left, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hOP hi
    · exact (Finset.mem_sdiff.mp (hT hi)).1
  · rw [hcard]
    omega
  · by_cases hp : P.card ≤ K
    · right
      have he : T = P \ O := by
        dsimp [T]
        rw [List.take_of_length_le (by omega), Finset.sort_toFinset]
      rw [he]
      intro i hi
      by_cases hoi : i ∈ O
      · exact Finset.mem_union_left _ hoi
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hoi⟩)
    · left
      rw [hcard]
      have := Finset.card_le_card hOP
      omega

/-- Smallest boundary distance among fractional coordinates; one at integral
points. All operations, including minimization, are finite rational operations. -/
def greedyStep {n : ℕ} (z : Fin n → ℚ) (S : Finset (Fin n)) : ℚ :=
  if hf : (fractional z).Nonempty then
    ((fractional z).image (stepBound z S)).min' (hf.image _)
  else 1

theorem greedyStep_spec {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    (hf : (fractional z).Nonempty) :
    0 < greedyStep z S ∧ greedyStep z S < 1 ∧
    (∀ i, greedyStep z S ≤ stepBound z S i) ∧
    ∃ i ∈ fractional z, greedyStep z S = stepBound z S i := by
  obtain ⟨t, ht0, ht1, htmin, i, hi, he⟩ := exists_peel_step h hS hf
  have hg : greedyStep z S = t := by
    simp only [greedyStep, dif_pos hf]
    apply le_antisymm
    · rw [he]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp
        (((fractional z).image (stepBound z S)).min'_mem (hf.image _))
      rw [← hje]
      exact htmin j
  rw [hg]
  exact ⟨ht0, ht1, htmin, i, hi, he⟩

/-- Fuel-bounded executable greedy peeling. Feasible inputs need at most `n`
peels; the zero-fuel branch is only reached at an integral point. -/
def greedyAux {n : ℕ} : ℕ → ℕ → (Fin n → ℚ) → List (Atom n)
  | 0, _, z => [(1, ones z)]
  | fuel + 1, K, z =>
    if fractional z = ∅ then [(1, ones z)] else
      let S := greedySet K z
      let t := greedyStep z S
      prependPeel S t (greedyAux fuel K (residual z S t))

def greedy {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : List (Atom n) := greedyAux n K z

theorem greedyAux_correct {n : ℕ} (fuel : ℕ) {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) (hf : (fractional z).card ≤ fuel) :
    ValidDecomposition K z (greedyAux fuel K z) ∧
      (greedyAux fuel K z).length ≤ (fractional z).card + 1 := by
  induction fuel generalizing z with
  | zero =>
    have he : fractional z = ∅ := Finset.card_eq_zero.mp (by omega)
    exact ⟨integral_decomposition h he, by simp [greedyAux]⟩
  | succ fuel ih =>
    by_cases he : fractional z = ∅
    · simp only [greedyAux, if_pos he]
      exact ⟨integral_decomposition h he, by simp⟩
    · simp only [greedyAux, if_neg he]
      let S := greedySet K z
      let t := greedyStep z S
      have hS : PeelSet K z S := greedySet_valid h
      obtain ⟨ht0, ht1, hb, i, hi, ht⟩ := greedyStep_spec h hS (Finset.nonempty_iff_ne_empty.mpr he)
      have hres : Feasible K (residual z S t) := residual_feasible h hS ht1 hb
      have hprog := residual_progress h hS ht1 hi ht
      change (fractional (residual z S t)).card < (fractional z).card at hprog
      have hr := ih hres (by omega)
      exact ⟨prependPeel_valid hS.2.2.1 ht0.le ht1 hr.1, by
        rw [prependPeel_length]
        have := hr.2
        change (greedyAux fuel K (residual z S t)).length + 1 ≤ _
        omega⟩

/-- The certified executable rational algorithm implements every feasible
marginal vector with at most `n+1` atoms. -/
theorem greedy_correct {n : ℕ} {K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    ValidDecomposition K z (greedy K z) ∧ (greedy K z).length ≤ n + 1 := by
  have hf : (fractional z).card ≤ n := by simpa using Finset.card_le_univ (fractional z)
  have hh := greedyAux_correct n h hf
  exact ⟨hh.1, hh.2.trans (Nat.add_le_add_right hf 1)⟩

theorem greedyAux_positive {n : ℕ} (fuel : ℕ) {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) (hf : (fractional z).card ≤ fuel) :
    ∀ a ∈ greedyAux fuel K z, 0 < a.1 := by
  induction fuel generalizing z with
  | zero => simp [greedyAux]
  | succ fuel ih =>
    by_cases he : fractional z = ∅
    · simp [greedyAux, he]
    · let S := greedySet K z
      let t := greedyStep z S
      have hS : PeelSet K z S := greedySet_valid h
      obtain ⟨ht0, ht1, hb, i, hi, ht⟩ := greedyStep_spec h hS (Finset.nonempty_iff_ne_empty.mpr he)
      have hres : Feasible K (residual z S t) := residual_feasible h hS ht1 hb
      have hprog := residual_progress h hS ht1 hi ht
      change (fractional (residual z S t)).card < (fractional z).card at hprog
      have hr := ih hres (by omega)
      intro a ha
      simp only [greedyAux, if_neg he] at ha
      change a ∈ prependPeel S t (greedyAux fuel K (residual z S t)) at ha
      simp only [prependPeel, List.mem_cons, List.mem_map] at ha
      rcases ha with hae | ⟨b, hb, rfl⟩
      · simpa [hae] using ht0
      · exact mul_pos (sub_pos.mpr ht1) (hr b hb)

theorem greedy_positive {n : ℕ} {K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    ∀ a ∈ greedy K z, 0 < a.1 :=
  greedyAux_positive n h (by simpa using Finset.card_le_univ (fractional z))

theorem greedy_legal {n : ℕ} {K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    ∀ a ∈ greedy K z, a.2.card ≤ K := by
  intro a ha
  exact (greedy_correct h).1.2.2.1 a ha (ne_of_gt (greedy_positive h a ha))

/-- Boundary cases require no positive dimension or rank assumptions. -/
@[simp] theorem greedy_empty (K : ℕ) (z : Fin 0 → ℚ) :
    greedy K z = [(1, ∅)] := by
  simp [greedy, greedyAux, ones]

@[simp] theorem greedy_zero (n K : ℕ) :
    greedy K (fun _ : Fin n => (0 : ℚ)) = [(1, ∅)] := by
  cases n <;> simp [greedy, greedyAux, fractional, ones]

theorem feasible_zero_rank {n : ℕ} {z : Fin n → ℚ} (h : Feasible 0 z) : z = 0 := by
  funext i
  have hi : z i ≤ ∑ j, z j := Finset.single_le_sum (fun j _ => (h.1 j).1) (Finset.mem_univ i)
  have hh := h.2
  simp only [Nat.cast_zero] at hh
  exact le_antisymm (hi.trans hh) (h.1 i).1

theorem greedy_zero_rank {n : ℕ} {z : Fin n → ℚ} (h : Feasible 0 z) :
    greedy 0 z = [(1, ∅)] := by
  rw [feasible_zero_rank h]
  exact greedy_zero n 0

theorem feasible_full_rank {n K : ℕ} {z : Fin n → ℚ} (hK : n ≤ K)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1) : Feasible K z := by
  refine ⟨hz, ?_⟩
  calc
    ∑ i, z i ≤ ∑ _i : Fin n, (1 : ℚ) := Finset.sum_le_sum (fun i _ => (hz i).2)
    _ = n := by simp
    _ ≤ K := by exact_mod_cast hK

end BalancedAssortments.Decomposition
