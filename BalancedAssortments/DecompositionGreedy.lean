import BalancedAssortments.Decomposition

namespace BalancedAssortments.Decomposition

/-- The rational uniform-matroid independence polytope. -/
def Feasible {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : Prop :=
  (∀ i, 0 ≤ z i ∧ z i ≤ 1) ∧ ∑ i, z i ≤ (K : ℚ)

/-- Fractional coordinates are the progress measure for greedy peeling. -/
def fractional {n : ℕ} (z : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i ≠ 0 ∧ z i ≠ 1

def ones {n : ℕ} (z : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i => z i = 1

def positive {n : ℕ} (z : Fin n → ℚ) : Finset (Fin n) :=
  Finset.univ.filter fun i => 0 < z i

/-- A greedy integral set includes every already-integral one and either has
full rank or contains every positive coordinate. -/
def PeelSet {n : ℕ} (K : ℕ) (z : Fin n → ℚ) (S : Finset (Fin n)) : Prop :=
  ones z ⊆ S ∧ S ⊆ positive z ∧ S.card ≤ K ∧
    (S.card = K ∨ positive z ⊆ S)

private theorem ones_card_le {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) : (ones z).card ≤ K := by
  have hc : ((ones z).card : ℚ) ≤ ∑ i, z i := by
    calc
      ((ones z).card : ℚ) = ∑ i ∈ ones z, z i := by
        rw [show (∑ i ∈ ones z, z i) = ∑ _i ∈ ones z, (1 : ℚ) from
          Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)]
        simp
      _ ≤ ∑ i, z i := Finset.sum_le_univ_sum_of_nonneg (fun i => (h.1 i).1)
  exact_mod_cast hc.trans h.2

/-- Selecting a legal peel set needs only finite-set cardinality, not a
convex-hull membership assumption. -/
theorem exists_peelSet {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) : ∃ S, PeelSet K z S := by
  have hop : ones z ⊆ positive z := by
    intro i hi
    simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp [positive, hi]
  by_cases hp : (positive z).card ≤ K
  · exact ⟨positive z, hop, Finset.Subset.refl _, hp, Or.inr (Finset.Subset.refl _)⟩
  · have ho := ones_card_le h
    obtain ⟨S, hos, hsp, hcard⟩ := Finset.exists_subsuperset_card_eq hop ho (le_of_not_ge hp)
    exact ⟨S, hos, hsp, hcard.le, Or.inl hcard⟩

/-- Distance to a newly fixed boundary when peeling the set `S`. -/
def stepBound {n : ℕ} (z : Fin n → ℚ) (S : Finset (Fin n)) (i : Fin n) : ℚ :=
  if i ∈ S then z i else 1 - z i

/-- The residual after taking mass `t` from one integral assortment. -/
def residual {n : ℕ} (z : Fin n → ℚ) (S : Finset (Fin n)) (t : ℚ) : Fin n → ℚ :=
  fun i => (z i - if i ∈ S then t else 0) / (1 - t)

theorem residual_box {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} {t : ℚ} (ht : t < 1)
    (hb : ∀ i, t ≤ stepBound z S i) :
    ∀ i, 0 ≤ residual z S t i ∧ residual z S t i ≤ 1 := by
  intro i
  have hd : 0 < 1 - t := sub_pos.mpr ht
  unfold residual
  constructor
  · apply div_nonneg _ hd.le
    by_cases hi : i ∈ S
    · simpa [hi, stepBound, sub_nonneg] using hb i
    · simpa [hi] using (h.1 i).1
  · apply (div_le_one hd).mpr
    by_cases hi : i ∈ S
    · simpa [hi] using (h.1 i).2
    · have hi' := hb i
      simp only [stepBound, hi, ↓reduceIte] at hi'
      simp only [hi, ↓reduceIte, sub_zero]
      linarith

theorem residual_feasible {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    {t : ℚ} (ht : t < 1) (hb : ∀ i, t ≤ stepBound z S i) :
    Feasible K (residual z S t) := by
  have hbox := residual_box h ht hb
  refine ⟨hbox, ?_⟩
  rcases hS.2.2.2 with hfull | hpos
  · have hsum : (∑ i, residual z S t i) =
        ((∑ i, z i) - (S.card : ℚ) * t) / (1 - t) := by
      simp only [residual, ← Finset.sum_div, Finset.sum_sub_distrib]
      congr 1
      simp
    rw [hsum, hfull]
    apply (div_le_iff₀ (sub_pos.mpr ht)).mpr
    nlinarith [h.2]
  · have hzero : ∀ i, i ∉ S → residual z S t i = 0 := by
      intro i hi
      have hz : z i = 0 := by
        have hn : ¬0 < z i := fun hp => hi (hpos (by simp [positive, hp]))
        exact le_antisymm (le_of_not_gt hn) (h.1 i).1
      simp [residual, hi, hz]
    calc
      ∑ i, residual z S t i ≤ ∑ i : Fin n, if i ∈ S then (1 : ℚ) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact (hbox i).2
        · simp [hzero i hi]
      _ = (S.card : ℚ) := by simp
      _ ≤ (K : ℚ) := by exact_mod_cast hS.2.2.1

private theorem stepBound_pos {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    (i : Fin n) : 0 < stepBound z S i := by
  unfold stepBound
  split_ifs with hi
  · exact (Finset.mem_filter.mp (hS.2.1 hi)).2
  · apply sub_pos.mpr
    exact lt_of_le_of_ne (h.1 i).2 (fun he => hi (hS.1 (by simp [ones, he])))

private theorem stepBound_eq_one {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    {i : Fin n} (hi : i ∉ fractional z) : stepBound z S i = 1 := by
  have hz : z i = 0 ∨ z i = 1 := by
    by_cases hz : z i = 0
    · exact Or.inl hz
    · exact Or.inr (by simpa [fractional, hz] using hi)
  rcases hz with hz | hz
  · have hn : i ∉ S := by
      intro hm
      have hp := (Finset.mem_filter.mp (hS.2.1 hm)).2
      simpa [hz] using hp
    simp [stepBound, hn, hz]
  · have hm : i ∈ S := hS.1 (by simp [ones, hz])
    simp [stepBound, hm, hz]

private theorem stepBound_lt_one {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ fractional z) : stepBound z S i < 1 := by
  have hfrac := (Finset.mem_filter.mp hi).2
  unfold stepBound
  split_ifs
  · exact lt_of_le_of_ne (h.1 i).2 hfrac.2
  · have hp : 0 < z i := lt_of_le_of_ne (h.1 i).1 (Ne.symm hfrac.1)
    linarith

/-- A positive rational step strictly below one, attained at a fractional
coordinate. At that coordinate the residual hits zero or one. -/
theorem exists_peel_step {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    (hf : (fractional z).Nonempty) :
    ∃ t : ℚ, 0 < t ∧ t < 1 ∧ (∀ i, t ≤ stepBound z S i) ∧
      ∃ i ∈ fractional z, t = stepBound z S i := by
  obtain ⟨i, hi, hmin⟩ := (fractional z).exists_min_image (stepBound z S) hf
  refine ⟨stepBound z S i, stepBound_pos h hS i, stepBound_lt_one h hi, ?_, i, hi, rfl⟩
  intro j
  by_cases hj : j ∈ fractional z
  · exact hmin j hj
  · rw [stepBound_eq_one h hS hj]
    exact (stepBound_lt_one h hi).le

theorem residual_fractional_subset {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    {t : ℚ} (ht : t < 1) : fractional (residual z S t) ⊆ fractional z := by
  intro i hi
  have hri := (Finset.mem_filter.mp hi).2
  by_contra hn
  by_cases hz : z i = 0
  · have hs : i ∉ S := by
      intro hm
      have hp := (Finset.mem_filter.mp (hS.2.1 hm)).2
      simpa [hz] using hp
    exact hri.1 (by simp [residual, hs, hz])
  · have hz1 : z i = 1 := by simpa [fractional, hz] using hn
    have hs : i ∈ S := hS.1 (by simp [ones, hz1])
    exact hri.2 (by simp [residual, hs, hz1, ne_of_gt (sub_pos.mpr ht)])

theorem residual_progress {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    {t : ℚ} (ht : t < 1) {i : Fin n} (hi : i ∈ fractional z)
    (he : t = stepBound z S i) :
    (fractional (residual z S t)).card < (fractional z).card := by
  have hn : i ∉ fractional (residual z S t) := by
    have hd : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
    by_cases hs : i ∈ S
    · have he' : t = z i := by simpa [stepBound, hs] using he
      simp [fractional, residual, hs, ← he']
    · have he' : t = 1 - z i := by simpa [stepBound, hs] using he
      have hz : z i = 1 - t := by linarith
      simp [fractional, residual, hs, hz, hd]
  have hsub := residual_fractional_subset h hS ht
  apply Finset.card_lt_card
  exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hn (heq.symm ▸ hi)⟩

/-- Prefix one atom and scale the remaining rational distribution. -/
def prependPeel {n : ℕ} (S : Finset (Fin n)) (t : ℚ) (p : List (Atom n)) :
    List (Atom n) := (t, S) :: p.map (fun a => ((1 - t) * a.1, a.2))

@[simp] theorem prependPeel_length {n : ℕ} (S : Finset (Fin n)) (t : ℚ)
    (p : List (Atom n)) : (prependPeel S t p).length = p.length + 1 := by
  simp [prependPeel]

theorem prependPeel_valid {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    {S : Finset (Fin n)} (hS : S.card ≤ K) {t : ℚ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    {p : List (Atom n)} (hp : ValidDecomposition K (residual z S t) p) :
    ValidDecomposition K z (prependPeel S t p) := by
  have hd : 0 < 1 - t := sub_pos.mpr ht1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_cons.mp ha with he | ha
    · subst a; exact ht0
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact mul_nonneg hd.le (hp.1 b hb)
  · simp only [prependPeel, List.map_cons, List.map_map, Function.comp_def, List.sum_cons]
    rw [List.sum_map_mul_left, hp.2.1]
    ring
  · intro a ha hn
    rcases List.mem_cons.mp ha with he | ha
    · subst a; exact hS
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact hp.2.2.1 b hb (fun hz => hn (by simp [hz]))
  · intro i
    simp only [prependPeel, List.map_cons, List.map_map, Function.comp_def, List.sum_cons]
    simp_rw [← mul_ite_zero]
    rw [List.sum_map_mul_left, hp.2.2.2 i]
    unfold residual
    rw [mul_div_cancel₀ _ hd.ne']
    split_ifs <;> ring

/-- Integral points are represented by their unique incidence set. -/
theorem integral_decomposition {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) (hf : fractional z = ∅) :
    ValidDecomposition K z [(1, ones z)] := by
  refine ⟨?_, by simp, ?_, ?_⟩
  · intro a ha
    simpa using (List.mem_singleton.mp ha ▸ (show (0 : ℚ) ≤ 1 by norm_num))
  · intro a ha _
    obtain rfl := List.mem_singleton.mp ha
    exact ones_card_le h
  · intro i
    have hn : i ∉ fractional z := by simp [hf]
    by_cases hz : z i = 0
    · simp [ones, hz]
    · have hz1 : z i = 1 := by simpa [fractional, hz] using hn
      simp [ones, hz1]

/-- Every rational feasible marginal vector has a rational decomposition with
at most one more atom than its number of fractional coordinates. The proof
is a terminating greedy boundary-peeling construction. -/
theorem exists_sparse_decomposition {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    ∃ p : List (Atom n), ValidDecomposition K z p ∧
      p.length ≤ (fractional z).card + 1 := by
  generalize hm : (fractional z).card = m
  induction m using Nat.strong_induction_on generalizing z with
  | h m ih =>
    by_cases hf : fractional z = ∅
    · exact ⟨[(1, ones z)], integral_decomposition h hf, by simp⟩
    · obtain ⟨S, hS⟩ := exists_peelSet h
      obtain ⟨t, ht0, ht1, hb, i, hi, he⟩ := exists_peel_step h hS (Finset.nonempty_iff_ne_empty.mpr hf)
      have hres := residual_feasible h hS ht1 hb
      have hprogress := residual_progress h hS ht1 hi he
      obtain ⟨p, hp, hlen⟩ := ih (fractional (residual z S t)).card (by omega) hres rfl
      refine ⟨prependPeel S t p, prependPeel_valid hS.2.2.1 ht0.le ht1 hp, ?_⟩
      rw [prependPeel_length]
      omega

theorem exists_linear_decomposition {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    ∃ p : List (Atom n), ValidDecomposition K z p ∧ p.length ≤ n + 1 := by
  obtain ⟨p, hp, hlen⟩ := exists_sparse_decomposition h
  refine ⟨p, hp, hlen.trans ?_⟩
  simpa using Nat.add_le_add_right (Finset.card_le_univ (fractional z)) 1

end BalancedAssortments.Decomposition
