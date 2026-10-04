import BalancedAssortments.DecompositionBitBounds

namespace BalancedAssortments.Decomposition

/-- A unit-interval rational's reduced numerator is bounded by its denominator. -/
theorem unit_num_le_den {x : ℚ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x.num.natAbs ≤ x.den := by
  have hn : 0 ≤ x.num := Rat.num_nonneg.mpr hx0
  have hq : (x.num : ℚ) ≤ (x.den : ℚ) := by
    apply (div_le_one (by exact_mod_cast Rat.den_pos x)).mp
    rwa [Rat.num_div_den]
  have hi : x.num ≤ (x.den : ℤ) := by exact_mod_cast hq
  have hi' : (x.num.natAbs : ℤ) ≤ (x.den : ℤ) := by
    rw [Int.natAbs_of_nonneg hn]
    exact hi
  exact_mod_cast hi'

/-- Division of two original-grid amounts does not create a large denominator:
the reduced denominator is at most the positive divisor's grid numerator. -/
theorem normalized_grid_bound {D : ℕ} (hD : 0 < D) {R x : ℚ}
    (hR0 : 0 < R) (hR1 : R ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hR : OnGrid D R) (hRx : OnGrid D (R * x)) :
    x.num.natAbs ≤ D ∧ x.den ≤ D := by
  obtain ⟨r, hr⟩ := hR
  obtain ⟨a, ha⟩ := hRx
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  have hrq : (0 : ℚ) < (r : ℚ) := by
    rw [hr] at hR0
    exact (div_pos_iff_of_pos_right hDq).mp hR0
  have hrpos : 0 < r := by exact_mod_cast hrq
  have hrle : r ≤ (D : ℤ) := by
    have hh : (r : ℚ) ≤ (D : ℚ) := by
      apply (div_le_one hDq).mp
      rwa [← hr]
    exact_mod_cast hh
  have hxeq : x = Rat.divInt a r := by
    rw [Rat.divInt_eq_div]
    apply (eq_div_iff (ne_of_gt hrq)).mpr
    have he : (r : ℚ) * x = (a : ℚ) := by
      rw [hr] at ha
      apply (div_left_inj' hDq.ne').mp
      simpa [div_mul_eq_mul_div] using ha
    simpa [mul_comm] using he
  have hden : x.den ≤ D := by
    have hdiv : (x.den : ℤ) ∣ r := by rw [hxeq]; exact Rat.den_dvd a r
    have hh : (x.den : ℤ) ≤ (D : ℤ) := (Int.le_of_dvd hrpos hdiv).trans hrle
    exact_mod_cast hh
  exact ⟨(unit_num_le_den hx0 hx1).trans hden, hden⟩

/-- Execution states of the actual `greedyAux` recursion, together with the
remaining probability mass. No new choice of sets or steps is introduced. -/
def greedyTraceAux {n : ℕ} : ℕ → ℕ → ℚ → (Fin n → ℚ) → List (ℚ × (Fin n → ℚ))
  | 0, _, R, z => [(R, z)]
  | fuel + 1, K, R, z =>
    (R, z) :: if fractional z = ∅ then [] else
      let S := greedySet K z
      let t := greedyStep z S
      greedyTraceAux fuel K (R * (1 - t)) (residual z S t)

def greedyTrace {n : ℕ} (K : ℕ) (z : Fin n → ℚ) : List (ℚ × (Fin n → ℚ)) :=
  greedyTraceAux n K 1 z

/-- The trace includes at most `fuel+1` states. -/
theorem greedyTraceAux_length {n : ℕ} (fuel K : ℕ) (R : ℚ) (z : Fin n → ℚ) :
    (greedyTraceAux fuel K R z).length ≤ fuel + 1 := by
  induction fuel generalizing R z with
  | zero => simp [greedyTraceAux]
  | succ fuel ih =>
    simp only [greedyTraceAux, List.length_cons]
    split_ifs
    · simp
    · have := ih (R * (1 - greedyStep z (greedySet K z)))
        (residual z (greedySet K z) (greedyStep z (greedySet K z)))
      omega

/-- Strong invariant for every recursive rational state. -/
def GridState {n : ℕ} (K D : ℕ) (st : ℚ × (Fin n → ℚ)) : Prop :=
  Feasible K st.2 ∧ 0 < st.1 ∧ st.1 ≤ 1 ∧ OnGrid D st.1 ∧
    ∀ i, OnGrid D (st.1 * st.2 i)

theorem greedyTraceAux_invariant {n D : ℕ} (fuel : ℕ) {K : ℕ}
    {R : ℚ} {z : Fin n → ℚ} (hs : GridState K D (R, z)) :
    ∀ st ∈ greedyTraceAux fuel K R z, GridState K D st := by
  induction fuel generalizing R z with
  | zero => simpa [greedyTraceAux] using hs
  | succ fuel ih =>
    intro st hst
    simp only [greedyTraceAux, List.mem_cons] at hst
    rcases hst with he | hst
    · simpa [he] using hs
    · split_ifs at hst with hempty
      · simp at hst
      · let S := greedySet K z
        let t := greedyStep z S
        have hS : PeelSet K z S := greedySet_valid hs.1
        have hf := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨ht0, ht1, hb, i, hi, ht⟩ := greedyStep_spec hs.1 hS hf
        have htg : OnGrid D (R * t) := greedyStep_scaled_grid hs.1 hS hf hs.2.2.2.1 hs.2.2.2.2
        have hR' : OnGrid D (R * (1 - t)) := by
          rw [mul_sub, mul_one]
          exact hs.2.2.2.1.sub htg
        have hz' := residual_scaled_grid (S := S) (t := t) ht1 hs.2.2.2.2 htg
        apply ih (R := R * (1 - t)) (z := residual z S t) ?_ st hst
        refine ⟨residual_feasible hs.1 hS ht1 hb, mul_pos hs.2.1 (sub_pos.mpr ht1), ?_, hR', hz'⟩
        have hh : R * (1 - t) ≤ R := by nlinarith [hs.2.1, ht0]
        exact hh.trans hs.2.2.1

theorem greedyTrace_invariant {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z) :
    ∀ st ∈ greedyTrace K z, GridState K (commonDenominator z) st := by
  apply greedyTraceAux_invariant
  refine ⟨h, by norm_num, by norm_num, OnGrid.one (commonDenominator_pos z), ?_⟩
  intro i
  simpa using coordinate_on_common_grid z i

/-- Every coordinate in every actual recursive state has numerator and denominator
bounded by the original input denominator product, not a recursively growing one. -/
theorem greedyTrace_coordinate_bound {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z)
    {st : ℚ × (Fin n → ℚ)} (hst : st ∈ greedyTrace K z) (i : Fin n) :
    (st.2 i).num.natAbs ≤ commonDenominator z ∧ (st.2 i).den ≤ commonDenominator z := by
  have hs := greedyTrace_invariant h st hst
  exact normalized_grid_bound (commonDenominator_pos z) hs.2.1 hs.2.2.1
    (hs.1.1 i).1 (hs.1.1 i).2 hs.2.2.2.1 (hs.2.2.2.2 i)

/-- Polynomial bit size of every intermediate coordinate. -/
theorem greedyTrace_coordinate_bits {n K : ℕ} {z : Fin n → ℚ} (h : Feasible K z)
    {st : ℚ × (Fin n → ℚ)} (hst : st ∈ greedyTrace K z) (i : Fin n) :
    (st.2 i).num.natAbs.size ≤ denominatorBits z + 1 ∧
      (st.2 i).den.size ≤ denominatorBits z + 1 := by
  have hb := greedyTrace_coordinate_bound h hst i
  exact ⟨(Nat.size_le_size hb.1).trans (commonDenominator_size_bound z),
    (Nat.size_le_size hb.2).trans (commonDenominator_size_bound z)⟩

end BalancedAssortments.Decomposition
