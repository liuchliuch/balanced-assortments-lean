import BalancedAssortments.DecompositionAlgorithm

namespace BalancedAssortments.Decomposition

/-- A rational lies on a fixed denominator grid. Integers are used so closure
under subtraction is unconditional. -/
def OnGrid (D : ℕ) (x : ℚ) : Prop := ∃ k : ℤ, x = (k : ℚ) / D

theorem OnGrid.sub {D : ℕ} {x y : ℚ} (hx : OnGrid D x) (hy : OnGrid D y) :
    OnGrid D (x - y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a - b, by push_cast; ring⟩

theorem OnGrid.zero (D : ℕ) : OnGrid D 0 := ⟨0, by simp⟩

theorem OnGrid.one {D : ℕ} (hD : 0 < D) : OnGrid D 1 := by
  refine ⟨(D : ℤ), ?_⟩
  simp [ne_of_gt hD]

/-- Taking a greedy step preserves the common grid for its *actual* probability
mass, avoiding multiplication of denominators across recursive rounds. -/
theorem greedyStep_scaled_grid {n D K : ℕ} {z : Fin n → ℚ} {R : ℚ}
    (h : Feasible K z) {S : Finset (Fin n)} (hS : PeelSet K z S)
    (hf : (fractional z).Nonempty) (hR : OnGrid D R)
    (hz : ∀ i, OnGrid D (R * z i)) : OnGrid D (R * greedyStep z S) := by
  obtain ⟨_, _, _, i, _, hi⟩ := greedyStep_spec h hS hf
  rw [hi]
  unfold stepBound
  split_ifs
  · exact hz i
  · rw [mul_sub, mul_one]
    exact hR.sub (hz i)

theorem residual_scaled_grid {n D : ℕ} {z : Fin n → ℚ}
    {S : Finset (Fin n)} {t R : ℚ} (ht : t < 1)
    (hz : ∀ i, OnGrid D (R * z i)) (htg : OnGrid D (R * t)) :
    ∀ i, OnGrid D ((R * (1 - t)) * residual z S t i) := by
  intro i
  have hd : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  by_cases hi : i ∈ S
  · have he : (R * (1 - t)) * residual z S t i = R * z i - R * t := by
      simp only [residual, hi, ↓reduceIte]
      field_simp
    rw [he]
    exact (hz i).sub htg
  · have he : (R * (1 - t)) * residual z S t i = R * z i := by
      simp only [residual, hi, ↓reduceIte, sub_zero]
      field_simp
    rw [he]
    exact hz i

/-- Every recursive output mass, scaled by the remaining mass, lies on the
original denominator grid. This rules out exponential denominator growth. -/
theorem greedyAux_scaled_grid {n D : ℕ} (fuel : ℕ) {K : ℕ} {z : Fin n → ℚ}
    {R : ℚ} (h : Feasible K z) (hf : (fractional z).card ≤ fuel)
    (hR : OnGrid D R) (hz : ∀ i, OnGrid D (R * z i)) :
    ∀ a ∈ greedyAux fuel K z, OnGrid D (R * a.1) := by
  induction fuel generalizing z R with
  | zero =>
    intro a ha
    have he : a = (1, ones z) := by simpa [greedyAux] using ha
    simpa [he] using hR
  | succ fuel ih =>
    by_cases he : fractional z = ∅
    · intro a ha
      have hae : a = (1, ones z) := by simpa [greedyAux, he] using ha
      simpa [hae] using hR
    · let S := greedySet K z
      let t := greedyStep z S
      have hS : PeelSet K z S := greedySet_valid h
      have hne := Finset.nonempty_iff_ne_empty.mpr he
      obtain ⟨ht0, ht1, hb, i, hi, ht⟩ := greedyStep_spec h hS hne
      have hres : Feasible K (residual z S t) := residual_feasible h hS ht1 hb
      have hprog := residual_progress h hS ht1 hi ht
      change (fractional (residual z S t)).card < (fractional z).card at hprog
      have htg : OnGrid D (R * t) := greedyStep_scaled_grid h hS hne hR hz
      have hR' : OnGrid D (R * (1 - t)) := by
        rw [mul_sub, mul_one]
        exact hR.sub htg
      have hz' := residual_scaled_grid (S := S) (t := t) ht1 hz htg
      have hr := ih hres (by omega) hR' hz'
      intro a ha
      simp only [greedyAux, if_neg he] at ha
      change a ∈ prependPeel S t (greedyAux fuel K (residual z S t)) at ha
      simp only [prependPeel, List.mem_cons, List.mem_map] at ha
      rcases ha with hae | ⟨b, hb, rfl⟩
      · simpa [hae] using htg
      · simpa only [mul_assoc] using hr b hb

/-- Common denominator for all input coordinates. Its binary length is at most
the sum of the coordinate denominator lengths, plus one. -/
def commonDenominator {n : ℕ} (z : Fin n → ℚ) : ℕ := ∏ i, (z i).den

theorem commonDenominator_pos {n : ℕ} (z : Fin n → ℚ) : 0 < commonDenominator z := by
  exact Finset.prod_pos (fun i _ => Rat.den_pos (z i))

theorem coordinate_on_common_grid {n : ℕ} (z : Fin n → ℚ) (i : Fin n) :
    OnGrid (commonDenominator z) (z i) := by
  have hd : (z i).den ∣ commonDenominator z := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨m, hm⟩ := hd
  refine ⟨(z i).num * (m : ℤ), ?_⟩
  have hd0 : (z i).den ≠ 0 := ne_of_gt (Rat.den_pos _)
  have hm0 : m ≠ 0 := by
    intro he
    have hh := commonDenominator_pos z
    simp [hm, he] at hh
  rw [hm]
  push_cast
  rw [mul_div_mul_right _ _ (by exact_mod_cast hm0)]
  exact (Rat.num_div_den (z i)).symm

theorem greedy_weights_on_common_grid {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    ∀ a ∈ greedy K z, OnGrid (commonDenominator z) a.1 := by
  have hf : (fractional z).card ≤ n := by simpa using Finset.card_le_univ (fractional z)
  simpa [greedy] using greedyAux_scaled_grid n h hf
    (OnGrid.one (commonDenominator_pos z)) (fun i => by simpa using coordinate_on_common_grid z i)

theorem OnGrid.den_dvd {D : ℕ} {x : ℚ} (hx : OnGrid D x) : x.den ∣ D := by
  obtain ⟨k, hk⟩ := hx
  have he : x = Rat.divInt k (D : ℤ) := by simpa [Rat.divInt_eq_div] using hk
  rw [he]
  exact_mod_cast Rat.den_dvd k (D : ℤ)

/-- Canonical output denominators divide the input common denominator. -/
theorem greedy_den_dvd {n : ℕ} {K : ℕ} {z : Fin n → ℚ} (h : Feasible K z)
    {a : Atom n} (ha : a ∈ greedy K z) : a.1.den ∣ commonDenominator z :=
  (greedy_weights_on_common_grid h a ha).den_dvd

private theorem weight_le_one {n K : ℕ} {z : Fin n → ℚ} {p : List (Atom n)}
    (hp : ValidDecomposition K z p) {a : Atom n} (ha : a ∈ p) : a.1 ≤ 1 := by
  rw [← hp.2.1]
  apply List.single_le_sum
  · intro x hx
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
    exact hp.1 b hb
  · exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- The normalized numerator and denominator of every probability are bounded
by the original common denominator. -/
theorem greedy_num_den_bound {n : ℕ} {K : ℕ} {z : Fin n → ℚ} (h : Feasible K z)
    {a : Atom n} (ha : a ∈ greedy K z) :
    a.1.num.natAbs ≤ commonDenominator z ∧ a.1.den ≤ commonDenominator z := by
  have hd : a.1.den ≤ commonDenominator z :=
    Nat.le_of_dvd (commonDenominator_pos z) (greedy_den_dvd h ha)
  refine ⟨?_, hd⟩
  have hp := (greedy_correct h).1
  have hnonneg := (Rat.num_nonneg).mpr (hp.1 a ha)
  have hq := weight_le_one hp ha
  have hcast : (a.1.num : ℚ) ≤ (a.1.den : ℚ) := by
    apply (div_le_one (by exact_mod_cast Rat.den_pos a.1)).mp
    rwa [Rat.num_div_den]
  have hi : a.1.num ≤ (a.1.den : ℤ) := by exact_mod_cast hcast
  have hn : a.1.num.natAbs ≤ a.1.den := by
    have hi' : (a.1.num.natAbs : ℤ) ≤ (a.1.den : ℤ) := by
      rw [Int.natAbs_of_nonneg hnonneg]
      exact hi
    exact_mod_cast hi'
  exact hn.trans hd

/-- Binary encoding budget contributed by the input denominators. -/
def denominatorBits {n : ℕ} (z : Fin n → ℚ) : ℕ := ∑ i, (z i).den.size

theorem commonDenominator_size_bound {n : ℕ} (z : Fin n → ℚ) :
    (commonDenominator z).size ≤ denominatorBits z + 1 := by
  have hp : commonDenominator z ≤ 2 ^ denominatorBits z := by
    calc
      commonDenominator z ≤ ∏ i : Fin n, 2 ^ (z i).den.size := by
        exact Finset.prod_le_prod' (fun i _ => (Nat.lt_size_self (z i).den).le)
      _ = 2 ^ denominatorBits z := by simp [denominatorBits, Finset.prod_pow_eq_pow_sum]
  apply Nat.size_le.mpr
  have hpos : 0 < 2 ^ denominatorBits z := by positivity
  rw [pow_succ]
  omega

/-- Explicit polynomial output bit-size: each canonical numerator and denominator
has at most one plus the sum of the input denominator binary lengths. -/
theorem greedy_probability_bit_bound {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) {a : Atom n} (ha : a ∈ greedy K z) :
    a.1.num.natAbs.size ≤ denominatorBits z + 1 ∧
      a.1.den.size ≤ denominatorBits z + 1 := by
  have hh := greedy_num_den_bound h ha
  exact ⟨(Nat.size_le_size hh.1).trans (commonDenominator_size_bound z),
    (Nat.size_le_size hh.2).trans (commonDenominator_size_bound z)⟩

/-- Payload encoding: one `n`-bit incidence vector and binary numerator and
 denominator per atom. Framing and sign conventions are excluded. -/
def policyPayloadBits {n : ℕ} (p : List (Atom n)) : ℕ :=
  (p.map fun a => a.1.num.natAbs.size + a.1.den.size + n).sum

/-- The complete rational policy payload has polynomial size. -/
theorem greedy_policy_payload_bound {n : ℕ} {K : ℕ} {z : Fin n → ℚ}
    (h : Feasible K z) :
    policyPayloadBits (greedy K z) ≤
      (n + 1) * (2 * (denominatorBits z + 1) + n) := by
  let B := 2 * (denominatorBits z + 1) + n
  have hs := List.sum_le_card_nsmul
    ((greedy K z).map fun a => a.1.num.natAbs.size + a.1.den.size + n) B (by
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      have hb := greedy_probability_bit_bound h ha
      dsimp [B]
      omega)
  simp only [List.length_map, nsmul_eq_mul] at hs
  exact hs.trans (Nat.mul_le_mul_right B (greedy_correct h).2)

end BalancedAssortments.Decomposition
