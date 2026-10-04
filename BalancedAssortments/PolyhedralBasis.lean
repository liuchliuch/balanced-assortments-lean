import Mathlib

/-! Active-constraint basis infrastructure for bounded rational polyhedra.
No polynomial LP solver or small-certificate oracle is assumed. -/
noncomputable section
namespace BalancedAssortments.PolyhedralBasis
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

def evaluate (A : Matrix I (Fin n) ℝ) (x : Fin n → ℝ) (i : I) : ℝ :=
  ∑ j, A i j * x j

def polyhedron (A : Matrix I (Fin n) ℝ) (b : I → ℝ) : Set (Fin n → ℝ) :=
  {x | ∀ i, evaluate A x i ≤ b i}

lemma evaluate_add_smul (A : Matrix I (Fin n) ℝ) (x d : Fin n → ℝ) (t : ℝ) (i : I) :
    evaluate A (x + t • d) i = evaluate A x i + t * evaluate A d i := by
  simp only [evaluate, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Any direction annihilating all active constraints can be moved a positive
distance in both signs while remaining feasible. The step is constructed from
all finite slacks; there is no local-feasibility assumption. -/
theorem two_sided_feasible (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (x d : Fin n → ℝ) (hx : x ∈ polyhedron A b)
    (hactive : ∀ i, evaluate A x i = b i → evaluate A d i = 0) :
    ∃ t : ℝ, 0 < t ∧ x + t • d ∈ polyhedron A b ∧ x + (-t) • d ∈ polyhedron A b := by
  let S := ∑ i, |evaluate A d i| / (b i - evaluate A x i)
  have hnonneg : ∀ i, 0 ≤ |evaluate A d i| / (b i - evaluate A x i) := fun i =>
    div_nonneg (abs_nonneg _) (sub_nonneg.mpr (hx i))
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hnonneg i)
  let t := 1 / (1 + S)
  have ht : 0 < t := by dsimp [t]; positivity
  have htS : t * S ≤ 1 := by
    dsimp [t]
    rw [one_div_mul_eq_div]
    apply (div_le_one (by positivity)).2
    linarith
  have hbound : ∀ i, t * |evaluate A d i| ≤ b i - evaluate A x i := by
    intro i
    by_cases he : evaluate A x i = b i
    · simp [hactive i he, he]
    · have hs : 0 < b i - evaluate A x i := sub_pos.mpr (lt_of_le_of_ne (hx i) he)
      have hterm : |evaluate A d i| / (b i - evaluate A x i) ≤ S :=
        Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      have habs := (div_le_iff₀ hs).1 hterm
      calc t * |evaluate A d i| ≤ t * (S * (b i - evaluate A x i)) :=
             mul_le_mul_of_nonneg_left habs ht.le
           _ = (t * S) * (b i - evaluate A x i) := by ring
           _ ≤ 1 * (b i - evaluate A x i) := mul_le_mul_of_nonneg_right htS hs.le
           _ = _ := one_mul _
  refine ⟨t, ht, ?_, ?_⟩
  · intro i
    rw [evaluate_add_smul]
    have hb := hbound i
    have ha := mul_le_mul_of_nonneg_left (le_abs_self (evaluate A d i)) ht.le
    linarith
  · intro i
    rw [evaluate_add_smul]
    have hb := hbound i
    have ha := mul_le_mul_of_nonneg_left (neg_le_abs (evaluate A d i)) ht.le
    linarith

/-- At an extreme point, active constraints have no common nonzero null direction. -/
theorem active_kernel_trivial (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ (polyhedron A b).extremePoints ℝ)
    (d : Fin n → ℝ) (hd : ∀ i, evaluate A x i = b i → evaluate A d i = 0) : d = 0 := by
  obtain ⟨t, ht, hp, hm⟩ := two_sided_feasible A b x d hx.1 hd
  have hseg : x ∈ openSegment ℝ (x + t • d) (x + (-t) • d) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := hx.2 hp hm hseg
  funext j
  have hj := congr_fun he j
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hj
  have : t * d j = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left ht.ne'

/-- An extreme point has n independent active rows, selected from the actual
input inequalities. This supplies a nonsingular square active subsystem. -/
theorem extreme_has_active_basis (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (x : Fin n → ℝ) (hx : x ∈ (polyhedron A b).extremePoints ℝ) :
    ∃ f : Fin n → I, Function.Injective f ∧
      (∀ j, evaluate A x (f j) = b (f j)) ∧
      (A.submatrix f id).det ≠ 0 := by
  classical
  let J := {i : I // evaluate A x i = b i}
  let M : Matrix J (Fin n) ℝ := fun i j => A i.val j
  have hker : ∀ d : Fin n → ℝ, M.mulVec d = 0 → d = 0 := by
    intro d hd
    apply active_kernel_trivial A b x hx d
    intro i hi
    exact congr_fun hd (⟨i, hi⟩ : J)
  have hinj : Function.Injective M.mulVecLin := by
    intro u v he
    have hh : M.mulVec (u - v) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr he
    exact sub_eq_zero.mp (hker (u-v) hh)
  have hfull : Submodule.span ℝ (Set.range M.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row]
    exact LinearMap.finrank_range_of_inj hinj
  obtain ⟨κ, a, ha, hspan, hlin⟩ := exists_linearIndependent' ℝ M.row
  letI : Fintype κ := Fintype.ofInjective a ha
  let basis : Module.Basis κ ℝ (Fin n → ℝ) := Module.Basis.mk hlin (by rw [hspan, hfull])
  have hcard : Fintype.card κ = n := by
    simpa using (Module.finrank_eq_card_basis basis).symm
  let e : Fin n ≃ κ := (finCongr hcard.symm).trans (Fintype.equivFin κ).symm
  let f : Fin n → I := fun j => (a (e j)).val
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (ha (Subtype.ext hij))
  · intro j
    exact (a (e j)).property
  · have hli : LinearIndependent ℝ (A.submatrix f id).row := hlin.comp e e.injective
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli
    exact (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu))

/-- Every nonempty compact polyhedron admits a feasible point with a nonsingular
active subsystem. Compactness may be discharged using explicit coordinate bounds. -/
theorem compact_has_active_basis (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (hc : IsCompact (polyhedron A b)) (hn : (polyhedron A b).Nonempty) :
    ∃ (x : Fin n → ℝ) (f : Fin n → I), x ∈ polyhedron A b ∧ Function.Injective f ∧
      (∀ j, evaluate A x (f j) = b (f j)) ∧ (A.submatrix f id).det ≠ 0 := by
  obtain ⟨x, hx⟩ := hc.extremePoints_nonempty hn
  obtain ⟨f, hf, he, hd⟩ := extreme_has_active_basis A b x hx
  exact ⟨x, f, hx.1, hf, he, hd⟩

theorem polyhedron_closed (A : Matrix I (Fin n) ℝ) (b : I → ℝ) :
    IsClosed (polyhedron A b) := by
  unfold polyhedron
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le _ continuous_const
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))

/-- Explicit coordinate bounds discharge compactness. -/
theorem polyhedron_compact (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (lo hi : Fin n → ℝ)
    (hbound : ∀ x ∈ polyhedron A b, ∀ j, lo j ≤ x j ∧ x j ≤ hi j) :
    IsCompact (polyhedron A b) := by
  apply (isCompact_Icc : IsCompact (Set.Icc lo hi)).of_isClosed_subset (polyhedron_closed A b)
  intro x hx
  exact ⟨fun j => (hbound x hx j).1, fun j => (hbound x hx j).2⟩

end BalancedAssortments.PolyhedralBasis
