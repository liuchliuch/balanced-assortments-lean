import BalancedAssortments.PolyhedralBasisRational

/-! Exact rational LP optima via exposed faces and the derived active basis.
These are optimizer existence/size theorems, not a polynomial-time LP solver. -/
noncomputable section
namespace BalancedAssortments.PolyhedralBasis
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- A linear objective on a compact nonempty polyhedron has an optimal point
with an actual nonsingular active subsystem of the original constraints. -/
theorem compact_has_optimal_active_basis (A : Matrix I (Fin n) ℝ) (b : I → ℝ)
    (c : Fin n → ℝ) (hc : IsCompact (polyhedron A b)) (hn : (polyhedron A b).Nonempty) :
    ∃ (x : Fin n → ℝ) (f : Fin n → I), x ∈ polyhedron A b ∧
      (∀ y ∈ polyhedron A b, (∑ j, c j * y j) ≤ ∑ j, c j*x j) ∧
      Function.Injective f ∧ (∀ j, evaluate A x (f j) = b (f j)) ∧
      (A.submatrix f id).det ≠ 0 := by
  let l : (Fin n → ℝ) →L[ℝ] ℝ := ∑ j, c j • ContinuousLinearMap.proj j
  have hl : ∀ x, l x = ∑ j, c j*x j := by intro x; simp [l]
  have he : IsExposed ℝ (polyhedron A b) (l.toExposed (polyhedron A b)) :=
    ContinuousLinearMap.toExposed.isExposed
  have hne : (l.toExposed (polyhedron A b)).Nonempty := by
    obtain ⟨x,hx,hmax⟩ := hc.exists_isMaxOn hn l.continuous.continuousOn
    exact ⟨x,hx,hmax⟩
  have hcompact : IsCompact (l.toExposed (polyhedron A b)) :=
    hc.of_isClosed_subset (he.isClosed hc.isClosed) he.subset
  obtain ⟨x,hx⟩ := hcompact.extremePoints_nonempty hne
  have hxe := he.isExtreme.extremePoints_subset_extremePoints hx
  obtain ⟨f,hf,ha,hd⟩ := extreme_has_active_basis A b x hxe
  refine ⟨x,f,hx.1.1,?_,hf,ha,hd⟩
  intro y hy
  simpa only [hl] using hx.1.2 y hy

/-- Every compact integer polyhedron has a small rational point maximizing any
linear objective, even when the objective itself has real coefficients. -/
theorem small_integer_optimizer {B : ℕ} (A : Matrix I (Fin n) ℤ) (b : I → ℤ)
    (c : Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ)^B) (hb : ∀ i, |b i| ≤ (2 : ℤ)^B)
    (hc : IsCompact (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))))
    (hn : (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (w : Fin n → ℚ) (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n*(B+n)+1 ∧ (∀ j,(p j).natAbs.size ≤ n*(B+n)+1) ∧
      (∀ j,w j = (p j : ℚ)/q) ∧
      (fun j => (w j : ℝ)) ∈ polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)) ∧
      ∀ y ∈ polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)),
        (∑ j,c j*y j) ≤ ∑ j,c j*(w j : ℝ) := by
  obtain ⟨x,f,hx,hmax,_,he,hdet⟩ := compact_has_optimal_active_basis _ _ c hc hn
  let N : Matrix (Fin n) (Fin n) ℤ := A.submatrix f id
  let rhs : Fin n → ℤ := fun j => b (f j)
  have hd : N.det ≠ 0 := by
    intro hz
    apply hdet
    have hh : (N.det : ℝ) = 0 := by simp [hz]
    rwa [cast_det_real] at hh
  have hs : (N.map (fun z : ℤ => (z : ℝ))).mulVec x = fun j => (rhs j : ℝ) := by
    funext j
    exact he j
  let p : Fin n → ℤ := fun j => (N.updateCol j rhs).det
  let w : Fin n → ℚ := fun j => (p j : ℚ)/N.det
  have hw : (fun j => (w j : ℝ)) = x := by
    funext j
    dsimp [w,p]
    simp only [Rat.cast_div,Rat.cast_intCast]
    exact (cramer_real_representation N rhs x hd hs j).symm
  have hN : ∀ i j, |N i j| ≤ (2:ℤ)^B := fun i j => hA (f i) j
  refine ⟨w,p,N.det,hd,CertificateBounds.det_binary_size N hN,?_,fun _ => rfl,?_,?_⟩
  · intro j
    apply CertificateBounds.det_binary_size
    intro i k
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact hb (f i)
    · exact hN i k
  · rw [hw]; exact hx
  · intro y hy
    have hj : ∀ j, (w j : ℝ) = x j := fun j => congr_fun hw j
    simpa only [hj] using hmax y hy

end BalancedAssortments.PolyhedralBasis
