import BalancedAssortments.PolyhedralBasis
import BalancedAssortments.CertificateBounds

/-! Small rational feasibility certificates for bounded integer polyhedra.
The existence of a nonsingular active basis is proved, not assumed. -/
noncomputable section
namespace BalancedAssortments.PolyhedralBasis
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

lemma cast_det_real (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.det : ℝ) = (A.map (fun z : ℤ => (z : ℝ))).det := (Int.castRingHom ℝ).map_det A

lemma cast_updateCol_real (A : Matrix (Fin n) (Fin n) ℤ) (b : Fin n → ℤ) (i : Fin n) :
    (A.updateCol i b).map (fun z : ℤ => (z : ℝ)) =
      (A.map (fun z : ℤ => (z : ℝ))).updateCol i (fun j => (b j : ℝ)) := by
  ext j k
  simp only [Matrix.map_apply, Matrix.updateCol_apply]
  split_ifs <;> rfl

/-- Real solutions of a nonsingular integer square system are rational, with
explicit determinant numerator and denominator. -/
theorem cramer_real_representation (A : Matrix (Fin n) (Fin n) ℤ)
    (b : Fin n → ℤ) (x : Fin n → ℝ) (hdet : A.det ≠ 0)
    (hsol : (A.map (fun z : ℤ => (z : ℝ))).mulVec x = fun j => (b j : ℝ))
    (i : Fin n) : x i = ((A.updateCol i b).det : ℝ) / (A.det : ℝ) := by
  let Ar := A.map (fun z : ℤ => (z : ℝ))
  have hc : Ar.cramer (fun j => (b j : ℝ)) = Ar.det • x := by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hsol, Matrix.mulVec_mulVec,
      Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hi := congr_fun hc i
  simp only [Matrix.cramer_apply, Pi.smul_apply, smul_eq_mul] at hi
  have hd : (A.det : ℝ) ≠ 0 := by exact_mod_cast hdet
  have he : ((A.updateCol i b).det : ℝ) = (A.det : ℝ) * x i := by
    rw [cast_det_real, cast_updateCol_real, cast_det_real]
    exact hi
  apply (eq_div_iff hd).mpr
  linarith

/-- Every nonempty compact integer polyhedron with B-bit coefficients admits a
rational feasible point with numerator and shared denominator sizes bounded by
n(B+n)+1. No feasible-point certificate or active basis is supplied as a premise. -/
theorem small_integer_polyhedron_certificate {B : ℕ}
    (A : Matrix I (Fin n) ℤ) (b : I → ℤ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) (hb : ∀ i, |b i| ≤ (2 : ℤ) ^ B)
    (hc : IsCompact (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))))
    (hn : (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (w : Fin n → ℚ) (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n * (B + n) + 1 ∧
      (∀ j, (p j).natAbs.size ≤ n * (B + n) + 1) ∧
      (∀ j, w j = (p j : ℚ) / q) ∧
      (fun j => (w j : ℝ)) ∈ polyhedron
        (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)) := by
  obtain ⟨x, f, hx, _, he, hdet⟩ := compact_has_active_basis _ _ hc hn
  let N : Matrix (Fin n) (Fin n) ℤ := A.submatrix f id
  let c : Fin n → ℤ := fun j => b (f j)
  have hd : N.det ≠ 0 := by
    intro hz
    apply hdet
    have hh : (N.det : ℝ) = 0 := by simp [hz]
    rwa [cast_det_real] at hh
  have hs : (N.map (fun z : ℤ => (z : ℝ))).mulVec x = fun j => (c j : ℝ) := by
    funext j
    exact he j
  let p : Fin n → ℤ := fun j => (N.updateCol j c).det
  let w : Fin n → ℚ := fun j => (p j : ℚ) / N.det
  have hw : (fun j => (w j : ℝ)) = x := by
    funext j
    dsimp [w, p]
    simp only [Rat.cast_div, Rat.cast_intCast]
    exact (cramer_real_representation N c x hd hs j).symm
  have hN : ∀ i j, |N i j| ≤ (2 : ℤ) ^ B := fun i j => hA (f i) j
  refine ⟨w, p, N.det, hd, CertificateBounds.det_binary_size N hN, ?_, fun _ => rfl, ?_⟩
  · intro j
    apply CertificateBounds.det_binary_size
    intro i k
    simp only [Matrix.updateCol_apply]
    split_ifs
    · exact hb (f i)
    · exact hN i k
  · rw [hw]
    exact hx

/-- Explicit coordinate boundedness is enough; compactness is derived from the
closed half-space description rather than supplied by an LP oracle. -/
theorem bounded_integer_polyhedron_certificate {B : ℕ}
    (A : Matrix I (Fin n) ℤ) (b : I → ℤ) (lo hi : Fin n → ℝ)
    (hA : ∀ i j, |A i j| ≤ (2 : ℤ) ^ B) (hb : ∀ i, |b i| ≤ (2 : ℤ) ^ B)
    (hbound : ∀ x ∈ polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)),
      ∀ j, lo j ≤ x j ∧ x j ≤ hi j)
    (hn : (polyhedron (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ))).Nonempty) :
    ∃ (w : Fin n → ℚ) (p : Fin n → ℤ) (q : ℤ), q ≠ 0 ∧
      q.natAbs.size ≤ n * (B + n) + 1 ∧
      (∀ j, (p j).natAbs.size ≤ n * (B + n) + 1) ∧
      (∀ j, w j = (p j : ℚ) / q) ∧
      (fun j => (w j : ℝ)) ∈ polyhedron
        (A.map (fun z : ℤ => (z : ℝ))) (fun i => (b i : ℝ)) := by
  exact small_integer_polyhedron_certificate A b hA hb
    (polyhedron_compact _ _ lo hi hbound) hn

end BalancedAssortments.PolyhedralBasis
