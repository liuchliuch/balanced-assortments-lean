import BalancedAssortments.Sales
import BalancedAssortments.Optimization
import BalancedAssortments.RealDecomposition
import BalancedAssortments.DecompositionGreedy

/-! Adapters between the independently formalized optimization, rational
certificate, and real finite-policy modules. -/
noncomputable section
namespace BalancedAssortments.Sales
open scoped BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem optimization_feasible_iff (v w : I → ℝ) (α : ℝ) (K : ℕ) :
    Optimization.feasible v α (K : ℝ) w ↔ CompactFeasible v w K ∧ Balanced α w := by
  simp only [Optimization.feasible, CompactFeasible, Optimization.balanced, Balanced]
  tauto

theorem optimization_revenue_eq (r w : I → ℝ) :
    Optimization.revenue r w = objective r w := rfl

def certificateSets {n : ℕ} (p : List (Decomposition.Atom n))
    (a : Fin p.length) : Finset (Fin n) := (p[a.val]).2

def certificateWeights {n : ℕ} (p : List (Decomposition.Atom n))
    (a : Fin p.length) : ℝ := ((p[a.val]).1 : ℝ)

theorem certificate_distribution {n K : ℕ} {z : Fin n → ℚ}
    {p : List (Decomposition.Atom n)} (hp : Decomposition.ValidDecomposition K z p) :
    Distribution (certificateWeights p) := by
  constructor
  · intro a
    unfold certificateWeights
    exact_mod_cast hp.1 _ (List.getElem_mem a.isLt)
  · unfold certificateWeights
    rw [← Rat.cast_sum]
    rw [Fin.sum_univ_fun_getElem]
    exact_mod_cast hp.2.1

theorem certificate_marginal {n K : ℕ} {z : Fin n → ℚ}
    {p : List (Decomposition.Atom n)} (hp : Decomposition.ValidDecomposition K z p)
    (i : Fin n) : marginal (certificateSets p) (certificateWeights p) i = (z i : ℝ) := by
  unfold marginal certificateSets certificateWeights
  have heq : (∑ a : Fin p.length, if i ∈ (p[a.val]).2 then ((p[a.val]).1 : ℝ) else 0) =
      ((∑ a : Fin p.length, if i ∈ (p[a.val]).2 then (p[a.val]).1 else 0 : ℚ) : ℝ) := by
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp
  rw [heq, Fin.sum_univ_fun_getElem p (fun a => if i ∈ a.2 then a.1 else 0)]
  exact_mod_cast hp.2.2.2 i

/-- Every checked rational decomposition yields an actual real MNL policy.
The finite atom index has exactly the certificate's length, so support bounds
on the certificate pass directly to the implementation. -/
theorem implement_rational_certificate {n K : ℕ} (v : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) {z : Fin n → ℚ} {p : List (Decomposition.Atom n)}
    (hp : Decomposition.ValidDecomposition K z p) :
    ∃ q : Fin p.length → ℝ, Distribution q ∧
      (∀ a, q a ≠ 0 → (certificateSets p a).card ≤ K) ∧
      sales v (certificateSets p) q = compactSales (fun i => v i * (z i : ℝ)) := by
  let pp := certificateWeights p
  have hpp : Distribution pp := certificate_distribution hp
  refine ⟨reverseTilt v (certificateSets p) pp,
    reverse_distribution v (fun i => (hv i).le) (certificateSets p) hpp, ?_, ?_⟩
  · intro a ha
    have hpa := (reverse_support v (fun i => (hv i).le) (certificateSets p) hpp a).1 ha
    apply hp.2.2.1 _ (List.getElem_mem a.isLt)
    intro hz
    apply hpa
    simp [pp, certificateWeights, hz]
  · funext i
    rw [reverse_sales v (fun i => (hv i).le)]
    have heq : (fun i => v i * marginal (certificateSets p) pp i) =
        (fun i => v i * (z i : ℝ)) := by
      funext j
      rw [certificate_marginal hp j]
    rw [heq]


/-- Unconditional rational compact-to-policy implementation with at most n+1
atoms, obtained by the proved greedy uniform-matroid decomposition. -/
theorem rational_compact_implementation {n K : ℕ} (v w : Fin n → ℚ)
    (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 ≤ w i ∧ w i ≤ v i)
    (hr : ∑ i, w i / v i ≤ (K : ℚ)) :
    ∃ (p : List (Decomposition.Atom n)) (q : Fin p.length → ℝ),
      p.length ≤ n + 1 ∧ Distribution q ∧
      (∀ a, q a ≠ 0 → (certificateSets p a).card ≤ K) ∧
      sales (fun i => (v i : ℝ)) (certificateSets p) q =
        compactSales (fun i => (w i : ℝ)) := by
  have hz : Decomposition.Feasible K (fun i => w i / v i) := by
    refine ⟨?_, hr⟩
    intro i
    exact ⟨div_nonneg (hc i).1 (hv i).le, (div_le_one (hv i)).2 (hc i).2⟩
  obtain ⟨p, hp, hlen⟩ := Decomposition.exists_linear_decomposition hz
  have hvr : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  obtain ⟨q, hq, hlegal, hs⟩ := implement_rational_certificate (fun i => (v i : ℝ)) hvr hp
  refine ⟨p, q, hlen, hq, hlegal, ?_⟩
  have heq : (fun i => (v i : ℝ) * ((w i / v i : ℚ) : ℝ)) =
      (fun i => (w i : ℝ)) := by
    funext i
    push_cast
    field_simp [(hvr i).ne']
  rw [heq] at hs
  exact hs


def realCertificateSets {n : ℕ} (p : List (RealDecomposition.Atom n))
    (a : Fin p.length) : Finset (Fin n) := (p[a.val]).2

def realCertificateWeights {n : ℕ} (p : List (RealDecomposition.Atom n))
    (a : Fin p.length) : ℝ := (p[a.val]).1

theorem real_certificate_distribution {n K : ℕ} {z : Fin n → ℝ}
    {p : List (RealDecomposition.Atom n)} (hp : RealDecomposition.ValidDecomposition K z p) :
    Distribution (realCertificateWeights p) := by
  constructor
  · intro a
    exact hp.1 _ (List.getElem_mem a.isLt)
  · unfold realCertificateWeights
    rw [Fin.sum_univ_fun_getElem]
    exact hp.2.1

theorem real_certificate_marginal {n K : ℕ} {z : Fin n → ℝ}
    {p : List (RealDecomposition.Atom n)} (hp : RealDecomposition.ValidDecomposition K z p)
    (i : Fin n) : marginal (realCertificateSets p) (realCertificateWeights p) i = z i := by
  unfold marginal realCertificateSets realCertificateWeights
  rw [Fin.sum_univ_fun_getElem p (fun a => if i ∈ a.2 then a.1 else 0)]
  exact hp.2.2.2 i

/-- Unconditional real compact-to-policy implementation, with n+1 atoms.
No marginal completeness hypothesis remains in this theorem. -/
theorem real_compact_implementation {n K : ℕ} (v w : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (hw : CompactFeasible v w K) :
    ∃ (p : List (RealDecomposition.Atom n)) (q : Fin p.length → ℝ),
      p.length ≤ n + 1 ∧ Distribution q ∧
      (∀ a, q a ≠ 0 → (realCertificateSets p a).card ≤ K) ∧
      sales v (realCertificateSets p) q = compactSales w := by
  have hz : RealDecomposition.Feasible K (fun i => w i / v i) := by
    refine ⟨?_, hw.2⟩
    intro i
    exact ⟨div_nonneg (hw.1 i).1 (hv i).le, (div_le_one (hv i)).2 (hw.1 i).2⟩
  obtain ⟨p, hp, hlen⟩ := RealDecomposition.exists_linear_decomposition hz
  let pp := realCertificateWeights p
  have hpp : Distribution pp := real_certificate_distribution hp
  refine ⟨p, reverseTilt v (realCertificateSets p) pp, hlen,
    reverse_distribution v (fun i => (hv i).le) (realCertificateSets p) hpp, ?_, ?_⟩
  · intro a ha
    have hpa := (reverse_support v (fun i => (hv i).le) (realCertificateSets p) hpp a).1 ha
    exact hp.2.2.1 _ (List.getElem_mem a.isLt) hpa
  · funext i
    rw [reverse_sales v (fun i => (hv i).le)]
    have heq : (fun i => v i * marginal (realCertificateSets p) pp i) = w := by
      funext j
      rw [real_certificate_marginal hp j]
      field_simp [(hv j).ne']
    rw [heq]


/-- Replace zero-probability displays by the empty assortment, obtaining a
policy whose every indexed display is legal (including unused atoms). -/
theorem compact_sparse_policy {n K : ℕ} (v w : Fin n → ℝ)
    (hv : ∀ i, 0 < v i) (hw : CompactFeasible v w K) :
    ∃ m ≤ n + 1, ∃ (S : Fin m → Finset (Fin n)) (q : Fin m → ℝ),
      Distribution q ∧ (∀ a, (S a).card ≤ K) ∧ sales v S q = compactSales w := by
  classical
  obtain ⟨p, q, hlen, hq, hlegal, hs⟩ := real_compact_implementation v w hv hw
  let S : Fin p.length → Finset (Fin n) := fun a =>
    if q a = 0 then ∅ else realCertificateSets p a
  refine ⟨p.length, hlen, S, q, hq, ?_, ?_⟩
  · intro a
    dsimp [S]
    split_ifs with ha
    · simp
    · exact hlegal a ha
  · rw [← hs]
    funext i
    unfold sales
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : q a = 0
    · simp [S, ha]
    · simp [S, ha, denominator]

/-- Feasibility, exact balance, and revenue of the compact optimization model
all transfer to a legal policy with at most n+1 displayed assortments. -/
theorem optimization_sparse_policy {n K : ℕ} (v r w : Fin n → ℝ) (α : ℝ)
    (hv : ∀ i, 0 < v i) (hw : Optimization.feasible v α (K : ℝ) w) :
    ∃ m ≤ n + 1, ∃ (S : Fin m → Finset (Fin n)) (q : Fin m → ℝ),
      Distribution q ∧ (∀ a, (S a).card ≤ K) ∧
      Balanced α (sales v S q) ∧ revenue r (sales v S q) = Optimization.revenue r w := by
  have h := (optimization_feasible_iff v w α K).1 hw
  obtain ⟨m, hm, S, q, hq, hK, hs⟩ := compact_sparse_policy v w hv h.1
  refine ⟨m, hm, S, q, hq, hK, ?_, ?_⟩
  · rw [hs]
    exact (compact_balance α w (fun i => (h.1.1 i).1)).2 h.2
  · rw [hs, compact_revenue]
    rfl


/-- Explicit rational reverse-tilt weights. -/
def rationalPolicy {n : ℕ} (v z : Fin n → ℚ) (p : List (Decomposition.Atom n))
    (a : Fin p.length) : ℚ :=
  (p[a.val]).1 * (1 + ∑ i ∈ (p[a.val]).2, v i) / (1 + ∑ i, v i * z i)

theorem rationalPolicy_cast {n K : ℕ} (v : Fin n → ℚ) {z : Fin n → ℚ}
    {p : List (Decomposition.Atom n)} (hp : Decomposition.ValidDecomposition K z p) :
    (fun a => (rationalPolicy v z p a : ℝ)) =
      reverseTilt (fun i => (v i : ℝ)) (certificateSets p) (certificateWeights p) := by
  funext a
  unfold rationalPolicy reverseTilt
  simp only [certificate_marginal hp, certificateWeights, denominator, certificateSets]
  push_cast
  rfl

/-- Rational compact input has an implementation with genuinely rational
weights, rather than merely a real-valued existence witness. -/
theorem rational_sparse_policy {n K : ℕ} (v w : Fin n → ℚ)
    (hv : ∀ i, 0 < v i) (hc : ∀ i, 0 ≤ w i ∧ w i ≤ v i)
    (hr : ∑ i, w i / v i ≤ (K : ℚ)) :
    ∃ (p : List (Decomposition.Atom n)) (q : Fin p.length → ℚ),
      p.length ≤ n + 1 ∧ Distribution (fun a => (q a : ℝ)) ∧
      (∀ a, q a ≠ 0 → (certificateSets p a).card ≤ K) ∧
      sales (fun i => (v i : ℝ)) (certificateSets p) (fun a => (q a : ℝ)) =
        compactSales (fun i => (w i : ℝ)) := by
  have hz : Decomposition.Feasible K (fun i => w i / v i) := by
    refine ⟨?_, hr⟩
    intro i
    exact ⟨div_nonneg (hc i).1 (hv i).le, (div_le_one (hv i)).2 (hc i).2⟩
  obtain ⟨p, hp, hlen⟩ := Decomposition.exists_linear_decomposition hz
  have hvr : ∀ i, (0 : ℝ) < (v i : ℝ) := fun i => by exact_mod_cast hv i
  have hpp := certificate_distribution hp
  refine ⟨p, rationalPolicy v (fun i => w i / v i) p, hlen, ?_, ?_, ?_⟩
  · rw [rationalPolicy_cast v hp]
    exact reverse_distribution _ (fun i => (hvr i).le) _ hpp
  · intro a ha
    apply hp.2.2.1 _ (List.getElem_mem a.isLt)
    intro he
    apply ha
    simp [rationalPolicy, he]
  · rw [rationalPolicy_cast v hp]
    funext i
    rw [reverse_sales _ (fun i => (hvr i).le)]
    have heq : (fun j => (v j : ℝ) * marginal (certificateSets p) (certificateWeights p) j) =
        (fun j => (w j : ℝ)) := by
      funext j
      rw [certificate_marginal hp j]
      push_cast
      field_simp [(hvr j).ne']
    rw [heq]


/-- The full real attainable-sales equivalence, with no decomposition oracle
or completeness assumption. The reverse implication even has n+1 atoms. -/
theorem exact_attainable {n K : ℕ} (v x : Fin n → ℝ) (hv : ∀ i, 0 < v i) :
    (∃ m, ∃ (S : Fin m → Finset (Fin n)) (q : Fin m → ℝ),
      Distribution q ∧ (∀ a, (S a).card ≤ K) ∧ sales v S q = x) ↔
    ∃ w, CompactFeasible v w K ∧ compactSales w = x := by
  constructor
  · rintro ⟨m, S, q, hq, hK, hx⟩
    obtain ⟨w, hw, hs⟩ := policy_to_compact v hv S hq K hK
    exact ⟨w, hw, hs.symm.trans hx⟩
  · rintro ⟨w, hw, hx⟩
    obtain ⟨m, _, S, q, hq, hK, hs⟩ := compact_sparse_policy v w hv hw
    exact ⟨m, S, q, hq, hK, hs.trans hx⟩

end BalancedAssortments.Sales
