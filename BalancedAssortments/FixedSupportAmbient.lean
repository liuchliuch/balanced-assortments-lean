import BalancedAssortments.FixedSupportCostCertified
import BalancedAssortments.SalesIntegration

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The prescribed support is supplied explicitly; its indexing is independent
of the optimizer and of the values of the input coefficients. -/
def extend {R : Type*} [Zero R] (A : Finset I) (e : Fin A.card≃A) (w : Fin A.card→R) (i : I) : R :=
  if hi : i∈A then w (e.symm ⟨i,hi⟩) else 0

@[simp] lemma extend_at {R : Type*} [Zero R] (A : Finset I) (e : Fin A.card≃A) (w : Fin A.card→R) (j : Fin A.card) :
    extend A e w (e j)=w j := by simp [extend,(e j).property]
@[simp] lemma extend_off {R : Type*} [Zero R] (A : Finset I) (e : Fin A.card≃A) (w : Fin A.card→R) {i : I} (hi : i∉A) :
    extend A e w i=0 := by simp [extend,hi]

lemma sum_supported {R : Type*} [AddCommMonoid R] (A : Finset I) (e : Fin A.card≃A)
    (f : I→R) (hz : ∀ i∉A,f i=0) : ∑ i,f i=∑ j,f (e j) := by
  calc
    _ = ∑ i∈A,f i := (Finset.sum_subset (Finset.subset_univ A) (by intro i hi hni;exact hz i hni)).symm
    _ = ∑ i:A,f i := Finset.sum_subtype A (fun _=>Iff.rfl) f
    _ = _ := (e.sum_comp (fun i:A=>f i)).symm

lemma sum_extend {R : Type*} [AddCommMonoid R] (A : Finset I) (e : Fin A.card≃A) (w : Fin A.card→R) :
    ∑ i,extend A e w i=∑ j,w j := by
  rw [sum_supported A e _ (fun i hi=>extend_off A e w hi)]
  simp

lemma rank_extend (A : Finset I) (e : Fin A.card≃A) (v : I→ℝ) (w : Fin A.card→ℝ) :
    ∑ i,extend A e w i/v i=∑ j,w j/v (e j) := by
  rw [sum_supported A e _ (by intro i hi;simp [hi])]
  simp

lemma objective_extend (A : Finset I) (e : Fin A.card≃A) (r : I→ℝ) (w : Fin A.card→ℝ) :
    Optimization.revenue r (extend A e w)=FixedSupportReal.revenue (fun j=>r (e j)) w := by
  unfold Optimization.revenue FixedSupportReal.revenue
  rw [sum_extend,sum_supported A e (fun i=>r i*extend A e w i) (by intro i hi;simp [hi])]
  simp

lemma feasible_extend (A : Finset I) (e : Fin A.card≃A) (v : I→ℝ) (α K : ℝ)
    (hv : ∀ i,0≤v i) (w : Fin A.card→ℝ)
    (h : FixedSupportReal.Feasible (fun j=>v (e j)) α K w) : Optimization.feasible v α K (extend A e w) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases hi : i∈A
    · simpa [extend,hi] using h.1 (e.symm ⟨i,hi⟩)
    · simp [extend,hi,hv i]
  · simpa only [rank_extend] using h.2.1
  · intro i
    by_cases hi : i∈A
    · right;intro j
      by_cases hj : j∈A
      · simpa [extend,hi,hj] using h.2.2 (e.symm ⟨i,hi⟩) (e.symm ⟨j,hj⟩)
      · simpa [extend,hi,hj] using (h.1 (e.symm ⟨i,hi⟩)).1
    · exact Or.inl (extend_off A e w hi)

lemma support_extend (A : Finset I) (e : Fin A.card≃A) (w : Fin A.card→ℝ)
    (hw : ∀ j,0<w j) (i : I) : 0<extend A e w i ↔ i∈A := by
  by_cases hi : i∈A <;> simp [extend,hi,hw]

lemma restrict_feasible (A : Finset I) (e : Fin A.card≃A) (v w : I→ℝ) (α K : ℝ)
    (h : Optimization.feasible v α K w) (hs : ∀ i,w i≠0 ↔ i∈A) :
    FixedSupportReal.Feasible (fun j=>v (e j)) α K (fun j=>w (e j)) := by
  refine ⟨fun j=>h.1 (e j),?_,?_⟩
  · rw [←sum_supported A e (fun i=>w i/v i) (by
      intro i hi
      have hz : w i=0 := by simpa using mt (hs i).mp hi
      simp [hz])]
    exact h.2.1
  · intro i j
    rcases h.2.2 (e i) with hz|hb
    · exact False.elim (((hs (e i)).mpr (e i).property) hz)
    · exact hb (e j)

lemma objective_restrict (A : Finset I) (e : Fin A.card≃A) (r w : I→ℝ)
    (hz : ∀ i∉A,w i=0) :
    Optimization.revenue r w=FixedSupportReal.revenue (fun j=>r (e j)) (fun j=>w (e j)) := by
  unfold Optimization.revenue FixedSupportReal.revenue
  rw [sum_supported A e w hz,sum_supported A e (fun i=>r i*w i) (by intro i hi;simp [hz i hi])]

/-- Any exact solver for the indexed active coordinates is an exact solver for
an arbitrary prescribed ambient support, with zero extension outside it. -/
theorem transfer_optimum (A : Finset I) (e : Fin A.card≃A) (r v : I→ℝ) (α K : ℝ)
    (hv : ∀ i,0≤v i) (w : Fin A.card→ℝ)
    (hf : FixedSupportReal.Feasible (fun j=>v (e j)) α K w) (hp : ∀ j,0<w j)
    (ho : ∀ u,FixedSupportReal.Feasible (fun j=>v (e j)) α K u →
      FixedSupportReal.revenue (fun j=>r (e j)) u≤FixedSupportReal.revenue (fun j=>r (e j)) w) :
    Optimization.feasible v α K (extend A e w) ∧
    (∀ i,0<extend A e w i ↔ i∈A) ∧
    ∀ u,Optimization.feasible v α K u → (∀ i,u i≠0 ↔ i∈A) →
      Optimization.revenue r u≤Optimization.revenue r (extend A e w) := by
  refine ⟨feasible_extend A e v α K hv w hf,support_extend A e w hp,?_⟩
  intro u hu hsupport
  have hz : ∀ i∉A,u i=0 := by intro i hi;simpa using mt (hsupport i).mp hi
  rw [objective_restrict A e r u hz,objective_extend]
  exact ho _ (restrict_feasible A e v u α K hu hsupport)

end BalancedAssortments.FixedSupportAmbient
