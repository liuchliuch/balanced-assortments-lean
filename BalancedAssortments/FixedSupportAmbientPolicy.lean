import BalancedAssortments.FixedSupportAmbientSolver

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open scoped BigOperators

/-- An ambient exact-support compact optimum has an actual legal randomized
MNL implementation, with the same support and objective, dominating every
finite original policy on that prescribed support. -/
theorem optimal_original_policy {N K : ℕ} (A : Finset (Fin N)) (r v w : Fin N→ℝ) (α : ℝ)
    (hv : ∀ i,0<v i) (hw : Optimization.feasible v α (K:ℝ) w)
    (hactive : ∀ i,0<w i ↔ i∈A)
    (hopt : ∀ u,Optimization.feasible v α (K:ℝ) u → (∀ i,u i≠0 ↔ i∈A) →
      Optimization.revenue r u≤Optimization.revenue r w) :
    ∃ m≤N+1,∃ (S : Fin m→Finset (Fin N)) (q : Fin m→ℝ),
      Sales.Distribution q ∧ (∀ a,(S a).card≤K) ∧
      Sales.sales v S q=Sales.compactSales w ∧
      Sales.Balanced α (Sales.sales v S q) ∧
      (∀ i,0<Sales.sales v S q i ↔ i∈A) ∧
      Sales.revenue r (Sales.sales v S q)=Optimization.revenue r w ∧
      ∀ {J : Type} [Fintype J] (T : J→Finset (Fin N)) (p : J→ℝ),
        Sales.Distribution p → (∀ a,(T a).card≤K) → Sales.Balanced α (Sales.sales v T p) →
        (∀ i,0<Sales.sales v T p i ↔ i∈A) →
        Sales.revenue r (Sales.sales v T p)≤Sales.revenue r (Sales.sales v S q) := by
  have hc := (Sales.optimization_feasible_iff v w α K).mp hw
  obtain ⟨m,hm,S,q,hq,hK,hs⟩:=Sales.compact_sparse_policy v w hv hc.1
  refine ⟨m,hm,S,q,hq,hK,hs,?_,?_,?_,?_⟩
  · rw [hs];exact (Sales.compact_balance α w (fun i=>(hc.1.1 i).1)).mpr hc.2
  · intro i;rw [hs];exact (Sales.compact_support w (fun i=>(hc.1.1 i).1) i).trans (hactive i)
  · rw [hs,Sales.compact_revenue];rfl
  · intro J inst T p hp hcap hbal hsup
    obtain ⟨u,hu,he⟩:=Sales.policy_to_compact v hv T hp K hcap
    have hub : Sales.Balanced α u := by
      apply (Sales.compact_balance α u (fun i=>(hu.1 i).1)).mp
      rw [←he];exact hbal
    have huf := (Sales.optimization_feasible_iff v u α K).mpr ⟨hu,hub⟩
    have hupos : ∀ i,0<u i ↔ i∈A := by
      intro i
      exact (Sales.compact_support u (fun j=>(hu.1 j).1) i).symm.trans (by simpa only [he] using hsup i)
    have hun : ∀ i,u i≠0 ↔ i∈A := by
      intro i
      constructor
      · intro hi
        exact (hupos i).mp (lt_of_le_of_ne (hu.1 i).1 (Ne.symm hi))
      · intro hi
        exact (hupos i).mpr hi |>.ne'
    rw [he,hs,Sales.compact_revenue,Sales.compact_revenue]
    exact hopt u huf hun

end BalancedAssortments.FixedSupportAmbient
