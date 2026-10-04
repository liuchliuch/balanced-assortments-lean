import BalancedAssortments.FixedSupportAmbientPolicy
import BalancedAssortments.FixedSupportCostSerializedInput

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open scoped BigOperators
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax FixedSupportCostProgram FixedSupportAlgorithm

/-- Exact source-model meaning of an ambient prescribed-support result. -/
def AmbientOptimal {N : ℕ} (A : Finset (Fin N)) (r v w : Fin N→ℝ) (α K R : ℝ) : Prop :=
  Optimization.feasible v α K w ∧ (∀ i,0<w i ↔ i∈A) ∧ Optimization.revenue r w=R ∧
  ∀ u,Optimization.feasible v α K u → (∀ i,u i≠0 ↔ i∈A) → Optimization.revenue r u≤R

/-- One uniform polynomial bounds the unchanged actual raw binary solver on
every nonempty prescribed support of every finite ambient catalog. Runtime is
measured in the exact serialized selected-catalog input, with no free width
parameter. The output has an explicit ambient zero-extension interpretation. -/
theorem binary_prescribed_support_polynomial : ∃ P : Polynomial ℕ,∀ {N : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty) (e : Fin A.card≃A)
    (r v : Fin N→ℚ) (ps : List (Fin A.card×Product)) (α K : Fraction),
    ps.map Prod.fst=List.finRange A.card → (∀ p∈ps,p.2.Valid) →
    (∀ i,0<r i) → (∀ i,0<v i) → Valid α → Valid K →
    0<decode α → decode α≤1 → 0<decode K →
    (∀ p∈ps,decode p.2.1=r (e p.1) ∧ decode p.2.2=v (e p.1)) →
    ∃ out p,(runBits α K ps).1=some out ∧
      Realizes (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) out p ∧
      (∀ x∈out.1,Valid x.2) ∧ Valid out.2 ∧
      AmbientOptimal A (fun i=>(r i:ℝ)) (fun i=>(v i:ℝ))
        (extend A e (fun j=>(candidateVector (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) p j:ℝ)))
        (decode α:ℝ) (decode K:ℝ) (decode out.2:ℝ) ∧
      (runBits α K ps).2≤P.eval (serializedInput α K ps).length := by
  obtain ⟨P,hP⟩:=runBits_polynomial_serialized
  refine ⟨P,?_⟩
  intro N A hA e r v ps α K hl hp hr hv hα hK ha ha1 hk hd
  obtain ⟨out,p,he,hreal,hvalid,hov,hf,hactive,hobj,hopt,hcost⟩:=
    binary_ambient_solver A hA e r v ps α K hl hp hr hv hα hK ha ha1 hk hd
  exact ⟨out,p,he,hreal,hvalid,hov,⟨hf,hactive,hobj,hopt⟩,hP α K ps hα hK hp⟩

/-- For integral assortment capacity, every certified compact optimum above
has the original randomized-policy interpretation without changing its value. -/
theorem certified_original_policy {N K : ℕ} (A : Finset (Fin N)) (r v w : Fin N→ℝ) (α R : ℝ)
    (hv : ∀ i,0<v i) (h : AmbientOptimal A r v w α (K:ℝ) R) :
    ∃ m≤N+1,∃ (S : Fin m→Finset (Fin N)) (q : Fin m→ℝ),
      Sales.Distribution q ∧ (∀ a,(S a).card≤K) ∧ Sales.Balanced α (Sales.sales v S q) ∧
      (∀ i,0<Sales.sales v S q i ↔ i∈A) ∧ Sales.revenue r (Sales.sales v S q)=R ∧
      ∀ {J : Type} [Fintype J] (T : J→Finset (Fin N)) (p : J→ℝ),
        Sales.Distribution p → (∀ a,(T a).card≤K) → Sales.Balanced α (Sales.sales v T p) →
        (∀ i,0<Sales.sales v T p i ↔ i∈A) → Sales.revenue r (Sales.sales v T p)≤R := by
  obtain ⟨m,hm,S,q,hq,hK,hs,hb,ha,hr,ho⟩:=optimal_original_policy A r v w α hv h.1 h.2.1
    (by intro u hu hs;rw [h.2.2.1];exact h.2.2.2 u hu hs)
  refine ⟨m,hm,S,q,hq,hK,hb,ha,hr.trans h.2.2.1,?_⟩
  intro J inst T p hp hcap hbal hsup
  exact (ho T p hp hcap hbal hsup).trans_eq (hr.trans h.2.2.1)

end BalancedAssortments.FixedSupportAmbient
