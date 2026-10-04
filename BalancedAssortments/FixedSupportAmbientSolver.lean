import BalancedAssortments.FixedSupportAmbient
import BalancedAssortments.FixedSupportCostInputSize

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open scoped BigOperators
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax FixedSupportCostProgram FixedSupportAlgorithm
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The same actual binary solver solves every nonempty prescribed ambient
support. Products outside the support are zero-extended exactly; objective and
all-real optimality are preserved under the supplied finite indexing. -/
theorem binary_ambient_solver (A : Finset I) (hA : A.Nonempty) (e : Fin A.card≃A)
    (r v : I→ℚ) (ps : List (Fin A.card×Product)) (α K : Fraction)
    (hlabels : ps.map Prod.fst=List.finRange A.card) (hp : ∀ p∈ps,p.2.Valid)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) (hα : Valid α) (hK : Valid K)
    (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ p∈ps,decode p.2.1=r (e p.1) ∧ decode p.2.2=v (e p.1)) :
    ∃ out p, (runBits α K ps).1=some out ∧
      Realizes (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) out p ∧
      (∀ x∈out.1,Valid x.2) ∧ Valid out.2 ∧
      let w := extend A e (fun j=>(candidateVector (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) p j:ℝ))
      Optimization.feasible (fun i=>(v i:ℝ)) (decode α:ℝ) (decode K:ℝ) w ∧
      (∀ i,0<w i ↔ i∈A) ∧ Optimization.revenue (fun i=>(r i:ℝ)) w=(decode out.2:ℝ) ∧
      (∀ u,Optimization.feasible (fun i=>(v i:ℝ)) (decode α:ℝ) (decode K:ℝ) u →
        (∀ i,u i≠0 ↔ i∈A) → Optimization.revenue (fun i=>(r i:ℝ)) u≤(decode out.2:ℝ)) ∧
      (runBits α K ps).2≤runCost A.card (inputVolume α K ps) := by
  obtain ⟨out,p,he,hreal,hvalid,hov,hpos,hf,hopt⟩:=runBits_exact_support (Finset.card_pos.mpr hA)
    (fun j=>r (e j)) (fun j=>v (e j)) ps α K hlabels hp (fun j=>hr (e j)) (fun j=>hv (e j))
    hα hK hαpos hα1 hKpos hdata
  refine ⟨out,p,he,hreal,hvalid,hov,?_,?_,?_,?_,?_⟩
  · exact feasible_extend A e _ _ _ (fun i=>by exact_mod_cast (hv i).le) _ hf
  · apply support_extend
    intro j;exact_mod_cast hpos j
  · rw [objective_extend,realRevenue_cast,←hreal.2]
  · intro u hu hs
    have hz : ∀ i∉A,u i=0 := by intro i hi;simpa using mt (hs i).mp hi
    rw [objective_restrict A e _ u hz]
    exact hopt _ (restrict_feasible A e _ u _ _ hu hs)
  · have hh:=runBits_input_cost α K ps hα hK hp
    have hl : ps.length=A.card := by have h:=congrArg List.length hlabels;simpa using h
    simpa only [hl] using hh

end BalancedAssortments.FixedSupportAmbient
