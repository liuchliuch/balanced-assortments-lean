import BalancedAssortments.FixedSupportAmbientOriginalPolicy
import BalancedAssortments.FixedSupportAmbientSerialized

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax FixedSupportCostProgram FixedSupportAlgorithm
open FixedSupportAmbientPreprocess (Prepared runAmbient)

/-- One uniform polynomial covers both the actual ambient-mask preprocessing
and the actual binary exact-support solver, measured in the original ambient
self-delimiting serialized input (including unselected products and the explicit support mask). -/
theorem ambient_prescribed_support_serialized : ∃ P : Polynomial ℕ,∀ {N : ℕ}
    (A : Finset (Fin N)) (hA : A.Nonempty)
    (data : Fin N→Product) (mask : Fin N→Bool) (r v : Fin N→ℚ) (α K : Fraction),
    (∀ i,mask i=true ↔ i∈A) → (∀ i,(data i).Valid) →
    (∀ i,0<r i) → (∀ i,0<v i) → Valid α → Valid K →
    0<decode α → decode α≤1 → 0<decode K →
    (∀ i,decode (data i).1=r i ∧ decode (data i).2=v i) →
    (∃ prepared : Prepared,∃ out,∃ e : Fin prepared.products.length≃A,∃ p,
      (runAmbient α K (List.ofFn data) (List.ofFn mask)).1=some ⟨prepared,out⟩ ∧
      Realizes (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) out p ∧
      (∀ x∈out.1,Valid x.2) ∧ Valid out.2 ∧
      AmbientOptimal A (fun i=>(r i:ℝ)) (fun i=>(v i:ℝ))
        (extendIndexed A e (fun j=>(candidateVector (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) p j:ℝ)))
        (decode α:ℝ) (decode K:ℝ) (decode out.2:ℝ)) ∧
      (runAmbient α K (List.ofFn data) (List.ofFn mask)).2≤
        P.eval (FixedSupportAmbientPreprocess.serializedAmbient α K (List.ofFn data) (List.ofFn mask)).length := by
  obtain ⟨P,hP⟩:=FixedSupportAmbientPreprocess.runAmbient_polynomial_serialized
  refine ⟨P,?_⟩
  intro N A hA data mask r v α K hm hd hr hv hα hK ha ha1 hk hdata
  refine ⟨runAmbient_correct A hA data mask r v α K hm hd hr hv hα hK ha ha1 hk hdata,?_⟩
  exact hP α K _ _ hα hK (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp;exact hd i)


end BalancedAssortments.FixedSupportAmbient
