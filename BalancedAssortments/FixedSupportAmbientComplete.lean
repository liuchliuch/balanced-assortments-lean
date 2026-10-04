import BalancedAssortments.FixedSupportAmbientProgram
import BalancedAssortments.FixedSupportAmbientSelection

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax FixedSupportCostProgram FixedSupportAlgorithm
open FixedSupportAmbientPreprocess (Prepared runAmbient)

/-- Exact source correctness of actual ambient-mask preprocessing followed by
the binary optimizer. The support mask is read structurally; its finite-set
meaning is proved, rather than supplied as a runtime membership oracle. -/
theorem runAmbient_correct {N : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (data : Fin N→Product) (mask : Fin N→Bool) (r v : Fin N→ℚ) (α K : Fraction)
    (hm : ∀ i,mask i=true ↔ i∈A) (hd : ∀ i,(data i).Valid)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) (hα : Valid α) (hK : Valid K)
    (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ i,decode (data i).1=r i ∧ decode (data i).2=v i) :
    ∃ prepared : Prepared,∃ out,∃ e : Fin prepared.products.length≃A,∃ p,
      (runAmbient α K (List.ofFn data) (List.ofFn mask)).1=some ⟨prepared,out⟩ ∧
      Realizes (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) out p ∧
      (∀ x∈out.1,Valid x.2) ∧ Valid out.2 ∧
      AmbientOptimal A (fun i=>(r i:ℝ)) (fun i=>(v i:ℝ))
        (extendIndexed A e (fun j=>(candidateVector (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) p j:ℝ)))
        (decode α:ℝ) (decode K:ℝ) (decode out.2:ℝ) := by
  obtain ⟨prepared,hprep⟩:=prepare_ofFn data mask
  obtain ⟨e,he⟩:=prepared_restriction data mask A hm prepared hprep
  have hc:=FixedSupportAmbientPreprocess.prepare_correct hprep
  have hvalid:=prepared_valid data mask prepared hprep hd
  have hdata' : ∀ p∈prepared.indexed,decode p.2.1=r (e p.1) ∧ decode p.2.2=v (e p.1) := by
    intro p hp
    rw [he p hp]
    exact hdata (e p.1)
  obtain ⟨out,p,hout,hreal,houtvalid,hobjvalid,hoptimal⟩:=binary_indexed_ambient_solver A hA e r v prepared.indexed α K
    hc.2.2.2.2.1 hvalid hr hv hα hK hαpos hα1 hKpos hdata'
  have hn : prepared.products.length=A.card := by simpa using Fintype.card_congr e
  have hne : prepared.products≠[] := by
    intro hz
    have hpos:=Finset.card_pos.mpr hA
    simp [hz] at hn
    omega
  exact ⟨prepared,out,e,p,FixedSupportAmbientPreprocess.runAmbient_returns α K _ _ prepared out hprep hne hout,
    hreal,houtvalid,hobjvalid,hoptimal⟩

/-- One uniform polynomial covers both the actual ambient-mask preprocessing
and the actual binary exact-support solver, measured in the original ambient
input (including unselected products and the explicit support mask). -/
theorem ambient_prescribed_support_polynomial : ∃ P : Polynomial ℕ,∀ {N : ℕ}
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
        P.eval (FixedSupportAmbientPreprocess.ambientVolume α K (List.ofFn data) (List.ofFn mask)) := by
  obtain ⟨P,hP⟩:=FixedSupportAmbientPreprocess.runAmbient_polynomial
  refine ⟨P,?_⟩
  intro N A hA data mask r v α K hm hd hr hv hα hK ha ha1 hk hdata
  refine ⟨runAmbient_correct A hA data mask r v α K hm hd hr hv hα hK ha ha1 hk hdata,?_⟩
  exact hP α K _ _ hα hK (by intro p hp;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hp;exact hd i)

end BalancedAssortments.FixedSupportAmbient
