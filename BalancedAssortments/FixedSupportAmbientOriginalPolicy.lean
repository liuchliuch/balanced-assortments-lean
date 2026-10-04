import BalancedAssortments.FixedSupportAmbientComplete

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints
open FixedSupportAmbientPreprocess (AmbientResult runAmbient)

/-- The cached value returned by the actual ambient-input solver is exactly
the best revenue of any legal balanced original MNL policy having the supplied
nonempty support. Policy existence here is the mathematical interpretation of
the value solver; its execution clock is the ambient solver clock. -/
theorem runAmbient_original_policy {N K : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty)
    (data : Fin N→Product) (mask : Fin N→Bool) (r v : Fin N→ℚ) (α κ : Fraction)
    (hm : ∀ i,mask i=true ↔ i∈A) (hd : ∀ i,(data i).Valid)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) (hα : Valid α) (hκ : Valid κ)
    (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode κ) (hK : decode κ=(K:ℚ))
    (hdata : ∀ i,decode (data i).1=r i ∧ decode (data i).2=v i) :
    ∃ result : AmbientResult,(runAmbient α κ (List.ofFn data) (List.ofFn mask)).1=some result ∧
      ∃ m≤N+1,∃ (S : Fin m→Finset (Fin N)) (q : Fin m→ℝ),
        Sales.Distribution q ∧ (∀ a,(S a).card≤K) ∧
        Sales.Balanced (decode α:ℝ) (Sales.sales (fun i=>(v i:ℝ)) S q) ∧
        (∀ i,0<Sales.sales (fun i=>(v i:ℝ)) S q i ↔ i∈A) ∧
        Sales.revenue (fun i=>(r i:ℝ)) (Sales.sales (fun i=>(v i:ℝ)) S q)=(decode result.2.2:ℝ) ∧
        ∀ {J : Type} [Fintype J] (T : J→Finset (Fin N)) (p : J→ℝ),
          Sales.Distribution p → (∀ a,(T a).card≤K) →
          Sales.Balanced (decode α:ℝ) (Sales.sales (fun i=>(v i:ℝ)) T p) →
          (∀ i,0<Sales.sales (fun i=>(v i:ℝ)) T p i ↔ i∈A) →
          Sales.revenue (fun i=>(r i:ℝ)) (Sales.sales (fun i=>(v i:ℝ)) T p)≤(decode result.2.2:ℝ) := by
  obtain ⟨prepared,out,e,p,hout,hreal,hvalid,hobjvalid,hopt⟩:=
    runAmbient_correct A hA data mask r v α κ hm hd hr hv hα hκ hαpos hα1 hKpos hdata
  have hKR : (decode κ:ℝ)=(K:ℝ) := by exact_mod_cast hK
  rw [hKR] at hopt
  refine ⟨⟨prepared,out⟩,hout,?_⟩
  exact certified_original_policy A _ _ _ _ _ (fun i=>by exact_mod_cast hv i) hopt

end BalancedAssortments.FixedSupportAmbient
