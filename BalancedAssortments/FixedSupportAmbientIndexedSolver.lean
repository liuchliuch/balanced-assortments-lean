import BalancedAssortments.FixedSupportAmbientIndex

noncomputable section
namespace BalancedAssortments.FixedSupportAmbient
open ComplexityTimeFractions (decode Valid)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax FixedSupportCostProgram FixedSupportAlgorithm

/-- Zero extension along the exact enumeration returned by structural support
selection; its index size need not be rewritten to a cardinality in executable
code. -/
def extendIndexed {N n : ℕ} (A : Finset (Fin N)) (e : Fin n≃A) (w : Fin n→ℝ) (i : Fin N) : ℝ :=
  if hi : i∈A then w (e.symm ⟨i,hi⟩) else 0

theorem binary_indexed_ambient_solver {N n : ℕ} (A : Finset (Fin N)) (hA : A.Nonempty) (e : Fin n≃A)
    (r v : Fin N→ℚ) (ps : List (Fin n×Product)) (α K : Fraction)
    (hlabels : ps.map Prod.fst=List.finRange n) (hp : ∀ p∈ps,p.2.Valid)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) (hα : Valid α) (hK : Valid K)
    (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ p∈ps,decode p.2.1=r (e p.1) ∧ decode p.2.2=v (e p.1)) :
    ∃ out p,(runBits α K ps).1=some out ∧
      Realizes (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) out p ∧
      (∀ x∈out.1,Valid x.2) ∧ Valid out.2 ∧
      AmbientOptimal A (fun i=>(r i:ℝ)) (fun i=>(v i:ℝ))
        (extendIndexed A e (fun j=>(candidateVector (fun j=>r (e j)) (fun j=>v (e j)) (decode α) (decode K) p j:ℝ)))
        (decode α:ℝ) (decode K:ℝ) (decode out.2:ℝ) := by
  have hn : n=A.card := by simpa using Fintype.card_congr e
  subst n
  obtain ⟨out,p,he,hreal,hvalid,hov,hf,hactive,hobj,hopt,hcost⟩:=
    binary_ambient_solver A hA e r v ps α K hlabels hp hr hv hα hK hαpos hα1 hKpos hdata
  exact ⟨out,p,he,hreal,hvalid,hov,⟨hf,hactive,hobj,hopt⟩⟩

end BalancedAssortments.FixedSupportAmbient
