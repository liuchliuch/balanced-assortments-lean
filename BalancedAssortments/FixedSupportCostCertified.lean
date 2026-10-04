import BalancedAssortments.FixedSupportCostProgramCorrect
import BalancedAssortments.FixedSupportCostProgramBounds

namespace BalancedAssortments.FixedSupportCostProgram
open ComplexityTimeFractions (decode Valid width)
open FixedSupportCostRational FixedSupportCostPoints FixedSupportCostMax
open FixedSupportAlgorithm

/-- The actual raw-bit exact prescribed-support solver: mathematical
correctness, exact active support, output encoding bounds, and total polynomial
bit/list cost refer to the same executable program and the same returned data. -/
theorem binary_fixed_support_solver {n B : ℕ} (hn : 0<n) (r v : Fin n→ℚ)
    (ps : List (Fin n×Product)) (α K : Fraction)
    (hlabels : ps.map Prod.fst=List.finRange n) (hp : ∀ p ∈ ps,p.2.Valid)
    (hr : ∀ i,0<r i) (hv : ∀ i,0<v i) (hα : Valid α) (hK : Valid K)
    (hαpos : 0<decode α) (hα1 : decode α≤1) (hKpos : 0<decode K)
    (hdata : ∀ p ∈ ps,decode p.2.1=r p.1 ∧ decode p.2.2=v p.1)
    (hαw : width α≤B) (hKw : width K≤B) (hpw : ∀ p ∈ ps,p.2.Width B) :
    ∃ out p, (runBits α K ps).1=some out ∧
      Realizes r v (decode α) (decode K) out p ∧ out.1.length=n ∧
      (∀ x ∈ out.1,Valid x.2 ∧ 0<decode x.2 ∧ width x.2≤outputVectorWidth n B) ∧
      Valid out.2 ∧ width out.2≤outputObjectiveWidth n B ∧
      FixedSupportReal.Feasible (fun i => (v i : ℝ)) (decode α : ℝ) (decode K : ℝ)
        (fun i => (candidateVector r v (decode α) (decode K) p i : ℝ)) ∧
      (∀ w : Fin n→ℝ,FixedSupportReal.Feasible (fun i => (v i : ℝ))
        (decode α : ℝ) (decode K : ℝ) w →
        FixedSupportReal.revenue (fun i => (r i : ℝ)) w≤(decode out.2 : ℝ)) ∧
      (runBits α K ps).2≤runCost n B := by
  obtain ⟨out,p,he,hreal,hvalid,hov,hpos,hf,hopt⟩ := runBits_exact_support hn r v ps α K hlabels hp hr hv
    hα hK hαpos hα1 hKpos hdata
  have hlen : ps.length=n := by
    have hh := congrArg List.length hlabels
    simpa using hh
  have hwidth := runBits_width α K ps hα hK hp hαw hKw hpw he
  have hcost := runBits_cost α K ps hα hK hp hαw hKw hpw
  rw [hlen] at hwidth hcost
  have houtlen : out.1.length=n := by
    have hh := congrArg List.length hreal.1
    have ho := (scoreOrder_perm r v p.1).length_eq
    simp only [List.length_map,List.length_finRange] at hh ho
    omega
  refine ⟨out,p,he,hreal,houtlen,?_,hov,hwidth.2,hf,hopt,hcost⟩
  intro x hx
  refine ⟨hvalid x hx,?_,hwidth.1 x hx⟩
  have hm : (x.1,decode x.2) ∈ out.1.map (fun x => (x.1,decode x.2)) := List.mem_map.mpr ⟨x,hx,rfl⟩
  rw [hreal.1] at hm
  obtain ⟨i,hi,heq⟩ := List.mem_map.mp hm
  have hv' := congrArg Prod.snd heq
  dsimp only at hv'
  rw [← hv']
  exact hpos i

end BalancedAssortments.FixedSupportCostProgram
