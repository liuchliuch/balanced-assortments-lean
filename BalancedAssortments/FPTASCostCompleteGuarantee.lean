import BalancedAssortments.FPTASCostCompletePolynomial
import BalancedAssortments.FPTASCostCompleteShape

/-! One end-to-end theorem for the complete raw binary policy program. -/
namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram

/-- Full FPTAS guarantee for the actual raw-bit/list program and original input
size: exact policy legality and balance, linear support, arbitrary-real optimum
comparison, and a literal polynomial bound. -/
theorem binary_policy_fptas {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (alpha epsilon : Fraction)
    (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i) :
    let out := runPolicyBits alpha epsilon ks (sourceProducts rv)
    let policy := interpretPolicy (n := n+1) out.1
    let I := (serializeInput alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv)).length
    FPTAS.PolicyValid d.K policy ∧
      Sales.Balanced (d.α : ℝ) (FPTAS.policySales d.v policy) ∧
      out.1.length ≤ n+2 ∧
      (∀ a ∈ out.1,a.1.Valid ∧ a.2.length=n+1) ∧
      (∀ u : Fin (n+1) → ℝ,
        Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u →
        (1-(ε : ℝ))*Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
          Sales.revenue (fun i => (d.r i : ℝ)) (FPTAS.policySales d.v policy)) ∧
      out.2 ≤ MvPolynomial.eval ![I,I,⌈10/ε⌉₊] policyPolynomial := by
  have hs := runPolicyBits_semantics d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
  have hb := runPolicyBits_balance_revenue d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
  exact ⟨hs.1,hb.1,hs.2.2,
    runPolicyBits_raw_shape d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec,
    runPolicyBits_approximation d hd ε hε hε1 alpha epsilon ks rv ha he had hed hK hprod hdec,
    runPolicyBits_serialized_polynomial d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec⟩

/-- Direct comparison to every feasible original randomized MNL assortment
policy, rather than only its compact-sales representation. -/
theorem binary_policy_approximates_original {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (alpha epsilon : Fraction)
    (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    {A : Type*} [Fintype A] (S : A → Finset (Fin (n+1))) (q : A → ℝ)
    (hq : Sales.Distribution q) (hcard : ∀ a,(S a).card≤d.K)
    (hb : Sales.Balanced (d.α : ℝ) (Sales.sales (fun i => (d.v i : ℝ)) S q)) :
    (1-(ε : ℝ))*Sales.revenue (fun i => (d.r i : ℝ))
      (Sales.sales (fun i => (d.v i : ℝ)) S q) ≤
    Sales.revenue (fun i => (d.r i : ℝ)) (FPTAS.policySales d.v
      (interpretPolicy (n := n+1) (runPolicyBits alpha epsilon ks (sourceProducts rv)).1)) := by
  have hv : ∀ i,(0 : ℝ)<(d.v i : ℝ) := fun i => by exact_mod_cast (hd.1 i).2
  obtain ⟨w,hw,hs⟩ := Sales.policy_to_compact (fun i => (d.v i : ℝ)) hv S hq d.K hcard
  have hbw : Sales.Balanced (d.α : ℝ) w := by
    rw [hs] at hb
    exact (Sales.compact_balance _ _ (fun i => (hw.1 i).1)).1 hb
  have hf := (Sales.optimization_feasible_iff (fun i => (d.v i : ℝ)) w d.α d.K).2 ⟨hw,hbw⟩
  have hh := runPolicyBits_approximation d hd ε hε hε1 alpha epsilon ks rv ha he had hed hK hprod hdec w hf
  rw [hs,Sales.compact_revenue]
  exact hh

end BalancedAssortments.FPTASCostComplete
