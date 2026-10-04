import BalancedAssortments.FPTASCostCodecPolynomial

/-! End-to-end FPTAS theorem on flat serialized input and output bitstreams. -/
namespace BalancedAssortments.FPTASCostCodec
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram FPTASCostComplete
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

def decodeOutput (bits : List Bool) : Option (List PolicyAtom) :=
  (EncodingTime.parse bits).1.bind parsePolicy

lemma run_decoded (bits : List Bool) (x : Input) (h : (parse bits).1 = some x) :
    (run bits).1.bind decodeOutput =
      some (runPolicyBits x.alpha x.epsilon x.rank x.products).1 := by
  simp only [run,h,Option.bind_some,decodeOutput]
  exact emitPolicy_roundtrip _

/-- Actual flat parser, policy algorithm and emitter. The output decodes to a
legal exactly balanced rational policy; it approximates every feasible real
sales vector and has a literal polynomial runtime in ORIGINAL bit length and
inverse accuracy. No intermediate widths, grid horizons or DP bounds are
assumed. Mathematical input validity is explicit. -/
theorem flat_policy_fptas {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (alpha epsilon : Fraction)
    (ks : List Bool) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (bits : List Bool)
    (hparse : (parse bits).1 = some ⟨alpha,epsilon,ks,sourceProducts rv⟩) :
    ∃ output : List Bool, ∃ atoms : List PolicyAtom,
      (run bits).1 = some output ∧ decodeOutput output = some atoms ∧
      FPTAS.PolicyValid d.K (interpretPolicy (n := n+1) atoms) ∧
      Sales.Balanced (d.α : ℝ) (FPTAS.policySales d.v (interpretPolicy (n := n+1) atoms)) ∧
      atoms.length ≤ n+2 ∧
      (∀ a ∈ atoms,a.1.Valid ∧ a.2.length=n+1) ∧
      (∀ u : Fin (n+1) → ℝ,
        Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u →
        (1-(ε : ℝ))*Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
          Sales.revenue (fun i => (d.r i : ℝ))
            (FPTAS.policySales d.v (interpretPolicy (n := n+1) atoms))) ∧
      (run bits).2 ≤ MvPolynomial.eval ![bits.length,⌈10/ε⌉₊] flatPolynomial := by
  let atoms := (runPolicyBits alpha epsilon ks (sourceProducts rv)).1
  have hb := binary_policy_fptas d hd ε hε hε1 alpha epsilon ks rv ha he had hed hK hprod hdec
  refine ⟨(emitPolicy atoms).1,atoms,?_,?_,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,?_⟩
  · simp only [run,hparse,atoms]
  · exact emitPolicy_roundtrip atoms
  · exact run_polynomial d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec bits hparse

end BalancedAssortments.FPTASCostCodec
