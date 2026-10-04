import BalancedAssortments.FPTASCostProgramCorrect
import BalancedAssortments.FPTASCostProgramBound
import BalancedAssortments.FPTASCostPolicy

/-! Complete raw binary FPTAS output: sales computation, marginal conversion,
sparse binary decomposition, and exact MNL reverse tilt. -/
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace BalancedAssortments.FPTASCostComplete
open ComplexityTimeBinary KnapsackCostRational FPTASCostSeeds FPTASCostOutput FPTASCostPolicy
open FPTASCostProgram Decomposition.CostMachine

/-- Coordinatewise binary division, with exact representation and charged traversal. -/
def marginalBits : List Fraction → List Fraction → List Fraction × ℕ
  | [], _ => ([], 1)
  | _, [] => ([], 1)
  | w::ws, v::vs =>
      let z := divideFresh w v
      let tail := marginalBits ws vs
      (z.1::tail.1,z.2+tail.2+4)

theorem marginalBits_ofFn {n : ℕ} (ws vs : Fin n → Fraction) :
    (marginalBits (List.ofFn ws) (List.ofFn vs)).1 =
      List.ofFn (fun i => (divideFresh (ws i) (vs i)).1) := by
  induction n with
  | zero => simp [marginalBits]
  | succ n ih => simp [List.ofFn_succ,marginalBits,ih]

@[simp] theorem marginalBits_length (ws vs : List Fraction) :
    (marginalBits ws vs).1.length = min ws.length vs.length := by
  induction ws generalizing vs with
  | nil => simp [marginalBits]
  | cons w ws ih => cases vs <;> simp [marginalBits,ih,Nat.succ_min_succ]

theorem marginalBits_width (ws vs : List Fraction) {a b : ℕ}
    (hw : ∀ w ∈ ws,w.Width a) (hv : ∀ v ∈ vs,v.Width b) :
    ∀ z ∈ (marginalBits ws vs).1,z.Width (a+2*b) := by
  induction ws generalizing vs with
  | nil => simp [marginalBits]
  | cons w ws ih =>
    cases vs with
    | nil => simp [marginalBits]
    | cons v vs =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact divideFresh_width (hw _ (by simp)) (hv _ (by simp))
      · exact ih _ (fun x hx => hw x (by simp [hx])) (fun x hx => hv x (by simp [hx])) z hz

theorem marginalBits_cost (ws vs : List Fraction) {a b : ℕ}
    (hw : ∀ w ∈ ws,w.Width a) (hv : ∀ v ∈ vs,v.Width b) :
    (marginalBits ws vs).2 ≤ ws.length*(256*(a+b+1)^2+12)+1 := by
  induction ws generalizing vs with
  | nil => simp [marginalBits]
  | cons w ws ih =>
    cases vs with
    | nil => simp [marginalBits]
    | cons v vs =>
      have hd := divideFresh_cost (hw w (by simp)) (hv v (by simp))
      have ht := ih vs (fun x hx => hw x (by simp [hx])) (fun x hx => hv x (by simp [hx]))
      simp only [marginalBits,List.length_cons]
      nlinarith

/-- Finish any feasible raw sales vector without reducing its fractions. -/
def finishPolicy (ks : List Bool) (vs ws : List Fraction) : List PolicyAtom × ℕ :=
  let z := marginalBits ws vs
  let sparse := binaryGreedyRank ks (z.1.map Fraction.numerator) (z.1.map Fraction.denominator)
  let out := policyOutput vs ws sparse.1 sparse.2.1
  (out.1,z.2+sparse.2.2+out.2+2*z.1.length+8)

/-- Complete executable policy entry point; the capacity fraction is formed
from the supplied binary rank, with no canonical arithmetic. -/
def runPolicyBits (alpha epsilon : Fraction) (ks : List Bool) (products : List Product) :
    List PolicyAtom × ℕ :=
  let sales := runSalesBits alpha epsilon (⟨ks,[true]⟩ : Fraction) products
  let vs := products.map Prod.snd
  let out := finishPolicy ks vs sales.1
  (out.1,sales.2+out.2+products.length+6)

theorem finishPolicy_correct {n : ℕ} (ks : List Bool) (vs ws : Fin n → Fraction)
    (hv : ∀ i,(vs i).Valid) (hw : ∀ i,(ws i).Valid) (hvp : ∀ i,0<(vs i).decode)
    (hfeas : Decomposition.Feasible (value ks) (fun i => (ws i).decode/(vs i).decode)) :
    FPTAS.PolicyValid (value ks) (interpretPolicy (n := n)
      (finishPolicy ks (List.ofFn vs) (List.ofFn ws)).1) ∧
    FPTAS.policySales (fun i => (vs i).decode)
      (interpretPolicy (n := n) (finishPolicy ks (List.ofFn vs) (List.ofFn ws)).1) =
        Sales.compactSales (fun i => ((ws i).decode : ℝ)) ∧
      (finishPolicy ks (List.ofFn vs) (List.ofFn ws)).1.length ≤ n+1 := by
  let ms : Fin n → Fraction := fun i => (divideFresh (ws i) (vs i)).1
  have hmvalid : ∀ i,(ms i).Valid := fun i => divideFresh_valid (hw i) (hvp i)
  have hmdecode : ∀ i,(ms i).decode = (ws i).decode/(vs i).decode :=
    fun i => divideFresh_decode _ _
  let nums := fun i => (ms i).numerator
  let dens := fun i => (ms i).denominator
  have hd : ∀ i,0<value (dens i) := hmvalid
  have hz : (fun i => (value (nums i) : ℚ)/(value (dens i) : ℚ)) =
      (fun i => (ws i).decode/(vs i).decode) := by
    funext i
    exact hmdecode i
  have hraw : Decomposition.Feasible (value ks)
      (fun i => (value (nums i) : ℚ)/(value (dens i) : ℚ)) := by
    rw [hz]
    exact hfeas
  have he := raw_binaryGreedy_eq_greedy (K := value ks) nums dens hd hraw
  rw [hz] at he
  let sparse := binaryGreedyRank ks (List.ofFn nums) (List.ofFn dens)
  have hsp : Decomposition.interpretGrid (value sparse.1)
      (interpretBitAtoms (n := n) sparse.2.1) =
      Decomposition.greedy (value ks) (fun i => (ws i).decode/(vs i).decode) := by
    simpa only [sparse,binaryGreedyRank,rankTokens_length] using he
  have hc : Decomposition.ValidDecomposition (value ks)
      (fun i => (ws i).decode/(vs i).decode)
      (Decomposition.interpretGrid (value sparse.1) (interpretBitAtoms (n := n) sparse.2.1)) := by
    rw [hsp]
    exact (Decomposition.greedy_correct hfeas).1
  have hp := policyOutput_valid vs ws sparse.1 sparse.2.1 hv hw hvp hc
  have hlen : sparse.2.1.length ≤ n+1 := by
    have hh := (Decomposition.greedy_correct hfeas).2
    rw [← hsp] at hh
    simpa [Decomposition.interpretGrid,interpretBitAtoms] using hh
  have hout : (finishPolicy ks (List.ofFn vs) (List.ofFn ws)).1 =
      (policyOutput (List.ofFn vs) (List.ofFn ws) sparse.1 sparse.2.1).1 := by
    simp only [finishPolicy,marginalBits_ofFn,List.map_ofFn]
    rfl
  rw [hout]
  exact ⟨hp.1,hp.2,by simpa only [policyOutput_length] using hlen⟩


/-- The full raw program returns a normalized legal sparse MNL policy with
exactly the sales vector selected by the certified binary sales program. -/
theorem runPolicyBits_semantics {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : Bits) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i) :
    let sales := (runSalesBits alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv)).1
    let out := (runPolicyBits alpha epsilon ks (sourceProducts rv)).1
    FPTAS.PolicyValid d.K (interpretPolicy (n := n+1) out) ∧
      FPTAS.policySales d.v (interpretPolicy (n := n+1) out) =
        Sales.compactSales (fun i => (FPTASCostFunctional.decodeVector (n := n+1) sales i : ℝ)) ∧
      out.length ≤ n+2 := by
  let capacity : Fraction := ⟨ks,[true]⟩
  have hc : capacity.Valid := by norm_num [capacity,Fraction.Valid,value]
  have hcd : capacity.decode = (d.K : ℚ) := by simp [capacity,Fraction.decode,value,hK]
  have hs := runSalesBits_semantics d hd ε hε alpha epsilon capacity rv ha he hc had hed hcd hprod hdec
  let ws := (runSalesBits alpha epsilon capacity (sourceProducts rv)).1
  let wf : Fin (n+1) → Fraction := fun i => ws[i.val]?.getD FPTASCostOutput.zero
  let vf : Fin (n+1) → Fraction := fun i => (rv i).2
  have hwlist : List.ofFn wf = ws := list_ofFn_getD ws FPTASCostOutput.zero hs.1
  have hvlist : List.ofFn vf = (sourceProducts rv).map Prod.snd := by
    simpa only [vf,sourceProducts,List.map_map,Function.comp_def] using (show List.ofFn vf = (List.finRange (n+1)).map vf from List.ofFn_eq_map)
  have hwvalid : ∀ i,(wf i).Valid := by
    intro i
    have hi : i.val < ws.length := by rw [hs.1]; exact i.isLt
    simp only [wf,List.getElem?_eq_getElem hi,Option.getD_some]
    exact hs.2.1 _ (List.getElem_mem hi)
  have hwd : FPTASCostFunctional.decodeVector (n := n+1) ws = fun i => (wf i).decode := by
    rw [← hwlist,FPTASCostFunctional.decodeVector_ofFn]
  have hf : FPTAS.Feasible d (fun i => (wf i).decode) := by
    have hh := hs.2.2.1
    rw [hwd] at hh
    exact hh
  have hvp : ∀ i,0<(vf i).decode := by intro i; rw [show (vf i).decode=d.v i from (hdec i).2]; exact (hd.1 i).2
  have hm : Decomposition.Feasible (value ks) (fun i => (wf i).decode/(vf i).decode) := by
    constructor
    · intro i
      dsimp only
      rw [show (vf i).decode=d.v i from (hdec i).2]
      exact ⟨div_nonneg (hf.1 i).1 (hd.1 i).2.le,(div_le_one (hd.1 i).2).2 (hf.1 i).2⟩
    · simpa only [vf,(hdec _).2,hK] using hf.2.1
  have hout := finishPolicy_correct ks vf wf (fun i => (hprod i).2) hwvalid hvp hm
  have hresult : (runPolicyBits alpha epsilon ks (sourceProducts rv)).1 =
      (finishPolicy ks (List.ofFn vf) (List.ofFn wf)).1 := by
    change (finishPolicy ks ((sourceProducts rv).map Prod.snd) ws).1 = _
    rw [hvlist,hwlist]
  change FPTAS.PolicyValid d.K (interpretPolicy (n := n+1) (runPolicyBits alpha epsilon ks (sourceProducts rv)).1) ∧ _
  rw [hresult,hwd]
  simpa only [vf,(hdec _).2,hK,Nat.add_assoc] using hout

/-- Exact balance and objective preservation for the actual raw policy output. -/
theorem runPolicyBits_balance_revenue {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (alpha epsilon : Fraction) (ks : Bits) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i) :
    let sales := (runSalesBits alpha epsilon (⟨ks,[true]⟩ : Fraction) (sourceProducts rv)).1
    let out := (runPolicyBits alpha epsilon ks (sourceProducts rv)).1
    Sales.Balanced (d.α : ℝ) (FPTAS.policySales d.v (interpretPolicy (n := n+1) out)) ∧
      Sales.revenue (fun i => (d.r i : ℝ)) (FPTAS.policySales d.v (interpretPolicy (n := n+1) out)) =
        (FPTAS.revenue d (FPTASCostFunctional.decodeVector sales) : ℝ) := by
  have hsem := runPolicyBits_semantics d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec
  have hc : (⟨ks,[true]⟩ : Fraction).Valid := by norm_num [Fraction.Valid,value]
  have hcd : (⟨ks,[true]⟩ : Fraction).decode = (d.K : ℚ) := by simp [Fraction.decode,value,hK]
  have hs := runSalesBits_semantics d hd ε hε alpha epsilon (⟨ks,[true]⟩ : Fraction) rv ha he hc had hed hcd hprod hdec
  change Sales.Balanced _ _ ∧ _
  rw [hsem.2.1]
  constructor
  · apply (Sales.compact_balance _ _ (fun i => by
      have hh := (hs.2.2.1.1 i).1
      exact_mod_cast hh)).2
    intro i
    rcases hs.2.2.1.2.2 i with hi | hi
    · left; try dsimp only; exact_mod_cast hi
    · right; intro j; try dsimp only; exact_mod_cast hi j
  · rw [Sales.compact_revenue]
    simp [Sales.objective,FPTAS.revenue]

/-- End-to-end approximation against all feasible real compact sales vectors;
the returned object is an actual raw binary sparse randomized MNL policy. -/
theorem runPolicyBits_approximation {n : ℕ} (d : FPTAS.Input n) (hd : FPTAS.Valid d)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε < 1) (alpha epsilon : Fraction) (ks : Bits) (rv : Fin (n+1) → Product)
    (ha : alpha.Valid) (he : epsilon.Valid) (had : alpha.decode=d.α) (hed : epsilon.decode=ε)
    (hK : value ks=d.K) (hprod : ∀ i,(rv i).1.Valid ∧ (rv i).2.Valid)
    (hdec : ∀ i,(rv i).1.decode=d.r i ∧ (rv i).2.decode=d.v i)
    (u : Fin (n+1) → ℝ) (hu : Optimization.feasible (fun i => (d.v i : ℝ)) d.α d.K u) :
    (1-(ε : ℝ))*Optimization.revenue (fun i => (d.r i : ℝ)) u ≤
      Sales.revenue (fun i => (d.r i : ℝ))
        (FPTAS.policySales d.v (interpretPolicy (n := n+1)
          (runPolicyBits alpha epsilon ks (sourceProducts rv)).1)) := by
  rw [(runPolicyBits_balance_revenue d hd ε hε alpha epsilon ks rv ha he had hed hK hprod hdec).2]
  apply runSalesBits_approximation d hd ε hε hε1 alpha epsilon _ rv ha he _ had hed _ hprod hdec u hu
  · norm_num [Fraction.Valid,value]
  · simp [Fraction.decode,value,hK]

end BalancedAssortments.FPTASCostComplete
