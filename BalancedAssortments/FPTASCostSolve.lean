import BalancedAssortments.KnapsackCostPreprocess
import BalancedAssortments.FPTASCostCounts
import BalancedAssortments.ApproximationCandidate

/-! Specialization of the bit-level knapsack solver to the actual FPTAS calls.
This module accounts for each complete call, including binary floor preprocessing;
the binary execution of outer grid/option generation is composed separately. -/
namespace BalancedAssortments.FPTASCost
open FPTAS KnapsackCostRational

/-- A representation of the already-created option data at a call boundary. -/
def rawItem (i : Knapsack.Item) : KnapsackCostState.Item := ⟨encode i.value, encode i.weight, encode i.profit, []⟩

def binaryCall {n : ℕ} (d : Input n) (ε τ ρ : ℚ) : Option KnapsackCostState.State × ℕ :=
  let δ := ε/10
  let gs := groups d δ τ ρ
  let pmax := maxList (gs.flatten.map Knapsack.Item.profit)
  let θ := δ*pmax/(n+1)
  KnapsackCostState.scaledSolve (encode θ) (encode d.K) ((n+1)*⌈(n+1:ℚ)/δ⌉₊)
    (gs.map (List.map rawItem))

/-- Explicit polynomial used by the binary solver, expressed only in dimensions
and bit width. S is the integer profit-state cutoff. -/
def solverBudget (N M S b : ℕ) : ℕ :=
  let W := 1+N*(6*b+1)+2*(S+1)+3*b
  N*(M*(4096*(b+1)^2+8)+5) + 64*(S+1)*(2*(S+1)+1) +
    N*(KnapsackCostState.rowCost (S+1) M (S+1) W N+4) + (S+1)*(16*W+9)+20

theorem solverBudget_mono {N N' M M' S S' b b' : ℕ}
    (hN : N ≤ N') (hM : M ≤ M') (hS : S ≤ S') (hb : b ≤ b') :
    solverBudget N M S b ≤ solverBudget N' M' S' b' := by
  dsimp only [solverBudget, KnapsackCostState.rowCost]
  gcongr

def callBudget (I Q : ℕ) : ℕ :=
  solverBudget I (innerHorizon (I+4) Q+2) (I^2*Q) (itemWidth (I+4) Q)

theorem capacity_width {n : ℕ} (d : Input n) (ε : ℚ) :
    (encode (d.K : ℚ)).Width (itemWidth (inputBits d ε+4) ⌈10/ε⌉₊) := by
  have hb := (nat_coefficient_from_size d.K).sizes
  have hk : d.K.size ≤ inputBits d ε := by unfold inputBits; omega
  have hm : d.K.size+1 ≤ itemWidth (inputBits d ε+4) ⌈10/ε⌉₊ := by
    unfold itemWidth profitWidth
    omega
  exact encode_width (hb.1.trans hm) (hb.2.trans hm)

/-- Every actual DP call has a uniform explicit polynomial bit/list-operation
bound in summed original input bit length and the reciprocal-accuracy ceiling. -/
theorem binaryCall_cost {n : ℕ} (d : Input n) (ε : ℚ) {τ ρ : ℚ}
    (hτ : τ ∈ scales d (ε/10)) (hρ : ρ ∈ revenues d (ε/10)) :
    (binaryCall d ε τ ρ).2 ≤ callBudget (inputBits d ε) ⌈10/ε⌉₊ := by
  let I := inputBits d ε
  let Q := ⌈10/ε⌉₊
  let b := itemWidth (I+4) Q
  let M := innerHorizon (I+4) Q+2
  let S := (n+1)*⌈(n+1:ℚ)/(ε/10)⌉₊
  obtain ⟨ht,hi⟩ := actual_call_field_widths d ε hτ hρ
  have hg : ∀ g ∈ (groups d (ε/10) τ ρ).map (List.map rawItem),
      g.length ≤ M ∧ ∀ i ∈ g, i.value.Width b ∧ i.weight.Width b ∧ i.profit.Width b := by
    intro g hgm
    obtain ⟨g',hg',rfl⟩ := List.mem_map.mp hgm
    refine ⟨?_, ?_⟩
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hg'
      have hh := (group_bounds d (ε/10) (actual_input_bound d ε) hτ hρ i).1
      simpa only [List.length_map, precision_parameter] using hh
    · intro i him
      obtain ⟨i',hi',rfl⟩ := List.mem_map.mp him
      exact hi g' hg' i' hi'
  have hh := KnapsackCostState.scaledSolve_cost (bound := S) ht (capacity_width d ε) hg
  have hn : ((groups d (ε/10) τ ρ).map (List.map rawItem)).length = n+1 := by simp [groups]
  have hexact : (binaryCall d ε τ ρ).2 ≤ solverBudget (n+1) M S b := by
    simpa only [binaryCall, hn, solverBudget] using hh
  have hS : S ≤ I^2*Q := by
    have hs := state_cutoff_bound (n+1) (ε/10)
    rw [precision_parameter] at hs
    simpa only [S, I, Nat.cast_add, Nat.cast_one] using hs.trans (Nat.mul_le_mul_right Q (Nat.pow_le_pow_left (product_count_le_inputBits d ε) 2))
  exact hexact.trans (solverBudget_mono (product_count_le_inputBits d ε) le_rfl hS le_rfl)

theorem rawItem_valid (i : Knapsack.Item) : (rawItem i).Valid :=
  ⟨encode_valid _, encode_valid _, encode_valid _⟩

theorem rawItem_decode {i : Knapsack.Item} (hv : 0 ≤ i.value) (hw : 0 ≤ i.weight)
    (hp : 0 ≤ i.profit) : (rawItem i).decode = i := by
  simp only [rawItem, KnapsackCostState.Item.decode]
  rw [encode_decode hv, encode_decode hw, encode_decode hp]

/-- A successful-call precondition connects the binary implementation to the
exact rational DP used in candidateAt. -/
theorem binaryCall_decode {n : ℕ} (d : Input n) (ε τ ρ : ℚ)
    (hε : 0 < ε) (hτ : 0 ≤ τ) (hv : ∀ i, 0 < d.v i)
    (hpmax : 0 < maxList (((groups d (ε/10) τ ρ).flatten).map Knapsack.Item.profit)) :
    (binaryCall d ε τ ρ).1.map KnapsackCostState.State.decode =
      Knapsack.solve ((ε/10)*maxList (((groups d (ε/10) τ ρ).flatten).map Knapsack.Item.profit)/(n+1))
        d.K ((n+1)*⌈(n+1:ℚ)/(ε/10)⌉₊) (groups d (ε/10) τ ρ) := by
  let θ := (ε/10)*maxList (((groups d (ε/10) τ ρ).flatten).map Knapsack.Item.profit)/(n+1)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hδ : 0 ≤ ε/10 := by positivity
  have hdec : ∀ g ∈ groups d (ε/10) τ ρ, ∀ i ∈ g, (rawItem i).decode = i := by
    intro g hg item hi
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hg
    have hd := ApproximationCandidate.group_item_data hi
    have hw := ApproximationCandidate.group_item_weight_nonneg (hv j) hτ hδ hi
    have hvalue : 0 ≤ item.value := by
      rcases hd.2.2.1 with hz | hm
      · simp [hz]
      · exact hτ.trans (Grids.grid_lower_bound hτ hδ hm)
    exact rawItem_decode hvalue hw hd.2.2.2
  have hvalid : ∀ g ∈ (groups d (ε/10) τ ρ).map (List.map rawItem), ∀ i ∈ g, i.Valid := by
    intro g hg i hi
    obtain ⟨g',_,rfl⟩ := List.mem_map.mp hg
    obtain ⟨i',_,rfl⟩ := List.mem_map.mp hi
    exact rawItem_valid i'
  have hh := KnapsackCostState.scaledSolve_decode (bound := (n+1)*⌈(n+1:ℚ)/(ε/10)⌉₊)
    (encode_valid θ) (by rwa [encode_decode hθ.le]) (encode_valid (d.K:ℚ)) hvalid
  have hgroups : ((groups d (ε/10) τ ρ).map (List.map rawItem)).map (List.map KnapsackCostState.Item.decode) =
      groups d (ε/10) τ ρ := by
    rw [List.map_map]
    calc
      _ = (groups d (ε/10) τ ρ).map id := by
        apply List.map_congr_left
        intro g hg
        simp only [Function.comp_apply, List.map_map]
        calc
          _ = g.map id := List.map_congr_left (fun i hi => hdec g hg i hi)
          _ = g := List.map_id _
      _ = _ := List.map_id _
  simpa only [binaryCall, encode_decode hθ.le, encode_decode (show (0:ℚ) ≤ d.K by positivity), hgroups]
    using hh

end BalancedAssortments.FPTASCost
