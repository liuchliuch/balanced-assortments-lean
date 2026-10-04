import BalancedAssortments.FPTASCostProgram
import BalancedAssortments.FPTASGuarantee

namespace BalancedAssortments.FPTASCostFunctional
open FPTAS KnapsackCostRational FPTASCostOutput FPTASCostLoops

/-- Coordinate interpretation of an actual returned list, retaining the source
zero-default convention only outside the proved length. -/
def decodeVector {n : ℕ} (xs : List Fraction) : Fin n → ℚ :=
  fun i => (xs[i.val]?.map Fraction.decode).getD 0

theorem ofFn_decodeVector (xs : List Fraction) :
    List.ofFn (decodeVector (n := xs.length) xs) = xs.map Fraction.decode := by
  rw [← List.ofFn_getElem_eq_map xs Fraction.decode]
  apply congrArg List.ofFn
  funext i
  simp [decodeVector,i.isLt]

theorem ofFn_decodeVector_length {n : ℕ} (xs : List Fraction) (hlen : xs.length = n) :
    List.ofFn (decodeVector (n := n) xs) = xs.map Fraction.decode := by
  subst n
  exact ofFn_decodeVector xs

theorem decodeVector_ofFn {n : ℕ} (x : Fin n → Fraction) :
    decodeVector (List.ofFn x) = fun i => (x i).decode := by
  funext i
  simp [decodeVector]

theorem stateVector_decode {n : ℕ} (s : KnapsackCostState.State) :
    FPTAS.stateVector (n := n) s.decode = decodeVector s.choices := by
  funext i
  simp [FPTAS.stateVector,KnapsackCostState.State.decode,decodeVector,List.getElem?_map]

lemma zipWith_ofFn_local {A B C : Type*} (f : A → B → C) {n : ℕ}
    (a : Fin n → A) (b : Fin n → B) :
    List.zipWith f (List.ofFn a) (List.ofFn b) = List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.ofFn_succ,ih]

theorem list_revenue_fin {n : ℕ} (rs ws : List Fraction)
    (hrn : rs.length = n) (hwn : ws.length = n)
    (hr : ∀ x ∈ rs, x.Valid) (hw : ∀ x ∈ ws, x.Valid) :
    (FPTASCostOutput.revenue rs ws).1.decode =
      (∑ i : Fin n, decodeVector rs i * decodeVector ws i)/(1+∑ i : Fin n, decodeVector ws i) := by
  rw [FPTASCostOutput.revenue_decode rs ws hr hw]
  have hr' := ofFn_decodeVector_length rs hrn
  have hw' := ofFn_decodeVector_length ws hwn
  have hz : ((rs.zip ws).map fun p => p.1.decode*p.2.decode) =
      (rs.map Fraction.decode).zipWith (· * ·) (ws.map Fraction.decode) := by
    clear hrn hwn hr hw hr' hw' n
    induction rs generalizing ws with
    | nil => cases ws <;> rfl
    | cons r rs ih =>
      cases ws with
      | nil => rfl
      | cons w ws =>
        simpa only [List.zip_cons_cons,List.map_cons,List.zipWith_cons_cons] using
          congrArg (List.cons (r.decode*w.decode)) (ih ws)
  rw [hz,←hr',←hw']
  simp [zipWith_ofFn_local,List.sum_ofFn]

/-- Any actual accepted candidate retains exact source feasibility. -/
theorem candidateAt_feasible {n : ℕ} {d : Input n} (hd : Valid d) {δ τ ρ : ℚ}
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) {w : Fin (n+1) → ℚ}
    (hc : candidateAt d δ τ ρ = some w) : Feasible d w := by
  let gs := groups d δ τ ρ
  let pmax := maxList (gs.flatten.map Knapsack.Item.profit)
  let θ := δ*pmax/(n+1)
  let bound := (n+1)*⌈(n+1 : ℚ)/δ⌉₊
  change (if pmax ≤ 0 then none else match Knapsack.solve θ d.K bound gs with
    | none => none | some s => if ρ ≤ s.profit then some (stateVector s) else none) = some w at hc
  by_cases hp : pmax ≤ 0
  · simp [hp] at hc
  · simp only [hp,if_false] at hc
    cases hs : Knapsack.solve θ d.K bound gs with
    | none => simp [hs] at hc
    | some s =>
      by_cases hρ : ρ ≤ s.profit
      · simp only [hs,hρ,if_true,Option.some.injEq] at hc
        subst w
        exact ApproximationCandidate.solve_vector_feasible (fun i => (hd.1 i).2) hd.2.1 hτ hδ hs
      · simp [hs,hρ] at hc

theorem rawCandidates_feasible {n : ℕ} (d : Input n) (hd : Valid d) {ε : ℚ}
    (hε : 0 ≤ ε) {w : Fin (n+1) → ℚ} (hw : w ∈ rawCandidates d ε) : Feasible d w := by
  simp only [rawCandidates,List.mem_append] at hw
  rcases hw with hw | hw
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
    exact singleton_feasible d hd i
  · obtain ⟨τ,hτ,hw⟩ := List.mem_flatMap.mp hw
    obtain ⟨ρ,_,hc⟩ := List.mem_filterMap.mp hw
    have hδ : 0 ≤ ε/10 := by positivity
    have ha : 0 ≤ d.α*vmin d/(n+1 : ℚ) := by
      exact div_nonneg (mul_nonneg hd.2.1.le (vmin_pos d (fun i => (hd.1 i).2)).le) (by positivity)
    have ht := ha.trans (Grids.grid_lower_bound ha hδ hτ)
    exact candidateAt_feasible hd hδ ht hc

theorem admissibleCandidates_eq_raw {n : ℕ} (d : Input n) (hd : Valid d) {ε : ℚ}
    (hε : 0 ≤ ε) : admissibleCandidates d ε = rawCandidates d ε := by
  apply List.filter_eq_self.mpr
  intro w hw
  exact decide_eq_true (rawCandidates_feasible d hd hε hw)

theorem runSales_mem_raw {n : ℕ} (d : Input n) (hd : Valid d) {ε : ℚ}
    (hε : 0 ≤ ε) : runSales d ε ∈ rawCandidates d ε := by
  have hm : singleton d 0 ∈ rawCandidates d ε := by
    simp only [rawCandidates,List.mem_append,List.mem_map]
    exact Or.inl ⟨0,List.mem_finRange 0,rfl⟩
  unfold runSales
  rw [admissibleCandidates_eq_raw d hd hε]
  cases h : (rawCandidates d ε).argmax (FPTAS.revenue d) with
  | none =>
    have he := List.argmax_eq_none.mp h
    rw [he] at hm
    simp at hm
  | some w => exact List.argmax_mem h
end BalancedAssortments.FPTASCostFunctional
