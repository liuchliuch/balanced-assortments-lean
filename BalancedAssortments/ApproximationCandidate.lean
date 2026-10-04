import BalancedAssortments.FPTASBounds

/-! Exact interpretation of the rational knapsack options used by the outer routine. -/
namespace BalancedAssortments.ApproximationCandidate
open FPTAS Knapsack

theorem group_item_data {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    {i : Fin (n+1)} {item : Item} (hi : item ∈ group d δ τ ρ i) :
    item.weight = item.value / d.v i ∧ item.profit = (d.r i - ρ) * item.value ∧
    (item.value = 0 ∨ item.value ∈ Grids.geometricGrid τ δ (min (d.v i) (τ / d.α))
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α)))) ∧ 0 ≤ item.profit := by
  simp only [group, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq] at hi
  rcases hi with rfl | ⟨u, ⟨hu, hp⟩, rfl⟩
  · simp
  · exact ⟨rfl, rfl, Or.inr hu, hp.le⟩

theorem group_item_weight_nonneg {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    {i : Fin (n+1)} {item : Item} (hv : 0 < d.v i) (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hi : item ∈ group d δ τ ρ i) : 0 ≤ item.weight := by
  obtain ⟨hw, _, hz | hg, _⟩ := group_item_data hi
  · simp [hw, hz]
  · rw [hw]
    exact div_nonneg (hτ.trans (Grids.grid_lower_bound hτ hδ hg)) hv.le

theorem group_item_cap {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    {i : Fin (n+1)} {item : Item} (hv : 0 ≤ d.v i)
    (hi : item ∈ group d δ τ ρ i) : item.value ≤ d.v i := by
  obtain ⟨_, _, hz | hg, _⟩ := group_item_data hi
  · simpa [hz] using hv
  · obtain ⟨_, _, _, hb⟩ := Grids.mem_geometricGrid.mp hg
    exact hb.trans (min_le_left _ _)

theorem group_item_weight_le_one {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    {i : Fin (n+1)} {item : Item} (hv : 0 < d.v i)
    (hi : item ∈ group d δ τ ρ i) : item.weight ≤ 1 := by
  rw [(group_item_data hi).1]
  exact (div_le_one hv).2 (group_item_cap hv.le hi)

/-- The reconstructed finite vector corresponds coordinatewise to an actual option
from each product group; stored exact weight/profit equal their finite sums. -/
theorem solve_vector_data {n : ℕ} {d : Input n} {δ τ ρ θ capacity : ℚ}
    {bound : ℕ} {s : State} (hs : solve θ capacity bound (groups d δ τ ρ) = some s) :
    ∃ f : Fin (n+1) → Item,
      (∀ i, f i ∈ group d δ τ ρ i) ∧
      (∀ i, stateVector s i = (f i).value) ∧
      s.weight = ∑ i, (f i).weight ∧ s.profit = ∑ i, (f i).profit := by
  obtain ⟨items, hitems, hc, hw, hp, _⟩ := solve_reconstruction hs
  have hlen : items.length = n + 1 := by
    simpa [groups] using hitems.length_eq
  let f : Fin (n+1) → Item := fun i => items[i.val]'(by omega)
  have hlist : items = List.ofFn f := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro i
    have hglen : (groups d δ τ ρ).length = n+1 := by simp [groups]
    have hh := hitems.get (i := i.val) (by omega) (by omega)
    simpa only [groups, List.get_eq_getElem, List.getElem_map,
      List.getElem_finRange] using hh
  · intro i
    simp only [stateVector, hc, hlist, List.map_ofFn, List.getElem?_ofFn,
      dif_pos i.isLt, Option.getD_some, Function.comp_apply]
  · simpa only [hlist, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hw
  · simpa only [hlist, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hp

/-- Every returned DP vector obeys the exact assortment constraints before the
outer algorithm's defensive feasibility filter is applied. -/
theorem solve_vector_feasible {n : ℕ} {d : Input n} {δ τ ρ θ : ℚ}
    {bound : ℕ} {s : State} (hv : ∀ i, 0 < d.v i) (hα : 0 < d.α)
    (hτ : 0 ≤ τ) (hδ : 0 ≤ δ)
    (hs : solve θ d.K bound (groups d δ τ ρ) = some s) : Feasible d (stateVector s) := by
  obtain ⟨f, hf, hval, hw, hp⟩ := solve_vector_data hs
  have hoption : ∀ i, stateVector s i ∈ Grids.productOptions τ δ d.α (d.v i)
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α))) := by
    intro i
    rw [hval i]
    rcases (group_item_data (hf i)).2.2.1 with hz | hg
    · simp [Grids.productOptions, hz]
    · exact List.mem_cons_of_mem _ hg
  have hb := fun i => Grids.option_band hτ hδ (hoption i)
  have hnon : ∀ i : Fin (n+1), 0 ≤ stateVector s i := by
    intro i
    rcases hb i with hz | ⟨hl, _, _⟩
    · simp [hz]
    · exact hτ.trans hl
  have hupper : ∀ i : Fin (n+1), stateVector s i ≤ τ / d.α := by
    intro i
    rcases hb i with hz | ⟨_, _, hu⟩
    · rw [hz]; exact div_nonneg hτ hα.le
    · exact hu
  refine ⟨fun i => ⟨hnon i, ?_⟩, ?_, ?_⟩
  · rw [hval i]
    exact group_item_cap (hv i).le (hf i)
  · have hcap := (solve_feasible (show (0 : ℚ) ≤ d.K by positivity) hs).1
    rw [hw] at hcap
    convert hcap using 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hval i, (group_item_data (hf i)).1]
  · intro i
    rcases hb i with hz | ⟨hl, _, _⟩
    · exact Or.inl hz
    · refine Or.inr (fun j => ?_)
      have hh := (le_div_iff₀ hα).mp (hupper j)
      nlinarith

/-- The stored original profit is exactly the fractional-revenue acceptance test. -/
theorem solve_vector_revenue_test {n : ℕ} {d : Input n} {δ τ ρ θ capacity : ℚ}
    {bound : ℕ} {s : State}
    (hs : solve θ capacity bound (groups d δ τ ρ) = some s)
    (hnon : ∀ i : Fin (n+1), 0 ≤ stateVector s i) :
    ρ ≤ revenue d (stateVector s) ↔ ρ ≤ s.profit := by
  obtain ⟨f, hf, hval, _, hp⟩ := solve_vector_data hs
  have he : s.profit = (∑ i, d.r i * stateVector s i) - ρ * ∑ i : Fin (n+1), stateVector s i := by
    rw [hp]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [(group_item_data (hf i)).2.1, hval i]
    ring
  have hd : 0 < 1 + ∑ i : Fin (n+1), stateVector s i := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hnon i)
    linarith
  rw [revenue, le_div_iff₀ hd, he]
  constructor <;> intro h <;> nlinarith

theorem function_selection {n : ℕ} {d : Input n} (δ τ ρ θ : ℚ)
    (f : Fin (n+1) → Item) (hf : ∀ i, f i ∈ group d δ τ ρ i) :
    ∃ s, Selection θ (groups d δ τ ρ) s ∧
      s.weight = ∑ i, (f i).weight ∧ s.profit = ∑ i, (f i).profit := by
  let s := chooseState θ (List.finRange (n+1)) f
  refine ⟨s, chooseState_selection θ _ f _ (fun i _ => hf i), ?_, ?_⟩
  · have hh := (chooseState_sums θ (List.finRange (n+1)) f).2.1
    simpa only [← List.ofFn_eq_map, List.sum_ofFn] using hh
  · have hh := (chooseState_sums θ (List.finRange (n+1)) f).2.2
    simpa only [← List.ofFn_eq_map, List.sum_ofFn] using hh

/-- Removing options with nonpositive transformed profit preserves feasibility
and does not decrease the transformed objective. -/
theorem comparison_items {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    (y : Fin (n+1) → ℚ) (hy : Feasible d y)
    (hopt : ∀ i, y i ∈ Grids.productOptions τ δ d.α (d.v i)
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α))))
    (hv : ∀ i, 0 < d.v i) :
    ∃ f : Fin (n+1) → Item, (∀ i, f i ∈ group d δ τ ρ i) ∧
      (∑ i, (f i).weight) ≤ d.K ∧
      (∑ i, (d.r i - ρ) * y i) ≤ ∑ i, (f i).profit := by
  let f : Fin (n+1) → Item := fun i =>
    if 0 < (d.r i - ρ) * y i then ⟨y i, y i / d.v i, (d.r i - ρ) * y i⟩ else ⟨0,0,0⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i
    by_cases hp : 0 < (d.r i - ρ) * y i
    · have hg : y i ∈ Grids.geometricGrid τ δ (min (d.v i) (τ / d.α))
          (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α))) := by
        have hh := hopt i
        simp only [Grids.productOptions, List.mem_cons] at hh
        rcases hh with hz | hg
        · simp [hz] at hp
        · exact hg
      simp only [f, if_pos hp, group, List.mem_cons, List.mem_map, List.mem_filter,
        decide_eq_true_eq]
      exact Or.inr ⟨y i, ⟨hg, hp⟩, rfl⟩
    · simp [f, hp, group]
  · apply le_trans _ hy.2.1
    apply Finset.sum_le_sum
    intro i _
    dsimp [f]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hy.1 i).1 (hv i).le
  · apply Finset.sum_le_sum
    intro i _
    dsimp [f]
    split_ifs with hp
    · exact le_rfl
    · exact le_of_not_gt hp

/-- Revenue slack implies the corresponding transformed-profit slack. -/
theorem transformed_profit_slack {n : ℕ} {d : Input n} {δ ρ : ℚ}
    (y : Fin (n+1) → ℚ) (hy : ∀ i, 0 ≤ y i) (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hrev : (1 + 2 * δ) * ρ ≤ revenue d y) :
    (1 + 2 * δ) * ρ ≤ ∑ i, (d.r i - ρ) * y i := by
  have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => hy i)
  have hd : 0 < 1 + ∑ i, y i := by linarith
  have hh := (le_div_iff₀ hd).mp hrev
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hprod : 0 ≤ 2 * δ * ρ * ∑ i, y i := by positivity
  nlinarith

/-- The largest transformed-profit option can be selected alone: zero options
complete all other groups, and its exact weight is at most one. -/
theorem maximum_selection {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    (θ : ℚ) (hv : ∀ i, 0 < d.v i) (hK : 1 ≤ d.K)
    (hpmax : 0 < maxList (((groups d δ τ ρ).flatten).map Item.profit)) :
    ∃ s, Selection θ (groups d δ τ ρ) s ∧ s.weight ≤ d.K ∧
      maxList (((groups d δ τ ρ).flatten).map Item.profit) ≤ s.profit := by
  obtain ⟨g, hg, item, hi, he⟩ := maxProfit_attained d δ τ ρ hpmax
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  let f : Fin (n+1) → Item := fun j => if j = i then item else ⟨0,0,0⟩
  have hf : ∀ j, f j ∈ group d δ τ ρ j := by
    intro j
    by_cases hj : j = i
    · subst j; simpa [f] using hi
    · simp [f, hj, group]
  obtain ⟨s, hs, hw, hp⟩ := function_selection δ τ ρ θ f hf
  refine ⟨s, hs, ?_, ?_⟩
  · have hweight : item.weight ≤ 1 := group_item_weight_le_one (hv i) hi
    have hk : (1 : ℚ) ≤ d.K := by exact_mod_cast hK
    rw [hw]
    simpa [f, apply_ite] using hweight.trans hk
  · rw [hp]
    have hh : (∑ j, (f j).profit) = item.profit := by simp [f, apply_ite]
    rw [hh, he]

/-- The actual candidate routine succeeds whenever a feasible option vector has
revenue at least (1+2δ) times the requested grid revenue. -/
theorem candidateAt_success {n : ℕ} {d : Input n} {δ τ ρ : ℚ}
    (hvalid : Valid d) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2)
    (hτ : 0 ≤ τ) (hρ : 0 < ρ) (y : Fin (n+1) → ℚ) (hy : Feasible d y)
    (hopt : ∀ i, y i ∈ Grids.productOptions τ δ d.α (d.v i)
      (GridBounds.gridHorizon τ δ (min (d.v i) (τ / d.α))))
    (hrev : (1 + 2 * δ) * ρ ≤ revenue d y) :
    ∃ z, candidateAt d δ τ ρ = some z ∧ Feasible d z ∧ ρ ≤ revenue d z := by
  let gs := groups d δ τ ρ
  let pmax := maxList ((gs.flatten).map Item.profit)
  have hv : ∀ i, 0 < d.v i := fun i => (hvalid.1 i).2
  obtain ⟨f, hf, hfw, hfp⟩ := comparison_items y hy hopt hv
  have hslack := (transformed_profit_slack y (fun i => (hy.1 i).1) hδ.le hρ.le hrev).trans hfp
  have hfpPos : 0 < ∑ i, (f i).profit := lt_of_lt_of_le (by positivity) hslack
  have hpmax : 0 < pmax := by
    by_contra hn
    have hz : ∑ i, (f i).profit ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      have hm := maxProfit_bound d δ τ ρ (g := group d δ τ ρ i)
        (by simp [groups]) (hf i)
      exact hm.trans (le_of_not_gt hn)
    linarith
  let θ := δ * pmax / (n+1)
  obtain ⟨comparison, hc, hcw, hcp⟩ := function_selection δ τ ρ θ f hf
  obtain ⟨maximum, hm, hmw, hmp⟩ := maximum_selection θ hv hvalid.2.2.2.1 hpmax
  have hweights : ∀ g ∈ gs, ∀ item ∈ g, 0 ≤ item.weight := by
    intro g hg item hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact group_item_weight_nonneg (hv i) hτ hδ.le hi
  have hprofits : ∀ g ∈ gs, ∀ item ∈ g, 0 ≤ item.profit ∧ item.profit ≤ pmax := by
    intro g hg item hi
    have hu := maxProfit_bound d δ τ ρ hg hi
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
    exact ⟨(group_item_data hi).2.2.2, hu⟩
  have hlen : gs.length = n+1 := by simp [gs, groups]
  obtain ⟨s, hs, hsprofit⟩ := solve_passes_target hδ hδhalf hρ.le hpmax
    (show 0 < gs.length by omega) hweights hprofits
    (by simpa [hlen, θ] using hc) (by simpa [hcw] using hfw)
    (by simpa [hcp] using hslack)
    (by simpa [hlen, θ] using hm) hmw hmp
  have hs' : solve θ d.K ((n+1) * ⌈(n+1 : ℚ) / δ⌉₊) gs = some s := by
    simpa only [hlen, θ, Nat.cast_add, Nat.cast_one] using hs
  have hz := solve_vector_feasible hv hvalid.2.1 hτ hδ.le hs'
  refine ⟨stateVector s, ?_, hz, (solve_vector_revenue_test hs' (fun i => (hz.1 i).1)).2 hsprofit⟩
  simp only [candidateAt, gs, pmax, not_le.mpr hpmax, ↓reduceIte]
  change (match solve θ d.K ((n+1) * ⌈(n+1 : ℚ) / δ⌉₊) gs with
    | none => none
    | some s => if ρ ≤ s.profit then some (stateVector s) else none) = some (stateVector s)
  rw [hs']
  simp only [hsprofit, ↓reduceIte]

end BalancedAssortments.ApproximationCandidate
