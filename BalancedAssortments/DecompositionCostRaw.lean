import BalancedAssortments.DecompositionCostCertified

/-! The binary decomposition accepts arbitrary positive-denominator fractions;
canonical reduction by gcd is not required. -/
namespace BalancedAssortments.Decomposition.CostMachine
open ComplexityTimeBinary

private theorem get_mul_prod_erase (xs : List ℕ) (i : ℕ) (hi : i < xs.length) :
    xs[i] * (xs.eraseIdx i).prod = xs.prod := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      have hh := ih i (by simpa using hi)
      simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.prod_cons]
      nlinarith [hh]

def rawCounts {n : ℕ} (nums dens : Fin n → Bits) (i : Fin n) : ℕ :=
  value (nums i) * (((List.ofFn dens).eraseIdx i.val).map value).prod

theorem rawCounts_value {n : ℕ} (nums dens : Fin n → Bits) :
    ((initialBitsCounts (List.ofFn dens) 0 (List.ofFn nums)).1.map value) =
      List.ofFn (rawCounts nums dens) := by
  rw [initialBitsCounts_value]
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j < n := by simpa using hj'
    simp [List.getElem_mapIdx, rawCounts, hjn]

theorem rawGridValues {n : ℕ} (nums dens : Fin n → Bits)
    (hd : ∀ i, 0 < value (dens i)) :
    gridValues (value (productBits (List.ofFn dens)).1) (rawCounts nums dens) =
      fun i => (value (nums i) : ℚ) / (value (dens i) : ℚ) := by
  funext i
  have hD : 0 < ((List.ofFn dens).map value).prod := by
    simp only [List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_pos (fun j _ => hd j)
  have he := get_mul_prod_erase ((List.ofFn dens).map value) i.val (by simpa using i.isLt)
  simp only [List.getElem_map, List.getElem_ofFn, List.eraseIdx_map] at he
  have hp : 0 < (((List.ofFn dens).eraseIdx i.val).map value).prod := by
    by_contra hn
    have hz : (((List.ofFn dens).eraseIdx i.val).map value).prod = 0 := by omega
    rw [hz, mul_zero] at he
    omega
  simp only [gridValues, rawCounts, productBits_value, ← he, Nat.cast_mul]
  rw [mul_div_mul_right _ _ (by exact_mod_cast hp.ne')]

theorem raw_binaryGreedy_eq_greedy {n K : ℕ} (nums dens : Fin n → Bits)
    (hd : ∀ i, 0 < value (dens i))
    (h : Feasible K (fun i => (value (nums i) : ℚ) / (value (dens i) : ℚ))) :
    let out := binaryGreedy K (List.ofFn nums) (List.ofFn dens)
    interpretGrid (value out.1) (interpretBitAtoms (n := n) out.2.1) =
      greedy K (fun i => (value (nums i) : ℚ) / (value (dens i) : ℚ)) := by
  let D := value (productBits (List.ofFn dens)).1
  have hD : 0 < D := by
    dsimp [D]
    simp only [productBits_value, List.map_ofFn, List.prod_ofFn]
    exact Finset.prod_pos (fun j _ => hd j)
  have hz := rawGridValues nums dens hd
  have hf : Feasible K (gridValues D (rawCounts nums dens)) := by rw [hz]; exact h
  have hg := binaryGridAux_refines n K (productBits (List.ofFn dens)).1
    (initialBitsCounts (List.ofFn dens) 0 (List.ofFn nums)).1 (rawCounts nums dens)
    (rawCounts_value nums dens) hD hf
  have hr := gridAux_eq_greedyAux (D := D) n K D (rawCounts nums dens) hD hf
  rw [hz] at hr
  simp only [div_self (by exact_mod_cast hD.ne' : (D : ℚ) ≠ 0), one_mul] at hr
  have hid : (greedyAux n K (fun i => (value (nums i) : ℚ) / value (dens i))).map
      (fun b => (b.1, b.2)) = greedyAux n K (fun i => (value (nums i) : ℚ) / value (dens i)) := by
    simp
  rw [hid] at hr
  simpa only [binaryGreedy, List.length_ofFn, hg, greedy] using hr

/-- Arbitrary unreduced bit fractions feed the same exact decomposition without
an implicit gcd/canonicalization step. The bound uses their actual stored bits. -/
theorem raw_binary_sparse_decomposition {n L : ℕ} (ks : Bits) (xs ys : List Bits)
    (hx : xs.length = n) (hy : ys.length = n)
    (hd : ∀ i : Fin n, 0 < value (ys[i.val]?.getD []))
    (h : Feasible (value ks) (fun i : Fin n =>
      (value (xs[i.val]?.getD []) : ℚ) / (value (ys[i.val]?.getD []) : ℚ)))
    (hK : value ks ≤ n) (hL : bitVolume xs + bitVolume ys ≤ L) :
    let out := binaryGreedyRank ks xs ys
    let z := fun i : Fin n => (value (xs[i.val]?.getD []) : ℚ) / (value (ys[i.val]?.getD []) : ℚ)
    let p := interpretGrid (value out.1) (interpretBitAtoms (n := n) out.2.1)
    ValidDecomposition (value ks) z p ∧
      (∀ a ∈ p, 0 < a.1 ∧ a.2.card ≤ value ks) ∧
      out.2.1.length ≤ n+1 ∧
      out.2.2 ≤ 8192 * (n+1)^2 * (L+1)^2 + 3*n + 4*ks.length + 2 := by
  let nums : Fin n → Bits := fun i => xs[i.val]?.getD []
  let dens : Fin n → Bits := fun i => ys[i.val]?.getD []
  have hn : List.ofFn nums = xs := list_ofFn_getD xs [] hx
  have hde : List.ofFn dens = ys := list_ofFn_getD ys [] hy
  have he := raw_binaryGreedy_eq_greedy (K := value ks) nums dens hd h
  rw [hn, hde] at he
  have herr : interpretGrid (value (binaryGreedyRank ks xs ys).1)
      (interpretBitAtoms (n := n) (binaryGreedyRank ks xs ys).2.1) =
      greedy (value ks) (fun i => (value (nums i) : ℚ) / value (dens i)) := by
    simpa only [binaryGreedyRank, rankTokens_length] using he
  refine ⟨?_, ?_, ?_, binaryGreedyRank_bit_cost ks xs ys hx hy hK hL⟩
  · rw [herr]
    exact (greedy_correct h).1
  · rw [herr]
    intro a ha
    exact ⟨greedy_positive h a ha, greedy_legal h a ha⟩
  · have hh := (greedy_correct h).2
    rw [← herr] at hh
    simpa [interpretGrid, interpretBitAtoms] using hh

end BalancedAssortments.Decomposition.CostMachine
