import BalancedAssortments.FixedSupportAlgorithmFinite
import BalancedAssortments.PolyhedralBasisCoefficientBounds

namespace BalancedAssortments.FixedSupportAlgorithm
open PolyhedralBasis

/-- Closure for a finite sum with a common bit-height bound. -/
theorem coeffBound_finset_sum {I : Type*} [DecidableEq I] (s : Finset I) (f : I → ℚ)
    {B : ℕ} (hf : ∀ i ∈ s, CoeffBound B (f i)) :
    CoeffBound (s.card * (B + 1)) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using CoeffBound.zero 0
  | @insert i s hi ih =>
    have hh := (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))
    rw [Finset.sum_insert hi]
    convert hh using 1 <;> simp [Finset.card_insert_of_notMem hi] <;> nlinarith

theorem coeffBound_list_sum (xs : List ℚ) {B : ℕ} (hx : ∀ x ∈ xs, CoeffBound B x) :
    CoeffBound (xs.length * (B + 1)) xs.sum := by
  induction xs with
  | nil => simpa using CoeffBound.zero 0
  | cons x xs ih =>
    have hh := (hx x (by simp)).add (ih (fun y hy => hx y (by simp [hy])))
    simpa [List.length_cons, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

theorem coeffBound_natCast {m n : ℕ} (hm : m ≤ n) : CoeffBound n (m : ℚ) := by
  have hp (k : ℕ) : k ≤ 2 ^ k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; have := Nat.two_pow_pos k; omega
  have hpI : (m : ℤ) ≤ (2 : ℤ) ^ n := by exact_mod_cast hm.trans (hp n)
  have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ n := one_le_pow₀ (by norm_num)
  simpa [CoeffBound] using And.intro hpI h1

def coefficientBudget (n B : ℕ) : ℕ := (n + 1) * (B + 1)

private theorem budget_basic (n B : ℕ) :
    B + 1 ≤ coefficientBudget n B ∧ n ≤ coefficientBudget n B ∧ 1 ≤ coefficientBudget n B := by
  dsimp [coefficientBudget]
  constructor
  · nlinarith
  · constructor <;> nlinarith

theorem inverseSum_coeffBound {n B : ℕ} (v : Fin n → ℚ) (hv : ∀ i, CoeffBound B (v i)) :
    CoeffBound (coefficientBudget n B) (inverseSum v) := by
  have hh := coeffBound_finset_sum Finset.univ (fun i => 1 / v i) (B := B)
    (fun i _ => by simpa only [one_div] using (hv i).inv)
  apply hh.mono
  simp [coefficientBudget]

theorem scaleUpper_coeffBound {n B : ℕ} (v : Fin n → ℚ) (K : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hK : CoeffBound B K) :
    CoeffBound (2 * coefficientBudget n B) (scaleUpper v K) := by
  have hb := budget_basic n B
  have hm := (insert (K / inverseSum v) (Finset.univ.image v)).min'_mem (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with he | hm
  · change scaleUpper v K = _ at he
    rw [he]
    exact (hK.div (inverseSum_coeffBound v hv)).mono (by omega)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    change v i = scaleUpper v K at hi
    rw [← hi]
    exact (hv i).mono (by omega)

theorem revenueUpper_coeffBound {n B : ℕ} (r : Fin n → ℚ)
    (hr : ∀ i, CoeffBound B (r i)) : CoeffBound B (revenueUpper r) := by
  have hm := (insert 0 (Finset.univ.image r)).max'_mem (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.mp hm with he | hm
  · change revenueUpper r = 0 at he
    rw [he]
    exact CoeffBound.zero B
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
    change r i = revenueUpper r at hi
    rw [← hi]
    exact hr i

theorem scoreLines_coeffBound {n B : ℕ} (r v : Fin n → ℚ)
    (hr : ∀ i, CoeffBound B (r i)) (hv : ∀ i, CoeffBound B (v i)) :
    ∀ f ∈ scoreLines r v, CoeffBound (4*B+1) f.1 ∧ CoeffBound (4*B+1) f.2 := by
  intro f hf
  rcases Finset.mem_union.mp hf with hf | hf
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨(hv i).neg.mono (by omega), ((hr i).mul (hv i)).mono (by omega)⟩
  · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨((hv j).sub (hv i)).mono (by omega),
      (((hr i).mul (hv i)).sub ((hr j).mul (hv j))).mono (by omega)⟩

theorem affineCritical_coeffBound {B : ℕ} (lo hi : ℚ) (F : Finset (Affine (𝕜 := ℚ)))
    (hlo : CoeffBound B lo) (hhi : CoeffBound B hi)
    (hF : ∀ f ∈ F, CoeffBound B f.1 ∧ CoeffBound B f.2) :
    ∀ c ∈ affineCritical lo hi F, CoeffBound (2*B) c := by
  intro c hc
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hlo.mono (by omega)
  rcases Finset.mem_insert.mp hc with rfl | hc
  · exact hhi.mono (by omega)
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc).1
  have hh := hF f (Finset.mem_filter.mp hf).1
  exact (hh.2.neg.div hh.1).mono (by omega)

theorem regimeSamples_coeffBound {B : ℕ} (C : Finset ℚ)
    (hC : ∀ c ∈ C, CoeffBound B c) :
    ∀ s ∈ regimeSamples C, CoeffBound (2*B+2) s := by
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact (hC s hs).mono (by omega)
  · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hs
    have h2 : CoeffBound 1 (2 : ℚ) := by norm_num [CoeffBound]
    exact (((hC a (Finset.mem_product.mp hab).1).add (hC b (Finset.mem_product.mp hab).2)).div h2).mono (by omega)

theorem scoreSamples_coeffBound {n B : ℕ} (r v : Fin n → ℚ)
    (hr : ∀ i, CoeffBound B (r i)) (hv : ∀ i, CoeffBound B (v i)) :
    ∀ q ∈ scoreSamples r v, CoeffBound (16*B+8) q := by
  have hc := affineCritical_coeffBound 0 (revenueUpper r) (scoreLines r v)
    (CoeffBound.zero (4*B+1)) ((revenueUpper_coeffBound r hr).mono (by omega))
    (scoreLines_coeffBound r v hr hv)
  intro q hq
  exact (regimeSamples_coeffBound _ hc q hq).mono (by omega)

theorem capCuts_coeffBound {n B : ℕ} (v : Fin n → ℚ) (α K : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α) (hK : CoeffBound B K) :
    ∀ a ∈ capCuts v α (scaleUpper v K), CoeffBound (2 * coefficientBudget n B) a := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact CoeffBound.zero _
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact scaleUpper_coeffBound v K hv hK
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ha).1
  exact (hα.mul (hv i)).mono (by have := budget_basic n B; omega)

theorem subsetInverseSum_coeffBound {n B : ℕ} (v : Fin n → ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (P : Finset (Fin n)) :
    CoeffBound (coefficientBudget n B) (∑ i ∈ P, 1 / v i) := by
  have hh := coeffBound_finset_sum P (fun i => 1 / v i) (B := B)
    (fun i _ => by simpa only [one_div] using (hv i).inv)
  apply hh.mono
  have hc : P.card ≤ n := by simpa using Finset.card_le_univ P
  dsimp [coefficientBudget]
  nlinarith

theorem prefixDenominator_coeffBound {n B : ℕ} (v : Fin n → ℚ) (α : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α) (P C : Finset (Fin n)) :
    CoeffBound (4 * coefficientBudget n B) (prefixDenominator v α P C) := by
  have h1 := subsetInverseSum_coeffBound v hv (Finset.univ \ P)
  have h2 := subsetInverseSum_coeffBound v hv (P \ C)
  have ha : CoeffBound B (1 / α) := by simpa only [one_div] using hα.inv
  exact (h1.add (ha.mul h2)).mono (by have := budget_basic n B; omega)

theorem prefixRoot_coeffBound {n B : ℕ} (v : Fin n → ℚ) (α K a : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α) (hK : CoeffBound B K)
    (P : Finset (Fin n)) : CoeffBound (8 * coefficientBudget n B) (prefixRoot v α K a P) := by
  have hc : (P ∩ cappedAt v α a).card ≤ n := by simpa using Finset.card_le_univ (P ∩ cappedAt v α a)
  have hn := hK.sub (coeffBound_natCast hc)
  have hd := prefixDenominator_coeffBound v α hv hα P (cappedAt v α a)
  exact (hn.div hd).mono (by have := budget_basic n B; omega)

theorem scaleSamples_coeffBound {n B : ℕ} (r v : Fin n → ℚ) (α K ρ : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α) (hK : CoeffBound B K) :
    ∀ t ∈ scaleSamples r v α K ρ, CoeffBound (8 * coefficientBudget n B) t := by
  intro t ht
  rcases Finset.mem_union.mp ht with ht | ht
  · exact (capCuts_coeffBound v α K hv hα hK t ht).mono (by omega)
  · obtain ⟨⟨a, k⟩, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
    exact prefixRoot_coeffBound v α K a hv hα hK _

theorem rationalCap_coeffBound {n B : ℕ} (v : Fin n → ℚ) (α t : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α)
    (ht : CoeffBound (8 * coefficientBudget n B) t) (i : Fin n) :
    CoeffBound (20 * coefficientBudget n B) (rationalCap v α t i) := by
  have hb := budget_basic n B
  have hdiv : CoeffBound (10 * coefficientBudget n B) (t / (α * v i)) :=
    (ht.div (hα.mul (hv i))).mono (by omega)
  have hmin := (CoeffBound.one (10 * coefficientBudget n B)).min hdiv
  have hother : CoeffBound (9 * coefficientBudget n B) (t / v i) := (ht.div (hv i)).mono (by omega)
  exact (hmin.sub hother).mono (by omega)

theorem rationalBudget_coeffBound {n B : ℕ} (v : Fin n → ℚ) (K t : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hK : CoeffBound B K)
    (ht : CoeffBound (8 * coefficientBudget n B) t) :
    CoeffBound (12 * coefficientBudget n B) (rationalBudget v K t) :=
  (hK.sub (ht.mul (inverseSum_coeffBound v hv))).mono (by have := budget_basic n B; omega)

/-- Every intermediate greedy budget/returned allocation is controlled by a
linear accumulation of capacity bit heights, not repeated doubling. -/
theorem solve_alloc_coeffBound (items : List ContinuousKnapsack.Item) {C BB : ℕ} {budget : ℚ}
    (hb : CoeffBound BB budget) (hc : ∀ i ∈ items, CoeffBound C i.cap) :
    ∀ y ∈ (ContinuousKnapsack.solve budget items).1,
      CoeffBound (BB + items.length * (C + 1)) y := by
  induction items generalizing budget BB with
  | nil => simp [ContinuousKnapsack.solve]
  | cons i items ih =>
    have hic := hc i (by simp)
    have hit := fun j hj => hc j (List.mem_cons_of_mem i hj)
    intro y hy
    simp only [ContinuousKnapsack.solve] at hy
    split_ifs at hy with hs hfill
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hb.mono (by simp)
      · have hy0 : y = 0 := (List.mem_replicate.mp hy).2
        rw [hy0]
        exact CoeffBound.zero _
    · rcases List.mem_cons.mp hy with rfl | hy
      · exact hic.mono (by simp only [List.length_cons]; nlinarith)
      · have hh := ih (hb.sub hic) hit y hy
        convert hh using 1 <;> simp only [List.length_cons] <;> nlinarith
    · have hy0 : y = 0 := (List.mem_replicate.mp hy).2
      rw [hy0]
      exact CoeffBound.zero _

theorem coeffBound_getD (xs : List ℚ) {B : ℕ} (hx : ∀ x ∈ xs, CoeffBound B x) (k : ℕ) :
    CoeffBound B (xs[k]?.getD 0) := by
  cases he : xs[k]? with
  | none => simp only [he, Option.getD_none]; exact CoeffBound.zero B
  | some x => simpa only [he, Option.getD_some] using hx x (List.mem_of_getElem? he)

theorem candidateVector_coeffBound {n B : ℕ} (r v : Fin n → ℚ) (α K : ℚ)
    (hv : ∀ i, CoeffBound B (v i)) (hα : CoeffBound B α) (hK : CoeffBound B K)
    {p : ℚ × ℚ} (hp : p ∈ candidates r v α K) :
    ∀ i, CoeffBound (64 * (n + 1) * coefficientBudget n B) (candidateVector r v α K p i) := by
  have hp' := (mem_candidates r v α K p).mp hp
  have ht := scaleSamples_coeffBound r v α K p.1 hv hα hK p.2 hp'.2
  have hb := rationalBudget_coeffBound v K p.2 hv hK ht
  have hc : ∀ i ∈ knapsackItems r v α p.1 p.2,
      CoeffBound (20 * coefficientBudget n B) i.cap := by
    intro j hj
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hj
    exact rationalCap_coeffBound v α p.2 hv hα ht i
  have ha := solve_alloc_coeffBound _ hb hc
  intro i
  have hy := coeffBound_getD _ ha ((scoreOrder r v p.1).idxOf i)
  have hh := ht.add ((hv i).mul hy)
  apply hh.mono
  simp only [knapsackItems, List.length_map, scoreOrder_length]
  have := budget_basic n B
  nlinarith

theorem revenue_coeffBound {n B W : ℕ} (r w : Fin n → ℚ)
    (hr : ∀ i, CoeffBound B (r i)) (hw : ∀ i, CoeffBound W (w i)) :
    CoeffBound (n * (B + W + 1) + n * (W + 1) + 1) (fractionalRevenue r w) := by
  have hn := coeffBound_finset_sum Finset.univ (fun i => r i * w i)
    (fun i _ => (hr i).mul (hw i))
  have hs := coeffBound_finset_sum Finset.univ w (fun i _ => hw i)
  have hd := (CoeffBound.one 0).add hs
  simpa [fractionalRevenue, Nat.add_assoc] using hn.div hd

/-- Canonical probability/revenue arithmetic throughout every enumerated
candidate has polynomial bit height. This theorem does not by itself assert a
running-time bound for the separate binary implementation. -/
theorem optimize_output_bit_bound {n B : ℕ} (r v : Fin n → ℚ) (α K : ℚ)
    (hr : ∀ i, CoeffBound B (r i)) (hv : ∀ i, CoeffBound B (v i))
    (hα : CoeffBound B α) (hK : CoeffBound B K) :
    (∀ i, (optimize r v α K i).num.natAbs.size ≤ 64*(n+1)*coefficientBudget n B+1 ∧
      (optimize r v α K i).den.size ≤ 64*(n+1)*coefficientBudget n B+1) ∧
    (fractionalRevenue r (optimize r v α K)).num.natAbs.size ≤
      256*(n+1)^2*coefficientBudget n B+1 ∧
    (fractionalRevenue r (optimize r v α K)).den.size ≤
      256*(n+1)^2*coefficientBudget n B+1 := by
  have hw := candidateVector_coeffBound r v α K hv hα hK (bestCandidate_mem r v α K)
  have hrev := revenue_coeffBound r (optimize r v α K) hr hw
  have hrev' : CoeffBound (256*(n+1)^2*coefficientBudget n B) (fractionalRevenue r (optimize r v α K)) :=
    hrev.mono (by have := budget_basic n B; nlinarith)
  exact ⟨fun i => (hw i).sizes, hrev'.sizes⟩

end BalancedAssortments.FixedSupportAlgorithm
