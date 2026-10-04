import BalancedAssortments.FixedSupportAlgorithmScalePieces
import BalancedAssortments.FixedSupportAlgorithmOrder

namespace BalancedAssortments.FixedSupportAlgorithm

noncomputable def realLine (f : Affine (𝕜 := ℚ)) : Affine (𝕜 := ℝ) := ((f.1 : ℝ), (f.2 : ℝ))

@[simp] theorem affineRoot_realLine (f : Affine (𝕜 := ℚ)) :
    affineRoot (realLine f) = ((affineRoot f : ℚ) : ℝ) := by simp [realLine, affineRoot]

def orderedLabel {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) (k : Fin n) : Fin n :=
  (scoreOrder r v q).get ⟨k.val, by simpa using k.isLt⟩

def orderedPrefix {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) (k : ℕ) : Finset (Fin n) :=
  ((scoreOrder r v q).take k).toFinset

theorem orderedPrefix_next {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) (k : Fin n) :
    orderedPrefix r v q (k.val + 1) = insert (orderedLabel r v q k) (orderedPrefix r v q k.val) := by
  have hk : k.val < (scoreOrder r v q).length := by simpa using k.isLt
  unfold orderedPrefix
  rw [List.take_succ_eq_append_getElem hk, List.toFinset_append]
  ext i
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.mem_union, Finset.mem_singleton, Finset.mem_insert, Finset.not_mem_empty, or_false]
  change (i ∈ orderedPrefix r v q k.val ∨ i = orderedLabel r v q k) ↔
    (i = orderedLabel r v q k ∨ i ∈ orderedPrefix r v q k.val)
  tauto

theorem orderedLabel_not_prefix {n : ℕ} (r v : Fin n → ℚ) (q : ℚ) (k : Fin n) :
    orderedLabel r v q k ∉ orderedPrefix r v q k.val := by
  have hk : k.val < (scoreOrder r v q).length := by simpa using k.isLt
  have hn : ((scoreOrder r v q).take (k.val + 1)).Nodup := (scoreOrder_nodup r v q).take
  rw [List.take_succ_eq_append_getElem hk] at hn
  have hh := (List.nodup_concat ((scoreOrder r v q).take k.val) ((scoreOrder r v q)[k.val])).mp
    (by simpa only [List.concat_eq_append] using hn)
  simpa [orderedLabel, orderedPrefix] using hh.1

private theorem affine_ext_two {f g : Affine (𝕜 := ℝ)} {a b : ℝ} (hab : a ≠ b)
    (ha : affineValue f a = affineValue g a) (hb : affineValue f b = affineValue g b) : f = g := by
  have hm : (f.1 - g.1) * (a - b) = 0 := by dsimp [affineValue] at *; nlinarith
  have hs : f.1 = g.1 := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (sub_ne_zero.mpr hab))
  apply Prod.ext hs
  dsimp [affineValue] at ha
  rw [hs] at ha
  linarith

/-- Consecutive prefix affine residuals differ by exactly the coordinate cap
piece. The proof uses two points and therefore avoids any unexplained symbolic
case split on whether the newly added coordinate is capped. -/
theorem prefixLine_step {n : ℕ} (r v : Fin n → ℚ) {α K q a b : ℚ}
    (hv : ∀ i, 0 < v i) (hα : 0 < α) (hab : a < b)
    (hcross : ∀ i, α * v i ≤ a ∨ b ≤ α * v i) (k : Fin n) :
    ((realLine (prefixLine v α K a (orderedPrefix r v q k.val))).1 -
        (realLine (capLine v α a (orderedLabel r v q k))).1,
      (realLine (prefixLine v α K a (orderedPrefix r v q k.val))).2 -
        (realLine (capLine v α a (orderedLabel r v q k))).2) =
      realLine (prefixLine v α K a (orderedPrefix r v q (k.val + 1))) := by
  have he (t : ℝ) (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) :
      affineValue
        ((realLine (prefixLine v α K a (orderedPrefix r v q k.val))).1 -
            (realLine (capLine v α a (orderedLabel r v q k))).1,
          (realLine (prefixLine v α K a (orderedPrefix r v q k.val))).2 -
            (realLine (capLine v α a (orderedLabel r v q k))).2) t =
        affineValue (realLine (prefixLine v α K a (orderedPrefix r v q (k.val + 1)))) t := by
    have hc := capLine_real v hv hα hcross ht (orderedLabel r v q k)
    have hp := prefixLine_real v (K := K) hv hα hcross ht (orderedPrefix r v q k.val)
    have hn := prefixLine_real v (K := K) hv hα hcross ht (orderedPrefix r v q (k.val + 1))
    change _ = affineValue (realLine _) t at hp hn
    change _ = affineValue (realLine _) t at hc
    rw [orderedPrefix_next, Finset.sum_insert (orderedLabel_not_prefix r v q k)] at hn
    rw [orderedPrefix_next]
    dsimp [affineValue] at *
    linarith
  apply affine_ext_two (a := (a : ℝ)) (b := (b : ℝ)) (by exact_mod_cast ne_of_lt hab)
  · exact he _ ⟨le_rfl, by exact_mod_cast hab.le⟩
  · exact he _ ⟨by exact_mod_cast hab.le, le_rfl⟩

/-- The transformed objective written in the exact closed-form greedy prefix
coordinates. A later recovery lemma identifies it with the executed policy. -/
noncomputable def prefixObjective {n : ℕ} (r v : Fin n → ℚ) (α K q : ℚ) (ρ t : ℝ) : ℝ :=
  t * (∑ i, ((r i : ℝ) - ρ)) + ∑ k : Fin n,
    realScore r v ρ (orderedLabel r v q k) *
      (if 0 < score r v q (orderedLabel r v q k) then
        min (FixedSupportKnapsack.cap (fun i => (v i : ℝ)) (α : ℝ) t (orderedLabel r v q k))
          (max (FixedSupportKnapsack.budget (fun i => (v i : ℝ)) (K : ℝ) t -
            ∑ i ∈ orderedPrefix r v q k.val, FixedSupportKnapsack.cap (fun j => (v j : ℝ)) (α : ℝ) t i) 0)
       else 0)

/-- On a cap interval, the actual prefix expression equals the abstract clipped
affine expression used by the finite endpoint maximum theorem. -/
theorem prefixObjective_affine_form {n : ℕ} (r v : Fin n → ℚ) {α K q a b : ℚ} (ρ : ℝ)
    (hv : ∀ i, 0 < v i) (hα : 0 < α)
    (hcross : ∀ i, α * v i ≤ a ∨ b ≤ α * v i)
    {t : ℝ} (ht : (a : ℝ) ≤ t ∧ t ≤ (b : ℝ)) :
    prefixObjective r v α K q ρ t = clippedObjective
      (∑ i, ((r i : ℝ) - ρ)) (fun k => realScore r v ρ (orderedLabel r v q k))
      (fun k => decide (0 < score r v q (orderedLabel r v q k)))
      (fun k => realLine (capLine v α a (orderedLabel r v q k)))
      (fun k => realLine (prefixLine v α K a (orderedPrefix r v q k.val))) t := by
  unfold prefixObjective clippedObjective
  rw [mul_comm t]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [capLine_real v hv hα hcross ht, prefixLine_real v (K := K) hv hα hcross ht]
  simp [realLine]

end BalancedAssortments.FixedSupportAlgorithm
