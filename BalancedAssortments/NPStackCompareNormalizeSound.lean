import BalancedAssortments.NPStackNormalize
import BalancedAssortments.NPStackDeterministic

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeReduction

theorem compare_noChoice : NoChoice compareProgram := by
  intro q a b
  cases q <;> simp [compareProgram]

theorem normalize_noChoice : NoChoice normalizeProgram := by
  intro q a b
  cases q <;> simp [normalizeProgram]

/-- Every halting execution has the certified comparator result and exact
linear transition count, not merely the exhibited execution. -/
theorem compare_halted_correct (xs ys zs : List Bool) {t : ℕ}
    {c : Config CompareStack CompareState} {b : Bool}
    (h : Run compareProgram t (compareConfig (.readLeft .eq) xs ys zs) c)
    (hc : compareProgram.code c.pc=.halt b) :
    t=2*max xs.length ys.length+3 ∧
      c=compareConfig .done [] [] (leBits xs ys::zs) := by
  exact h.halted_unique (noChoice_deterministic compare_noChoice)
    (compare_leBits_run xs ys zs) hc rfl

/-- Every halting normalization run has canonical output and the proved linear
bound. Input and scratch stacks are consumed and the output suffix is preserved. -/
theorem normalize_halted_correct (xs zs : List Bool) {t : ℕ}
    {c : Config CompareStack NormalizeState} {b : Bool}
    (h : Run normalizeProgram t (normalizeConfig .sourceRead xs [] zs) c)
    (hc : normalizeProgram.code c.pc=.halt b) :
    t≤4*xs.length+2 ∧
      c=normalizeConfig .done [] [] ((ComplexityTimeReduction.normalize xs).1++zs) := by
  obtain ⟨u,hu,hr⟩ := normalize_run xs zs
  have hh := h.halted_unique (noChoice_deterministic normalize_noChoice) hr hc rfl
  exact ⟨hh.1 ▸ hu,hh.2⟩

theorem compare_truth_run (xs ys zs : List Bool) :
    Run compareProgram (2*max xs.length ys.length+3)
      (compareConfig (.readLeft .eq) xs ys zs)
      (compareConfig .done [] [] (decide (value xs≤value ys)::zs)) := by
  have he : leBits xs ys=decide (value xs≤value ys) := by
    apply Bool.eq_iff_iff.mpr
    simpa using leBits_correct xs ys
  rw [← he]
  exact compare_leBits_run xs ys zs

theorem normalize_canonical_outputs (xs : List Bool) :
    OutputsIn normalizeProgram xs (value xs).bits (4*xs.length+2) := by
  simpa only [normalize_standard] using normalize_outputs xs

end BalancedAssortments.NPStack
