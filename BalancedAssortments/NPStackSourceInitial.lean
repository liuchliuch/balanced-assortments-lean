import BalancedAssortments.NPStackSourceLoop

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction
open FPTASCostProgram (serializeBits)

lemma initial_cfg (bits : List Bool) : initial program bits=cfg .readTarget (stable bits [] [] [] [] []) := by
  unfold initial program compile cfg stable
  congr 1
  funext k;cases k <;> simp [store]

lemma read_target_run (payload rest : List Bool) :
    ∃ cost≤11*payload.length+9,Run program cost
      (cfg .readTarget (stable (serializeBits payload++rest) [] [] [] [] []))
      (cfg .positiveTarget (stable rest [] (value payload).bits [] [] [])) := by
  have h1 : Run program (7*payload.length+5)
      (cfg .readTarget (stable (serializeBits payload++rest) [] [] [] [] []))
      (cfg .normalizeTarget (store rest [] [] [] [] [] [] [] payload [] [])) := by
    simpa [cfg,stable,writes] using read_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.readTarget) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [readMap])
      (stable (serializeBits payload++rest) [] [] [] [] []) payload rest rfl rfl rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut
    (q := Stage.normalizeTarget) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store rest [] [] [] [] [] [] [] payload [] []) rfl
  have h2 : Run program t (cfg .normalizeTarget (store rest [] [] [] [] [] [] [] payload [] []))
      (cfg .positiveTarget (stable rest [] (value payload).bits [] [] [])) := by
    simpa [cfg,stable,writes,normalize_standard] using hr
  refine ⟨7*payload.length+5+t,?_,h1.trans h2⟩
  simp only [store_temp1] at ht
  omega

lemma positive_target_run (rest b : List Bool) (hne : b≠[]) :
    Run program 2 (cfg .positiveTarget (stable rest [] b [] [] []))
      (cfg .tripleLeft (stable rest [] b [] [] [])) := by
  cases b with
  | nil => contradiction
  | cons bit bits =>
    have h1 : Step program (cfg .positiveTarget (stable rest [] (bit::bits) [] [] []))
        (cfg (.restoreTarget bit) (stable rest [] bits [] [] [])) := by
      cases bit <;> simp [Step,successors,program,compile,code,table,cfg,stable]
    have h2 := push_step (.restoreTarget bit) .tripleLeft .target bit (stable rest [] bits [] [] []) rfl
    exact .succ h1 (.succ (by simpa [stable] using h2) (.zero _))

lemma zero_target_run (rest : List Bool) :
    Run program 1 (cfg .positiveTarget (stable rest [] [] [] [] []))
      (cfg .badClear (stable rest [] [] [] [] [])) := by
  apply Run.one
  simp [Step,successors,program,compile,code,table,cfg,stable]

end BalancedAssortments.NPStackSourceReduction
