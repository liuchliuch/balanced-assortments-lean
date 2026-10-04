import BalancedAssortments.NPStackSourceSpec

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction
open FPTASCostProgram (serializeBits)

lemma probe_nonempty (seen : Bool) (wi wo b tr qu ct : List Bool) (hne : wi≠[]) :
    Run program 2 (cfg (.probe seen) (stable wi wo b tr qu ct))
      (cfg .readItem (stable wi wo b tr qu ct)) := by
  cases wi with
  | nil => contradiction
  | cons bit bits =>
    have h1 : Step program (cfg (.probe seen) (stable (bit::bits) wo b tr qu ct))
        (cfg (.restoreInput seen bit) (stable bits wo b tr qu ct)) := by
      cases bit <;> simp [Step,successors,program,compile,code,table,cfg,stable]
    have h2 : Step program (cfg (.restoreInput seen bit) (stable bits wo b tr qu ct))
        (cfg .readItem (stable (bit::bits) wo b tr qu ct)) := by
      simpa [stable] using push_step (.restoreInput seen bit) .readItem .wireIn bit (stable bits wo b tr qu ct) rfl
    exact .succ h1 (.succ h2 (.zero _))

lemma read_item_run (seen : Bool) (payload rest wo b tr qu ct : List Bool) :
    ∃ cost≤11*payload.length+11,Run program cost
      (cfg (.probe seen) (stable (serializeBits payload++rest) wo b tr qu ct))
      (cfg .positiveItem (store rest wo b (value payload).bits tr qu ct [] [] [] [])) := by
  have hne : serializeBits payload++rest≠[] := by simp [serializeBits]
  have h1 := probe_nonempty seen (serializeBits payload++rest) wo b tr qu ct hne
  have h2 : Run program (7*payload.length+5)
      (cfg .readItem (stable (serializeBits payload++rest) wo b tr qu ct))
      (cfg .normalizeItem (store rest wo b [] tr qu ct [] payload [] [])) := by
    simpa [cfg,stable,writes] using read_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.readItem) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [readMap])
      (stable (serializeBits payload++rest) wo b tr qu ct) payload rest rfl rfl rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut
    (q := Stage.normalizeItem) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store rest wo b [] tr qu ct [] payload [] []) rfl
  have h3 : Run program t
      (cfg .normalizeItem (store rest wo b [] tr qu ct [] payload [] []))
      (cfg .positiveItem (store rest wo b (value payload).bits tr qu ct [] [] [] [])) := by
    simpa [cfg,writes,normalize_standard] using hr
  refine ⟨2+(7*payload.length+5)+t,?_,(h1.trans h2).trans h3⟩
  simp only [store_temp1] at ht
  omega

lemma positive_item_run (wi wo b a tr qu ct : List Bool) (hne : a≠[]) :
    Run program 2 (cfg .positiveItem (store wi wo b a tr qu ct [] [] [] []))
      (cfg .countOne (store wi wo b a tr qu ct [] [] [] [])) := by
  cases a with
  | nil => contradiction
  | cons bit bits =>
    have h1 : Step program (cfg .positiveItem (store wi wo b (bit::bits) tr qu ct [] [] [] []))
        (cfg (.restoreItem bit) (store wi wo b bits tr qu ct [] [] [] [])) := by
      cases bit <;> simp [Step,successors,program,compile,code,table,cfg]
    have h2 := push_step (.restoreItem bit) .countOne .item bit (store wi wo b bits tr qu ct [] [] [] []) rfl
    exact .succ h1 (.succ (by simpa using h2) (.zero _))

lemma zero_item_run (wi wo b tr qu ct : List Bool) :
    Run program 1 (cfg .positiveItem (store wi wo b [] tr qu ct [] [] [] []))
      (cfg .badClear (stable wi wo b tr qu ct)) := by
  apply Run.one
  simp [Step,successors,program,compile,code,table,cfg,stable]

lemma bits_nonempty {a : ℕ} (h : 0<a) : a.bits≠[] := by
  intro he
  have hv := value_bits a
  rw [he] at hv
  simp only [value] at hv
  omega

end BalancedAssortments.NPStackSourceReduction
