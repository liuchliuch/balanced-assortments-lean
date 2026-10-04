import BalancedAssortments.NPStackSourceStore

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction

lemma triple_normalized (b : List Bool) : (normalize (addCarry b (false::b) false).1).1=(3*value b).bits := by
  rw [normalize_standard,triple_value]
lemma quintuple_normalized (b : List Bool) : (normalize (addCarry b (false::false::b) false).1).1=(5*value b).bits := by
  rw [normalize_standard,quintuple_value]

/-- Actual finite seed-construction block, beginning after the target positivity
check. The target stream and previously emitted output are untouched. -/
theorem triple_seed_run (wi wo b : List Bool) :
    ∃ cost≤200*(b.length+3),Run program cost
      (cfg .tripleLeft (stable wi wo b [] [] []))
      (cfg .quintupleLeft (stable wi wo b (3*value b).bits [] [])) := by
  have h1 : Run program (5*b.length+4)
      (cfg .tripleLeft (store wi wo b [] [] [] [] [] [] [] []))
      (cfg .tripleRight (store wi wo b [] [] [] [] [] b [] [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.tripleLeft) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b [] [] [] [] [] [] [] []) rfl
  have h2 : Run program (5*b.length+4)
      (cfg .tripleRight (store wi wo b [] [] [] [] [] b [] []))
      (cfg .tripleShift (store wi wo b [] [] [] [] [] b b [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.tripleRight) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b [] [] [] [] [] b [] []) rfl
  have h3 : Run program 1
      (cfg .tripleShift (store wi wo b [] [] [] [] [] b b []))
      (cfg .tripleAdd (store wi wo b [] [] [] [] [] b (false::b) [])) := by
    simpa using Run.one (push_step .tripleShift .tripleAdd .temp2 false (store wi wo b [] [] [] [] [] b b []) rfl)
  have h4 : Run program (5*max b.length (b.length+1)+8)
      (cfg .tripleAdd (store wi wo b [] [] [] [] [] b (false::b) []))
      (cfg .tripleNormalize (store wi wo b [] [] [] [] (addCarry b (false::b) false).1 [] [] [])) := by
    simpa [cfg,writes] using add_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.tripleAdd) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [addMap])
      (store wi wo b [] [] [] [] [] b (false::b) []) rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.tripleNormalize) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store wi wo b [] [] [] [] (addCarry b (false::b) false).1 [] [] []) rfl
  have h5 : Run program t
      (cfg .tripleNormalize (store wi wo b [] [] [] [] (addCarry b (false::b) false).1 [] [] []))
      (cfg .quintupleLeft (store wi wo b [] (3*value b).bits [] [] [] [] [] [])) := by
    simpa [cfg,writes,triple_normalized] using hr
  have hh := (((h1.trans h2).trans h3).trans h4).trans h5
  refine ⟨_,?_,hh⟩
  simp only [store_price,addCarry_length,List.length_cons] at ht
  omega

theorem quintuple_seed_run (wi wo b tr : List Bool) :
    ∃ cost≤200*(b.length+3),Run program cost
      (cfg .quintupleLeft (stable wi wo b tr [] []))
      (cfg .initializeCount (stable wi wo b tr (5*value b).bits [])) := by
  have h1 : Run program (5*b.length+4)
      (cfg .quintupleLeft (store wi wo b [] tr [] [] [] [] [] []))
      (cfg .quintupleRight (store wi wo b [] tr [] [] [] b [] [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.quintupleLeft) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b [] tr [] [] [] [] [] []) rfl
  have h2 : Run program (5*b.length+4)
      (cfg .quintupleRight (store wi wo b [] tr [] [] [] b [] []))
      (cfg .quintupleShiftOne (store wi wo b [] tr [] [] [] b b [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.quintupleRight) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b [] tr [] [] [] b [] []) rfl
  have h3 : Run program 1
      (cfg .quintupleShiftOne (store wi wo b [] tr [] [] [] b b []))
      (cfg .quintupleShiftTwo (store wi wo b [] tr [] [] [] b (false::b) [])) := by
    simpa using Run.one (push_step .quintupleShiftOne .quintupleShiftTwo .temp2 false (store wi wo b [] tr [] [] [] b b []) rfl)
  have h3' : Run program 1
      (cfg .quintupleShiftTwo (store wi wo b [] tr [] [] [] b (false::b) []))
      (cfg .quintupleAdd (store wi wo b [] tr [] [] [] b (false::false::b) [])) := by
    simpa using Run.one (push_step .quintupleShiftTwo .quintupleAdd .temp2 false (store wi wo b [] tr [] [] [] b (false::b) []) rfl)
  have h4 : Run program (5*max b.length (b.length+2)+8)
      (cfg .quintupleAdd (store wi wo b [] tr [] [] [] b (false::false::b) []))
      (cfg .quintupleNormalize (store wi wo b [] tr [] [] (addCarry b (false::false::b) false).1 [] [] [])) := by
    simpa [cfg,writes,Nat.add_assoc] using add_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.quintupleAdd) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [addMap])
      (store wi wo b [] tr [] [] [] b (false::false::b) []) rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.quintupleNormalize) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store wi wo b [] tr [] [] (addCarry b (false::false::b) false).1 [] [] []) rfl
  have h5 : Run program t
      (cfg .quintupleNormalize (store wi wo b [] tr [] [] (addCarry b (false::false::b) false).1 [] [] []))
      (cfg .initializeCount (store wi wo b [] tr (5*value b).bits [] [] [] [] [])) := by
    simpa [cfg,writes,quintuple_normalized] using hr
  have hh := ((((h1.trans h2).trans h3).trans h3').trans h4).trans h5
  refine ⟨_,?_,hh⟩
  simp only [store_price,addCarry_length,List.length_cons] at ht
  omega

/-- Complete binary 3B/5B preparation and anchor-count initialization. -/
theorem seeds_run (wi wo b : List Bool) :
    ∃ cost≤500*(b.length+3),Run program cost
      (cfg .tripleLeft (stable wi wo b [] [] []))
      (cfg (.probe false) (stable wi wo b (3*value b).bits (5*value b).bits [true])) := by
  obtain ⟨t1,ht1,h1⟩ := triple_seed_run wi wo b
  obtain ⟨t2,ht2,h2⟩ := quintuple_seed_run wi wo b (3*value b).bits
  have h3 : Run program 1 (cfg .initializeCount (stable wi wo b (3*value b).bits (5*value b).bits []))
      (cfg (.probe false) (stable wi wo b (3*value b).bits (5*value b).bits [true])) := by
    simpa [stable] using Run.one (push_step .initializeCount (.probe false) .count true
      (stable wi wo b (3*value b).bits (5*value b).bits []) rfl)
  exact ⟨t1+t2+1,by omega,(h1.trans h2).trans h3⟩

end BalancedAssortments.NPStackSourceReduction
