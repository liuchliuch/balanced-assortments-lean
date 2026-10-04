import BalancedAssortments.NPStackSourceSeeds

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction

lemma normalize_sum (x y : List Bool) : (normalize (addCarry x y false).1).1=(value x+value y).bits := by
  rw [normalize_standard,addCarry_value]
  simp

theorem count_increment_run (wi wo b a tr qu ct : List Bool) :
    ∃ cost≤100*(ct.length+2),Run program cost
      (cfg .countOne (store wi wo b a tr qu ct [] [] [] []))
      (cfg .priceLeft (store wi wo b a tr qu (value ct+1).bits [] [] [] [])) := by
  have h1 : Run program 1 (cfg .countOne (store wi wo b a tr qu ct [] [] [] []))
      (cfg .countAdd (store wi wo b a tr qu ct [] [true] [] [])) := by
    simpa using Run.one (push_step .countOne .countAdd .temp1 true (store wi wo b a tr qu ct [] [] [] []) rfl)
  have h2 : Run program (5*max ct.length 1+8)
      (cfg .countAdd (store wi wo b a tr qu ct [] [true] [] []))
      (cfg .countNormalize (store wi wo b a tr qu [] [] [] [] (addCarry ct [true] false).1)) := by
    simpa [cfg,writes] using add_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.countAdd) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [addMap])
      (store wi wo b a tr qu ct [] [true] [] []) rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.countNormalize) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store wi wo b a tr qu [] [] [] [] (addCarry ct [true] false).1) rfl
  have h3 : Run program t
      (cfg .countNormalize (store wi wo b a tr qu [] [] [] [] (addCarry ct [true] false).1))
      (cfg .priceLeft (store wi wo b a tr qu (value ct+1).bits [] [] [] [])) := by
    simpa [cfg,writes,normalize_sum,value] using hr
  refine ⟨1+(5*max ct.length 1+8)+t,?_,(h1.trans h2).trans h3⟩
  simp only [store_temp3,addCarry_length,List.length_cons,List.length_nil] at ht
  omega

theorem price_run (wi wo b a tr qu ct : List Bool) :
    ∃ cost≤100*(tr.length+a.length+2),Run program cost
      (cfg .priceLeft (store wi wo b a tr qu ct [] [] [] []))
      (cfg .emitItemDen (store wi wo b a tr qu ct (value tr+value a).bits [] [] [])) := by
  have h1 : Run program (5*tr.length+4)
      (cfg .priceLeft (store wi wo b a tr qu ct [] [] [] []))
      (cfg .priceRight (store wi wo b a tr qu ct [] tr [] [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.priceLeft) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b a tr qu ct [] [] [] []) rfl
  have h2 : Run program (5*a.length+4)
      (cfg .priceRight (store wi wo b a tr qu ct [] tr [] []))
      (cfg .priceAdd (store wi wo b a tr qu ct [] tr a [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.priceRight) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi wo b a tr qu ct [] tr [] []) rfl
  have h3 : Run program (5*max tr.length a.length+8)
      (cfg .priceAdd (store wi wo b a tr qu ct [] tr a []))
      (cfg .priceNormalize (store wi wo b a tr qu ct [] [] [] (addCarry tr a false).1)) := by
    simpa [cfg,writes] using add_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.priceAdd) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [addMap])
      (store wi wo b a tr qu ct [] tr a []) rfl rfl
  obtain ⟨t,ht,hr⟩ := normalize_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.priceNormalize) rfl
    (by intro x y h;cases x <;> cases y <;> simp_all [normalizeMap])
    (store wi wo b a tr qu ct [] [] [] (addCarry tr a false).1) rfl
  have h4 : Run program t
      (cfg .priceNormalize (store wi wo b a tr qu ct [] [] [] (addCarry tr a false).1))
      (cfg .emitItemDen (store wi wo b a tr qu ct (value tr+value a).bits [] [] [])) := by
    simpa [cfg,writes,normalize_sum] using hr
  refine ⟨_,?_,((h1.trans h2).trans h3).trans h4⟩
  simp only [store_temp3,addCarry_length] at ht
  omega

end BalancedAssortments.NPStackSourceReduction
