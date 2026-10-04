import BalancedAssortments.NPStackSourceItem

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexityTimeReduction
open FPTASCostProgram (serializeBits)

def itemWire (b a price : List Bool) : List Bool :=
  serializeBits price++serializeBits []++serializeBits [true]++serializeBits b++serializeBits []++serializeBits a

lemma wire_nat (n : ℕ) : serializeBits n.bits=ComplexityEncoding.encodeNat n := by
  simp [serializeBits,ComplexityEncoding.encodeNat,Nat.size_eq_bits_len]

lemma itemWire_nat (B a : ℕ) : itemWire B.bits a.bits (3*B+a).bits=
    ComplexityEncoding.encodeFields (ComplexitySourceModel.itemNatFields B a) := by
  simp [itemWire,ComplexitySourceModel.itemNatFields,ComplexityEncoding.encodeFields,wire_nat,
    ComplexityEncoding.encodeNat,serializeBits,Nat.size_eq_bits_len,List.append_assoc]

theorem emit_item_run (wi wo b a tr qu ct pr : List Bool) :
    Run program (7*a.length+12*b.length+7*pr.length+48)
      (cfg .emitItemDen (store wi wo b a tr qu ct pr [] [] []))
      (cfg (.probe true) (stable wi (itemWire b a pr++wo) b tr qu ct)) := by
  let o1 := serializeBits a++wo
  let o2 := serializeBits []++o1
  let o3 := serializeBits b++o2
  let o4 := serializeBits [true]++o3
  let o5 := serializeBits []++o4
  have h1 : Run program (7*a.length+6)
      (cfg .emitItemDen (store wi wo b a tr qu ct pr [] [] []))
      (cfg .emitItemNegative (store wi o1 b [] tr qu ct pr [] [] [])) := by
    simpa [cfg,writes,o1] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitItemDen) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi wo b a tr qu ct pr [] [] []) rfl rfl
  have h2 : Run program 6
      (cfg .emitItemNegative (store wi o1 b [] tr qu ct pr [] [] []))
      (cfg .attractionCopy (store wi o2 b [] tr qu ct pr [] [] [])) := by
    simpa [cfg,writes,o2] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitItemNegative) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi o1 b [] tr qu ct pr [] [] []) rfl rfl
  have h3 : Run program (5*b.length+4)
      (cfg .attractionCopy (store wi o2 b [] tr qu ct pr [] [] []))
      (cfg .emitAttraction (store wi o2 b [] tr qu ct pr b [] [])) := by
    simpa [cfg] using copy_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.attractionCopy) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap])
      (store wi o2 b [] tr qu ct pr [] [] []) rfl
  have h4 : Run program (7*b.length+6)
      (cfg .emitAttraction (store wi o2 b [] tr qu ct pr b [] []))
      (cfg .priceDenOne (store wi o3 b [] tr qu ct pr [] [] [])) := by
    simpa [cfg,writes,o3] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitAttraction) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi o2 b [] tr qu ct pr b [] []) rfl rfl
  have h5 : Run program 1
      (cfg .priceDenOne (store wi o3 b [] tr qu ct pr [] [] []))
      (cfg .emitPriceDen (store wi o3 b [] tr qu ct pr [true] [] [])) := by
    simpa using Run.one (push_step .priceDenOne .emitPriceDen .temp1 true (store wi o3 b [] tr qu ct pr [] [] []) rfl)
  have h6 : Run program 13
      (cfg .emitPriceDen (store wi o3 b [] tr qu ct pr [true] [] []))
      (cfg .emitPriceNegative (store wi o4 b [] tr qu ct pr [] [] [])) := by
    simpa [cfg,writes,o4] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitPriceDen) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi o3 b [] tr qu ct pr [true] [] []) rfl rfl
  have h7 : Run program 6
      (cfg .emitPriceNegative (store wi o4 b [] tr qu ct pr [] [] []))
      (cfg .emitPrice (store wi o5 b [] tr qu ct pr [] [] [])) := by
    simpa [cfg,writes,o5] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitPriceNegative) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi o4 b [] tr qu ct pr [] [] []) rfl rfl
  have h8 : Run program (7*pr.length+6)
      (cfg .emitPrice (store wi o5 b [] tr qu ct pr [] [] []))
      (cfg (.probe true) (store wi (serializeBits pr++o5) b [] tr qu ct [] [] [] [])) := by
    simpa [cfg,writes] using encode_call table .readTarget Reg.wireIn Reg.wireOut (q := Stage.emitPrice) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi o5 b [] tr qu ct pr [] [] []) rfl rfl
  have hh := ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8
  convert hh using 1
  · omega
  · simp only [stable,itemWire,o1,o2,o3,o4,o5,List.append_assoc]

end BalancedAssortments.NPStackSourceReduction
