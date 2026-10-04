import BalancedAssortments.NPStackSourceEmit

namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary
open FPTASCostProgram (serializeBits)

def headerBits (i : Fin 14) (tr qu ct : List Bool) : List Bool :=
  match headerValue i with
  | .zero => [] | .one => [true] | .two => [false,true]
  | .triple => tr | .quintuple => qu | .count => ct

lemma headerBits_width (i : Fin 14) (tr qu ct : List Bool) :
    (headerBits i tr qu ct).length≤tr.length+qu.length+ct.length+2 := by
  unfold headerBits
  cases headerValue i <;> simp only [List.length_cons,List.length_nil] <;> omega

lemma header_prepare (i : Fin 14) (wi wo b tr qu ct : List Bool) :
    ∃ cost≤5*(headerBits i tr qu ct).length+4,Run program cost
      (cfg (.header i) (stable wi wo b tr qu ct))
      (cfg (.headerEncode i) (store wi wo b [] tr qu ct [] (headerBits i tr qu ct) [] [])) := by
  cases hh : headerValue i with
  | zero =>
    refine ⟨1,by simp [headerBits,hh],?_⟩
    apply Run.one
    simp [Step,successors,program,compile,code,table,cfg,stable,headerBits,hh]
  | one =>
    refine ⟨1,by simp [headerBits,hh],?_⟩
    simpa [stable,headerBits,hh] using Run.one (push_step (.header i) (.headerEncode i) .temp1 true
      (stable wi wo b tr qu ct) (by simp [table,hh]))
  | two =>
    refine ⟨2,by simp [headerBits,hh],?_⟩
    have h1 : Run program 1 (cfg (.header i) (stable wi wo b tr qu ct))
        (cfg (.headerTwo i) (store wi wo b [] tr qu ct [] [true] [] [])) := by
      simpa [stable] using Run.one (push_step (.header i) (.headerTwo i) .temp1 true
        (stable wi wo b tr qu ct) (by simp [table,hh]))
    have h2 : Run program 1 (cfg (.headerTwo i) (store wi wo b [] tr qu ct [] [true] [] []))
        (cfg (.headerEncode i) (store wi wo b [] tr qu ct [] [false,true] [] [])) := by
      simpa using Run.one (push_step (.headerTwo i) (.headerEncode i) .temp1 false
        (store wi wo b [] tr qu ct [] [true] [] []) rfl)
    simpa [headerBits,hh] using h1.trans h2
  | triple =>
    refine ⟨5*tr.length+4,by simp [headerBits,hh],?_⟩
    simpa [cfg,stable,headerBits,hh] using copy_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.header i) (s := Reg.triple) (w := Reg.temp2) (t := Reg.temp1) (next := Stage.headerEncode i) (by simp [table,hh])
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap]) (stable wi wo b tr qu ct) rfl
  | quintuple =>
    refine ⟨5*qu.length+4,by simp [headerBits,hh],?_⟩
    simpa [cfg,stable,headerBits,hh] using copy_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.header i) (s := Reg.quintuple) (w := Reg.temp2) (t := Reg.temp1) (next := Stage.headerEncode i) (by simp [table,hh])
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap]) (stable wi wo b tr qu ct) rfl
  | count =>
    refine ⟨5*ct.length+4,by simp [headerBits,hh],?_⟩
    simpa [cfg,stable,headerBits,hh] using copy_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.header i) (s := Reg.count) (w := Reg.temp2) (t := Reg.temp1) (next := Stage.headerEncode i) (by simp [table,hh])
      (by intro x y h;cases x <;> cases y <;> simp_all [copyMap]) (stable wi wo b tr qu ct) rfl

lemma header_step (i : Fin 14) (wi wo b tr qu ct : List Bool) :
    ∃ cost≤20*(headerBits i tr qu ct).length+20,Run program cost
      (cfg (.header i) (stable wi wo b tr qu ct))
      (cfg (afterHeader i) (stable wi (serializeBits (headerBits i tr qu ct)++wo) b tr qu ct)) := by
  obtain ⟨t,ht,hr⟩ := header_prepare i wi wo b tr qu ct
  have he : Run program (7*(headerBits i tr qu ct).length+6)
      (cfg (.headerEncode i) (store wi wo b [] tr qu ct [] (headerBits i tr qu ct) [] []))
      (cfg (afterHeader i) (stable wi (serializeBits (headerBits i tr qu ct)++wo) b tr qu ct)) := by
    simpa [cfg,writes,stable] using encode_call table .readTarget Reg.wireIn Reg.wireOut
      (q := Stage.headerEncode i) rfl
      (by intro x y h;cases x <;> cases y <;> simp_all [encodeMap])
      (store wi wo b [] tr qu ct [] (headerBits i tr qu ct) [] []) rfl rfl
  exact ⟨t+(7*(headerBits i tr qu ct).length+6),by omega,hr.trans he⟩

def headerWire (tr qu ct : List Bool) : List Bool :=
  [ct,[false,true],[true],[],[true],tr,[],[true],qu,[],[true],[true],[],[true]].flatMap serializeBits

theorem header_run (wi wo b tr qu ct : List Bool) :
    ∃ cost≤280*(tr.length+qu.length+ct.length+3),Run program cost
      (cfg (.header 0) (stable wi wo b tr qu ct))
      (cfg .done (stable wi (headerWire tr qu ct++wo) b tr qu ct)) := by
  let o1 := serializeBits (headerBits 0 tr qu ct)++wo
  obtain ⟨t0,ht0,h0⟩ := header_step 0 wi wo b tr qu ct
  norm_num only [afterHeader] at h0
  have hb0 : t0≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 0 tr qu ct
    omega
  let o2 := serializeBits (headerBits 1 tr qu ct)++o1
  obtain ⟨t1,ht1,h1⟩ := header_step 1 wi o1 b tr qu ct
  norm_num only [afterHeader] at h1
  have hb1 : t1≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 1 tr qu ct
    omega
  let o3 := serializeBits (headerBits 2 tr qu ct)++o2
  obtain ⟨t2,ht2,h2⟩ := header_step 2 wi o2 b tr qu ct
  norm_num only [afterHeader] at h2
  have hb2 : t2≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 2 tr qu ct
    omega
  let o4 := serializeBits (headerBits 3 tr qu ct)++o3
  obtain ⟨t3,ht3,h3⟩ := header_step 3 wi o3 b tr qu ct
  norm_num only [afterHeader] at h3
  have hb3 : t3≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 3 tr qu ct
    omega
  let o5 := serializeBits (headerBits 4 tr qu ct)++o4
  obtain ⟨t4,ht4,h4⟩ := header_step 4 wi o4 b tr qu ct
  norm_num only [afterHeader] at h4
  have hb4 : t4≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 4 tr qu ct
    omega
  let o6 := serializeBits (headerBits 5 tr qu ct)++o5
  obtain ⟨t5,ht5,h5⟩ := header_step 5 wi o5 b tr qu ct
  norm_num only [afterHeader] at h5
  have hb5 : t5≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 5 tr qu ct
    omega
  let o7 := serializeBits (headerBits 6 tr qu ct)++o6
  obtain ⟨t6,ht6,h6⟩ := header_step 6 wi o6 b tr qu ct
  norm_num only [afterHeader] at h6
  have hb6 : t6≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 6 tr qu ct
    omega
  let o8 := serializeBits (headerBits 7 tr qu ct)++o7
  obtain ⟨t7,ht7,h7⟩ := header_step 7 wi o7 b tr qu ct
  norm_num only [afterHeader] at h7
  have hb7 : t7≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 7 tr qu ct
    omega
  let o9 := serializeBits (headerBits 8 tr qu ct)++o8
  obtain ⟨t8,ht8,h8⟩ := header_step 8 wi o8 b tr qu ct
  norm_num only [afterHeader] at h8
  have hb8 : t8≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 8 tr qu ct
    omega
  let o10 := serializeBits (headerBits 9 tr qu ct)++o9
  obtain ⟨t9,ht9,h9⟩ := header_step 9 wi o9 b tr qu ct
  norm_num only [afterHeader] at h9
  have hb9 : t9≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 9 tr qu ct
    omega
  let o11 := serializeBits (headerBits 10 tr qu ct)++o10
  obtain ⟨t10,ht10,h10⟩ := header_step 10 wi o10 b tr qu ct
  norm_num only [afterHeader] at h10
  have hb10 : t10≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 10 tr qu ct
    omega
  let o12 := serializeBits (headerBits 11 tr qu ct)++o11
  obtain ⟨t11,ht11,h11⟩ := header_step 11 wi o11 b tr qu ct
  norm_num only [afterHeader] at h11
  have hb11 : t11≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 11 tr qu ct
    omega
  let o13 := serializeBits (headerBits 12 tr qu ct)++o12
  obtain ⟨t12,ht12,h12⟩ := header_step 12 wi o12 b tr qu ct
  norm_num only [afterHeader] at h12
  have hb12 : t12≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 12 tr qu ct
    omega
  let o14 := serializeBits (headerBits 13 tr qu ct)++o13
  obtain ⟨t13,ht13,h13⟩ := header_step 13 wi o13 b tr qu ct
  norm_num only [afterHeader] at h13
  have hb13 : t13≤20*(tr.length+qu.length+ct.length+3) := by
    have hw := headerBits_width 13 tr qu ct
    omega
  have hh := (((((((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9).trans h10).trans h11).trans h12).trans h13)
  refine ⟨t0+t1+t2+t3+t4+t5+t6+t7+t8+t9+t10+t11+t12+t13,by omega,?_⟩
  simpa [headerWire,headerBits,headerValue,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13,o14,List.append_assoc] using hh

lemma bits_two : (2:ℕ).bits=[false,true] := by
  simpa [Nat.bit_val] using Nat.bits_append_bit 1 false (by simp)

lemma headerWire_nat (B n : ℕ) : headerWire (3*B).bits (5*B).bits (n+1).bits=
    ComplexityEncoding.encodeFields [n+1,2,1,0,1,3*B,0,1,5*B,0,1,1,0,1] := by
  have h0 : serializeBits []=ComplexityEncoding.encodeNat 0 := by simpa using wire_nat 0
  have h1 : serializeBits [true]=ComplexityEncoding.encodeNat 1 := by simpa using wire_nat 1
  have h2 : serializeBits [false,true]=ComplexityEncoding.encodeNat 2 := by simpa [bits_two] using wire_nat 2
  simp [headerWire,ComplexityEncoding.encodeFields,wire_nat,h0,h1,h2,List.append_assoc]

def bodyWire (B : ℕ) (done : List ℕ) : List Bool :=
  ComplexityEncoding.encodeFields (done.flatMap (ComplexitySourceModel.itemNatFields B))

lemma sourceEncoding_parts (B : ℕ) (done : List ℕ) :
    ComplexitySourceModel.sourceEncoding B done=
      headerWire (3*B).bits (5*B).bits (done.length+1).bits++bodyWire B done := by
  rw [headerWire_nat]
  simp [ComplexitySourceModel.sourceEncoding,ComplexitySourceModel.sourceNatFields,
    bodyWire,ComplexityEncoding.encodeFields,List.flatMap_append]

lemma bodyWire_cons (B a : ℕ) (done : List ℕ) :
    bodyWire B (a::done)=itemWire B.bits a.bits (3*B+a).bits++bodyWire B done := by
  rw [itemWire_nat]
  simp [bodyWire,ComplexityEncoding.encodeFields,List.flatMap_append]

end BalancedAssortments.NPStackSourceReduction
