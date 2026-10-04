import BalancedAssortments.NPStackSourceClock

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace BalancedAssortments.NPStackSourceReduction
open NPStack NPStack.Macros ComplexityTimeBinary ComplexitySourceModel
open FPTASCostProgram (serializeBits)

/-- Total operational streaming loop, including malformed suffixes and zero
items. The global width/count invariant is derived from the original input. -/
theorem loop_run (B : ℕ) (done : List ℕ) (bits : List Bool) (L : ℕ)
    (hB : B.bits.length≤L) (hDone : ∀ a∈done,a.bits.length≤L)
    (hlen : done.length+bits.length≤L) :
    ∃ t≤loopBudget L bits.length,∃ out,
      Run program t (cfg (.probe (decide (done≠[])))
        (stable bits (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)) out ∧
      accepts program out ∧ out.stk .wireOut=loopSpec B done bits := by
  induction hn : bits.length using Nat.strong_induction_on generalizing done bits with
  | h n ih =>
    have hdlen : done.length≤L := by omega
    have hblen : bits.length≤L := by omega
    have hbody := bodyWire_bound B done L hB hDone
    have hbody' : (bodyWire B done).length≤6*L*(4*L+7) := by
      exact hbody.trans (Nat.mul_le_mul_right (4*L+7) (Nat.mul_le_mul_left 6 hdlen))
    cases bits with
    | nil =>
      by_cases he : done=[]
      · have hs : Step program (cfg (.probe (decide (done≠[])))
            (stable [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits))
            (cfg .badClear (stable [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)) := by
          simp [Step,successors,program,compile,code,table,cfg,stable,he]
        obtain ⟨out,hr,ha,hv⟩ := fixed_no_run (stable [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)
        simp only [stable,store_wireOut] at hr
        refine ⟨1+((bodyWire B done).length+1+fixedNoSource.length),?_,out,?_,ha,?_⟩
        · apply (unit_le_loop L n).trans' 
          have hh := reject_budget L
          omega
        · simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using Run.succ hs hr
        · simpa [loopSpec_nil,he] using hv
      · have hs : Step program (cfg (.probe (decide (done≠[])))
            (stable [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits))
            (cfg (.header 0) (stable [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)) := by
          simp [Step,successors,program,compile,code,table,cfg,stable,he]
        obtain ⟨t,ht,hr⟩ := header_run [] (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits
        have htr := triple_width B
        have hqu := quintuple_width B
        have hct := bits_length_le_self (done.length+1)
        refine ⟨t+1,?_,_,Run.succ hs hr,?_,?_⟩
        · apply (unit_le_loop L n).trans'
          have hh := header_budget L
          omega
        · simp [accepts,program,compile,code,table,cfg]
        · simp [cfg,stable,loopSpec_nil,he,sourceEncoding_parts]
    | cons bit bs =>
      have hne : bit::bs≠[] := by simp
      cases hp : (EncodingTime.parseField (bit::bs)).1 with
      | none =>
        have hs := probe_nonempty (decide (done≠[])) (bit::bs) (bodyWire B done)
          B.bits (3*B).bits (5*B).bits (done.length+1).bits hne
        obtain ⟨t,ht,after,hr,hout⟩ := read_failure .readItem .normalizeItem
          (stable (bit::bs) (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)
          rfl rfl rfl rfl hp
        simp only [stable,store_wireIn,store_wireOut] at ht hout
        obtain ⟨out,hno,ha,hv⟩ := fixed_no_run after
        rw [hout] at hno
        refine ⟨2+t+((bodyWire B done).length+1+fixedNoSource.length),?_,out,(hs.trans hr).trans hno,ha,?_⟩
        · apply (unit_le_loop L n).trans'
          have hh := reject_budget L
          omega
        · rw [loopSpec_bad B done (bit::bs) hne hp]
          exact hv
      | some parsed =>
        rcases parsed with ⟨payload,rest⟩
        have hwire := NPStackField.parseField_sound (bit::bs) payload rest hp
        have hlength : (bit::bs).length=2*payload.length+1+rest.length := by
          rw [hwire]
          simp [serializeBits]
          omega
        have hrest : rest.length<n := by omega
        have hpw : payload.length≤L := by omega
        have haw : (value payload).bits.length≤L := (canonical_width payload).trans hpw
        obtain ⟨tread,htread,hread⟩ := read_item_run (decide (done≠[])) payload rest (bodyWire B done)
          B.bits (3*B).bits (5*B).bits (done.length+1).bits
        rw [← hwire] at hread
        by_cases hpos : 0<value payload
        · have htest := positive_item_run rest (bodyWire B done) B.bits (value payload).bits
            (3*B).bits (5*B).bits (done.length+1).bits (bits_nonempty hpos)
          obtain ⟨twork,htwork,hwork⟩ := item_work_run B (value payload) done rest
          have hnewDone : ∀ a∈value payload::done,a.bits.length≤L := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact haw
            · exact hDone a ha
          have hnewLen : (value payload::done).length+rest.length≤L := by simp only [List.length_cons];omega
          obtain ⟨ttail,httail,out,htail,ha,hv⟩ := ih rest.length hrest (value payload::done) rest hnewDone hnewLen rfl
          have htail' : Run program ttail
              (cfg (.probe true) (stable rest (bodyWire B (value payload::done)) B.bits (3*B).bits (5*B).bits
                ((value payload::done).length+1).bits)) out := by simpa using htail
          have hstage : tread+2+twork≤unitBudget L := by
            apply (iteration_budget L).trans'
            omega
          refine ⟨(tread+2+twork)+ttail,?_,out,((hread.trans htest).trans hwork).trans htail',ha,?_⟩
          · exact loopBudget_step (by omega) hstage httail
          · rw [loopSpec_field B done (bit::bs) payload rest hne hp,if_pos hpos]
            exact hv
        · have hz : value payload=0 := by omega
          simp only [hz,Nat.zero_bits] at hread
          have htest := zero_item_run rest (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits
          obtain ⟨out,hno,ha,hv⟩ := fixed_no_run (stable rest (bodyWire B done) B.bits (3*B).bits (5*B).bits (done.length+1).bits)
          simp only [stable,store_wireOut] at hno
          refine ⟨tread+1+((bodyWire B done).length+1+fixedNoSource.length),?_,out,(hread.trans htest).trans hno,ha,?_⟩
          · apply (unit_le_loop L n).trans'
            have hh := reject_budget L
            omega
          · rw [loopSpec_field B done (bit::bs) payload rest hne hp,if_neg hpos]
            exact hv

end BalancedAssortments.NPStackSourceReduction
