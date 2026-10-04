import BalancedAssortments.NPStackSourceVerifierBodyBound

namespace BalancedAssortments.NPStack.SourceVerifier
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl

lemma rowBudget_mono {A M B : ℕ} (h : A≤M) : rowBudget A B≤rowBudget M B := by
  have hh := Nat.mul_le_mul_left rowCoefficient (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2)
  unfold rowBudget
  omega

theorem trace_bounded (rows : List InputRow) (s : Registers) (balance : List Bool) {A B M : ℕ}
    (hBA : B≤A) (hAM : A+rows.length*(6*B+5)≤M)
    (ha : ∀ k,width (s k)≤A) (ho : width (s .one)≤B)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[])
    (hx : ∀ r∈rows,recordWidth r.1≤B ∧ r.2.length≤B) (hvalid : RowsValid rows s) :
    NPStackSourcePairing.BoundedBodyRuns bodyProgram (rowBudget M B)
      (rows.map (fun r=>pairRecord r.1 r.2)) (workspaceStore s balance)
      (workspaceStore (traceEnd rows s balance).1 (traceEnd rows s balance).2) := by
  induction rows generalizing s balance A with
  | nil => exact .nil _
  | cons r rows ih =>
    rcases r with ⟨x,m⟩
    rcases hvalid with ⟨hm,haccept,hrest⟩
    have hxm := hx (x,m) (by simp)
    obtain ⟨t,ht,hr⟩ := body_row_bounded (loadRecord s x) m balance x.active hBA
      (loadRecord_width s x hBA ha hxm.1) (loadRecord_fresh s x ho hxm.1) hxm.2 hm haccept
    rw [packed_record _ x m balance (loadRecord_holds s x),loadRecord_workspace s x balance hp hv,
      ←pairRecord_fields x m] at hr
    have hd:=rowEffect_denominators s x
    have hnext:=next_width s x hBA ha ho hxm.1
    have hone : width (nextRegisters s x .one)≤B := by rw [next_readonly s x .one (by simp)];exact ho
    have htail:=ih (nextRegisters s x) (nextBalance s x balance) (by omega)
      (by simp only [List.length_cons,Nat.add_mul] at hAM;omega) hnext hone hd.1 hd.2
      (by intro r hh;exact hx r (by simp [hh])) hrest
    refine .cons (ht.trans (rowBudget_mono (by simp only [List.length_cons] at hAM;omega))) hr ?_ htail
    simp [bodyProgram,ClearRows.finishProgram,ClearRows.clearDone_halts,Instr.rename]

lemma pair_overhead_bound (x : WitnessRecord) (mask : List Bool) {B : ℕ}
    (hx : recordWidth x≤B) (hm : mask.length≤B) :
    NPStackSourcePairing.recordOverhead (pairRecord x mask)≤45*B+32 := by
  rw [NPStackSourcePairing.recordOverhead_formula]
  simp [pairRecord,recordFields,List.ofFn_succ]
  unfold recordWidth ComplexityTimeFractions.width width at hx
  omega

lemma overhead_sum_bound (rows : List InputRow) {B : ℕ}
    (hx : ∀ r∈rows,recordWidth r.1≤B ∧ r.2.length≤B) :
    ((rows.map (fun r=>pairRecord r.1 r.2)).map NPStackSourcePairing.recordOverhead).sum≤rows.length*(45*B+32) := by
  induction rows with
  | nil => simp
  | cons r rows ih =>
    have h:=pair_overhead_bound r.1 r.2 (hx r (by simp)).1 (hx r (by simp)).2
    have ht:=ih (by intro x hh;exact hx x (by simp [hh]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega

def firstPassBudget (n A B : ℕ) : ℕ := n*(45*B+32+rowBudget (A+n*(6*B+5)) B)+2

theorem firstPass_bounded (rows : List InputRow) (s : Registers) (balance : List Bool) {A B : ℕ}
    (hBA : B≤A) (ha : ∀ k,width (s k)≤A) (ho : width (s .one)≤B)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[])
    (hx : ∀ r∈rows,recordWidth r.1≤B ∧ r.2.length≤B) (hvalid : RowsValid rows s) :
    ∃ t≤firstPassBudget rows.length A B,
      Run (NPStackSourcePairing.program bodyProgram) t
        (NPStackSourcePairing.cfg .probe (NPStackSourcePairing.sourceStream (rows.map (fun r=>pairRecord r.1 r.2)))
          (NPStackSourcePairing.certificateStream (rows.map (fun r=>pairRecord r.1 r.2))) [] (fun _=>[]) (workspaceStore s balance))
        (NPStackSourcePairing.cfg .accept [] [] [] (fun _=>[])
          (workspaceStore (traceEnd rows s balance).1 (traceEnd rows s balance).2)) := by
  have hh:=trace_bounded rows s balance hBA (le_refl _) ha ho hp hv hx hvalid
  obtain ⟨t,ht,hr⟩:=NPStackSourcePairing.bounded_loop bodyProgram _ hh
  refine ⟨t,?_,hr⟩
  have hs:=overhead_sum_bound rows hx
  simp only [List.length_map] at ht
  unfold firstPassBudget
  nlinarith

end BalancedAssortments.NPStack.SourceVerifier
