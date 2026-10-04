import BalancedAssortments.NPStackSourceVerifierProgramGuards
import BalancedAssortments.NPStackSourceBalanceSemantics
import BalancedAssortments.NPStackSourceVerifierBalanceData

namespace BalancedAssortments.NPStack.SourceVerifier.Whole
open NPStack DirectVerifier ComplexityTimeVerifier VerifierControl
open NPStackFields (dataFields)

lemma dataFields_injective : Function.Injective dataFields := by
  intro xs
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => simp [dataFields] at h
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp [dataFields] at h
    | cons y ys =>
      have hh := congrArg NPStackFieldData.readTagged h
      have hread (a : List Bool) (as : List (List Bool)) :
          NPStackFieldData.readTagged (dataFields (a::as))=some (a,dataFields as) := by
        simpa [dataFields,List.append_assoc] using NPStackFieldData.readTagged_field a (dataFields as)
      rw [hread,hread] at hh
      have he := Option.some.inj hh
      have hx := congrArg Prod.fst he
      have ht := congrArg Prod.snd he
      exact congrArg₂ List.cons hx (ih ht)

lemma trace_denominators (rows : List InputRow) (s : Registers) (balance : List Bool)
    (hp : (s .priceDen).2=[]) (hv : (s .attractionDen).2=[]) :
    ((traceEnd rows s balance).1 .priceDen).2=[] ∧ ((traceEnd rows s balance).1 .attractionDen).2=[] := by
  induction rows generalizing s balance with
  | nil => exact ⟨hp,hv⟩
  | cons r rows ih =>
    have hd := rowEffect_denominators s r.1
    exact ih (nextRegisters s r.1) (nextBalance s r.1 balance) hd.1 hd.2

def rowEnd (s : Fin 8→List Bool) (c : Fin 2→List Bool) (records : List NPStackSourcePairing.PairRecord) :=
  traceEnd (records.map decodeRow) (initialRegisters s c) []

def scalarStart (s : Fin 8→List Bool) (c : Fin 2→List Bool) (records : List NPStackSourcePairing.PairRecord) : Registers :=
  cleanRegisters (rowEnd s c records).1

def afterHeader (s : Registers) : Registers := (eval VerifierCommands.headerCommand s).2
def afterRank (s : Registers) : Registers := (eval VerifierCommands.rankCommand (afterHeader s)).2
def afterRevenue (s : Registers) : Registers := (eval VerifierCommands.revenueCommand (afterRank s)).2

def balanceTriples (records : List NPStackSourcePairing.PairRecord) : List Balance.Triple :=
  (records.map decodeRecord).reverse.map Balance.witnessTriple

lemma saved_balance_stream (s : Fin 8→List Bool) (c : Fin 2→List Bool) (records : List NPStackSourcePairing.PairRecord) :
    (rowEnd s c records).2=Balance.stream (balanceTriples records) := by
  unfold balanceTriples
  rw [Balance.witness_stream,rowEnd,trace_balance,List.append_nil]
  simp only [← List.map_reverse,List.flatMap_map,Function.comp_def,decodeRow]

/-- Every accepting whole verifier execution recovers the exact raw header
and paired-row grammar, concrete first-pass validity, all final guard booleans,
and the actual successful second-pass fold. -/
theorem accepted_conditions_full (source certificate : List Bool) {T : ℕ} {out : Config SourceVerifier.Stack (State Balance.LoopState)}
    (hr : Run concreteProgram T ⟨concreteProgram.start,Header.store source certificate (fun _=>[])⟩ out)
    (ha : accepts concreteProgram out) :
    ∃ s : Fin 8→List Bool,∃ c : Fin 2→List Bool,∃ records,
      source=dataFields (List.ofFn s++records.flatMap (fun r=>List.ofFn r.1)) ∧
      certificate=dataFields (List.ofFn c++records.flatMap (fun r=>List.ofFn r.2)) ∧
      RowsValid (records.map decodeRow) (initialRegisters s c) ∧
      (eval VerifierCommands.headerCommand (scalarStart s c records)).1=true ∧
      (eval VerifierCommands.rankCommand (afterHeader (scalarStart s c records))).1=true ∧
      (eval VerifierCommands.revenueCommand (afterRank (scalarStart s c records))).1=true ∧
      ∃ finish,Balance.loopValue (afterRevenue (scalarStart s c records)) (balanceTriples records)=some finish ∧
        out.stk=Header.store [] [] (Balance.stable finish []) := by
  obtain ⟨h,r,g₁,g₂,g₃,th,tr,t₁,t₂,t₃,tb,hhead,hrows,hg₁,hg₂,hg₃,hbal,ht⟩ := accepting_execution Balance.loopProgram hr ha
  obtain ⟨eh,hrh,hah,hph,_⟩ := hhead
  obtain ⟨s,c,sr,cr,hps,hpc,heh,hth⟩ := Header.accepting_result source certificate hrh hah
  have hh : h=Header.store sr cr (Header.preparedValues s c) := by
    funext k
    simpa only [heh] using hph k
  rw [hh,prepared_global_store] at hrows
  obtain ⟨er,hrr,har,hpr,_⟩ := hrows
  obtain ⟨records,finish,tx,hsr,hcr,htrace,her,htr⟩ :=
    NPStackSourcePairing.accepting_trace SourceVerifier.bodyProgram body_clearsRows sr cr
      (workspaceStore (initialRegisters s c) []) hrr har
  obtain ⟨hvalid,hfinish⟩ := trace_sound htrace (initialRegisters s c) [] rfl rfl rfl
  have hd := trace_denominators (records.map decodeRow) (initialRegisters s c) [] rfl rfl
  have hrstore : r=globalStore (scalarStart s c records) (rowEnd s c records).2 := by
    funext k
    have hh := hpr k
    rw [her,hfinish] at hh
    change r k=(NPStackSourcePairing.cfg (Q:=RowControl) .accept [] [] [] (fun _=>[])
      (workspaceStore (rowEnd s c records).1 (rowEnd s c records).2)).stk k at hh
    exact hh.trans (congrFun (rows_to_globalStore (rowEnd s c records).1 (rowEnd s c records).2 hd.1 hd.2) k)
  rw [hrstore] at hg₁
  obtain ⟨_,h₁,hg1⟩ := command_stage_sound VerifierCommands.headerCommand (scalarStart s c records) (rowEnd s c records).2 hg₁
  rw [hg1] at hg₂
  obtain ⟨_,h₂,hg2⟩ := command_stage_sound VerifierCommands.rankCommand (afterHeader (scalarStart s c records)) (rowEnd s c records).2 hg₂
  rw [hg2] at hg₃
  obtain ⟨_,h₃,hg3⟩ := command_stage_sound VerifierCommands.revenueCommand (afterRank (scalarStart s c records)) (rowEnd s c records).2 hg₃
  rw [hg3] at hbal
  obtain ⟨eb,hrb,hab,hpb,hfb⟩ := hbal
  have hclean : Clean (afterRevenue (scalarStart s c records)) := by
    apply revenue_clean
    apply rank_clean
    rw [afterHeader,header_state]
    exact cleanRegisters_clean _
  have hprojection := balance_projection (afterRevenue (scalarStart s c records)) (rowEnd s c records).2 hclean
  change Run Balance.loopProgram tb
    ⟨Balance.loopProgram.start,fun k=>globalStore (afterRevenue (scalarStart s c records)) (rowEnd s c records).2 (.body k)⟩ eb at hrb
  rw [hprojection,saved_balance_stream] at hrb
  obtain ⟨last,hlast,heblast,_⟩ := Balance.loop_accepting_result (afterRevenue (scalarStart s c records)) (balanceTriples records) hrb hab
  have hsraw := (NPStackSourceRecords.parseFixed_sound 8 source (List.ofFn s) sr hps).2
  have hcraw := (NPStackSourceRecords.parseFixed_sound 2 certificate (List.ofFn c) cr hpc).2
  have hout : out.stk=Header.store [] [] (Balance.stable last []) := by
    funext k
    cases k with
    | source => exact hfb _ (by intro old; simp)
    | certificate => exact hfb _ (by intro old; simp)
    | scratch => exact hfb _ (by intro old; simp)
    | body k => simpa only [heblast] using hpb k
  refine ⟨s,c,records,?_,?_,hvalid,h₁,h₂,h₃,last,hlast,hout⟩
  · rw [hsraw,←hsr]
    simp [dataFields,NPStackSourcePairing.sourceStream,List.flatMap_append]
  · rw [hcraw,←hcr]
    simp [dataFields,NPStackSourcePairing.certificateStream,List.flatMap_append]

theorem accepted_conditions (source certificate : List Bool) {T : ℕ} {out : Config SourceVerifier.Stack (State Balance.LoopState)}
    (hr : Run concreteProgram T ⟨concreteProgram.start,Header.store source certificate (fun _=>[])⟩ out)
    (ha : accepts concreteProgram out) :
    ∃ s : Fin 8→List Bool,∃ c : Fin 2→List Bool,∃ records,
      source=dataFields (List.ofFn s++records.flatMap (fun r=>List.ofFn r.1)) ∧
      certificate=dataFields (List.ofFn c++records.flatMap (fun r=>List.ofFn r.2)) ∧
      RowsValid (records.map decodeRow) (initialRegisters s c) ∧
      (eval VerifierCommands.headerCommand (scalarStart s c records)).1=true ∧
      (eval VerifierCommands.rankCommand (afterHeader (scalarStart s c records))).1=true ∧
      (eval VerifierCommands.revenueCommand (afterRank (scalarStart s c records))).1=true ∧
      ∃ finish,Balance.loopValue (afterRevenue (scalarStart s c records)) (balanceTriples records)=some finish := by
  obtain ⟨s,c,rs,hs,hc,hv,h₁,h₂,h₃,u,hu,_⟩ := accepted_conditions_full source certificate hr ha
  exact ⟨s,c,rs,hs,hc,hv,h₁,h₂,h₃,u,hu⟩

end BalancedAssortments.NPStack.SourceVerifier.Whole
