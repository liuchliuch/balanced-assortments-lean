import BalancedAssortments.NPStackMacroRuns

namespace BalancedAssortments.NPStack.Macros
open NPStack

/-- Proof-side notation for a finite sequence of register updates. This is not
an operational instruction; each use below is justified by a concrete Run. -/
def writes {K : Type*} [DecidableEq K] : (K → List Bool) → List (K × List Bool) → K → List Bool
  | s,[] => s
  | s,(k,bits)::rest => writes (Function.update s k bits) rest

lemma writes_project {A K : Type*} [DecidableEq A] [DecidableEq K]
    (fk : A → K) (hi : Function.Injective fk) (s : A → List Bool) (t : K → List Bool)
    (h : ∀ a,t (fk a)=s a) (bindings : List (A × List Bool)) :
    ∀ a,writes t (bindings.map (fun p => (fk p.1,p.2))) (fk a)=writes s bindings a := by
  induction bindings generalizing s t with
  | nil => exact h
  | cons b bs ih => exact ih _ _ (update_relocated fk hi s t h b.1 b.2)

lemma writes_frame {A K : Type*} [DecidableEq K] (fk : A → K) (s : K → List Bool)
    (bindings : List (A × List Bool)) :
    ∀ k,(∀ a,fk a≠k) → writes s (bindings.map (fun p => (fk p.1,p.2))) k=s k := by
  induction bindings generalizing s with
  | nil => intro _ _; rfl
  | cons b bs ih =>
    intro k hk
    exact (ih _ k hk).trans (Function.update_of_ne (Ne.symm (hk b.1)) _ _)

/-- Whole-call composition with a finite, explicit register-update postcondition. -/
theorem call_run_writes {A B K Q : Type*} [DecidableEq A] [DecidableEq K]
    {P : Program A B} {R : Program K Q} (fk : A → K) (fq : B → Q)
    (hi : Function.Injective fk) (hcode : CodeExtends P R fk fq)
    {t : ℕ} {c d : Config A B} (hr : Run P t c d)
    (entry exit : Q) (store : K → List Bool) (bindings : List (A × List Bool))
    (hentry : R.code entry=.jump (fq c.pc)) (hexit : R.code (fq d.pc)=.jump exit)
    (hbefore : ∀ k,store (fk k)=c.stk k) (hafter : writes c.stk bindings=d.stk) :
    Run R (t+2) ⟨entry,store⟩
      ⟨exit,writes store (bindings.map (fun p => (fk p.1,p.2)))⟩ := by
  apply call_run fk fq hi hcode hr entry exit store _ hentry hexit hbefore
  · intro k
    rw [writes_project fk hi c.stk store hbefore bindings k,hafter]
  · exact writes_frame fk store bindings

variable {K Q : Type*} [DecidableEq K]

theorem copy_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q next : Q} {s w t : K} (hm : m q=.copy s w t next)
    (hi : Function.Injective (copyMap s w t)) (store : K → List Bool) (hw : store w=[]) :
    Run (compile m start input output) (5*(store s).length+4) ⟨.main q,store⟩
      ⟨.main next,Function.update store t (store s++store t)⟩ := by
  have hr := copy_run (store s) (store t)
  have hh := call_run_writes (R := compile m start input output) (copyMap s w t) (fun st => Label.local q (.copy st)) hi
    (copy_extends m start input output hm) hr (.main q) (.main next) store
    [(CopyStack.target,store s++store t)]
    (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,copyConfig,addConfig]) (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,copyConfig,addConfig])
    (by intro k;cases k <;> simp [copyMap,copyConfig,copyStacks,hw])
    (by simp [writes,copyConfig])
  simpa [writes,copyMap] using hh

theorem add_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q next : Q} {a b w t : K} {carry : Bool} (hm : m q=.add a b w t carry next)
    (hi : Function.Injective (addMap a b w t)) (store : K → List Bool) (hw : store w=[]) (ht : store t=[]) :
    Run (compile m start input output) (5*max (store a).length (store b).length+8) ⟨.main q,store⟩
      ⟨.main next,writes store [(a,[]),(b,[]),(t,(ComplexityTimeBinary.addCarry (store a) (store b) carry).1)]⟩ := by
  have hr := add_run (store a) (store b) carry
  have hh := call_run_writes (R := compile m start input output) (addMap a b w t) (fun st => Label.local q (.add st)) hi
    (add_extends m start input output hm) hr (.main q) (.main next) store
    [(AddStack.left,[]),(AddStack.right,[]),(AddStack.output,(ComplexityTimeBinary.addCarry (store a) (store b) carry).1)]
    (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,copyConfig,addConfig]) (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,copyConfig,addConfig])
    (by intro k;cases k <;> simp [addMap,addConfig,fourStacks,hw,ht])
    (by simp [writes,addConfig])
  simpa [writes,addMap] using hh

theorem normalize_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q next : Q} {s w t : K} (hm : m q=.normalize s w t next)
    (hi : Function.Injective (normalizeMap s w t)) (store : K → List Bool) (hw : store w=[]) :
    ∃ cost≤4*(store s).length+4,
      Run (compile m start input output) cost ⟨.main q,store⟩
        ⟨.main next,writes store [(s,[]),(t,(ComplexityTimeReduction.normalize (store s)).1++store t)]⟩ := by
  obtain ⟨cost,hcost,hr⟩ := normalize_run (store s) (store t)
  refine ⟨cost+2,by omega,?_⟩
  have hh := call_run_writes (R := compile m start input output) (normalizeMap s w t)
    (fun st => Label.local q (.normalize st)) hi (normalize_extends m start input output hm)
    hr (.main q) (.main next) store
    [(CompareStack.left,[]),(CompareStack.result,(ComplexityTimeReduction.normalize (store s)).1++store t)]
    (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,normalizeConfig]) (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,normalizeConfig])
    (by intro k;cases k <;> simp [normalizeMap,normalizeConfig,compareStacks,hw])
    (by funext k;cases k <;> simp [writes,normalizeConfig,compareStacks,Function.update])
  simpa [writes,normalizeMap] using hh

theorem read_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q yes no : Q} {i c r o : K} (hm : m q=.read i c r o yes no)
    (hi : Function.Injective (readMap i c r o)) (store : K → List Bool)
    (payload rest : List Bool) (hin : store i=FPTASCostProgram.serializeBits payload++rest)
    (hc : store c=[]) (hr : store r=[]) (ho : store o=[]) :
    Run (compile m start input output) (7*payload.length+5) ⟨.main q,store⟩
      ⟨.main yes,writes store [(i,rest),(o,payload)]⟩ := by
  have hrun := NPStackField.field_run payload rest
  have hh := call_run_writes (R := compile m start input output) (readMap i c r o)
    (fun st => Label.local q (.read st)) hi (read_extends m start input output hm)
    hrun (.main q) (.main yes) store [(NPStackField.Stack.input,rest),(NPStackField.Stack.output,payload)]
    (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,NPStackField.cfg]) (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,NPStackField.cfg])
    (by intro k;cases k <;> simp [readMap,NPStackField.cfg,hin,hc,hr,ho])
    (by funext k;cases k <;> simp [writes,NPStackField.cfg,Function.update])
  simpa [writes,readMap] using hh

theorem encode_call (m : Q → Macro K Q) (start : Q) (input output : K)
    {q next : Q} {i r c o : K} (hm : m q=.encode i r c o next)
    (hi : Function.Injective (encodeMap i r c o)) (store : K → List Bool)
    (hr : store r=[]) (hc : store c=[]) :
    Run (compile m start input output) (7*(store i).length+6) ⟨.main q,store⟩
      ⟨.main next,writes store [(i,[]),(o,FPTASCostProgram.serializeBits (store i)++store o)]⟩ := by
  have hrun := NPStackFieldEncode.encode_field (store i) (store o)
  have hh := call_run_writes (R := compile m start input output) (encodeMap i r c o)
    (fun st => Label.local q (.encode st)) hi (encode_extends m start input output hm)
    hrun (.main q) (.main next) store
    [(NPStackFieldEncode.Stack.input,[]),(NPStackFieldEncode.Stack.output,FPTASCostProgram.serializeBits (store i)++store o)]
    (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,NPStackFieldEncode.cfg]) (by simp [compile,code,returnCode,copyProgram,addProgram,normalizeProgram,NPStackField.program,NPStackFieldEncode.program,hm,NPStackFieldEncode.cfg])
    (by intro k;cases k <;> simp [encodeMap,NPStackFieldEncode.cfg,NPStackFieldEncode.store,hr,hc])
    (by funext k;cases k <;> simp [writes,NPStackFieldEncode.cfg,NPStackFieldEncode.store,Function.update,FPTASCostProgram.serializeBits,List.append_assoc])
  simpa [writes,encodeMap] using hh

end BalancedAssortments.NPStack.Macros
