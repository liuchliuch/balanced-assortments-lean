import BalancedAssortments.NPStackFields

/-! Finite Boolean-stack templates for CNF output fields. A field-register
operation preserves its source register and explicitly traverses/restores every
payload bit. Template dispatch is finite control, not an unbounded instruction. -/
namespace BalancedAssortments.NPCNF.StackTemplate
open NPStack
open NPStackFields (tagBits dataFields)

inductive Job (K : Type*) | bit (b : Bool) | field (k : K) deriving DecidableEq
inductive Stack (K : Type*) | reg (k : K) | scratch | output deriving DecidableEq, Fintype
inductive State (K : Type*) (n : ℕ)
  | dispatch (pc : Fin (n+1))
  | scan (k : K) (next : Fin (n+1))
  | save (k : K) (next : Fin (n+1)) (b : Bool)
  | delimiter (k : K) (next : Fin (n+1))
  | restore (k : K) (next : Fin (n+1))
  | putReg (k : K) (next : Fin (n+1)) (b : Bool)
  | putOut (k : K) (next : Fin (n+1)) (b : Bool)
  | putTag (k : K) (next : Fin (n+1))
  deriving DecidableEq, Fintype

variable {K : Type*} [DecidableEq K]
def advance {n : ℕ} (i : Fin (n+1)) : Fin (n+1) := ⟨min (i.val+1) n,by omega⟩

def program (jobs : List (Job K)) (inputKey : K) : Program (Stack K) (State K jobs.length) where
  start := .dispatch 0
  inputStack := .reg inputKey
  outputStack := .output
  code
    | .dispatch i => match jobs[i.val]? with
      | none => .halt true
      | some (.bit b) => .push .output b (.dispatch (advance i))
      | some (.field k) => .jump (.scan k (advance i))
    | .scan k q => .pop (.reg k) (.delimiter k q) (.save k q false) (.save k q true)
    | .save k q b => .push .scratch b (.scan k q)
    | .delimiter k q => .push .output false (.restore k q)
    | .restore k q => .pop .scratch (.dispatch q) (.putReg k q false) (.putReg k q true)
    | .putReg k q b => .push (.reg k) b (.putOut k q b)
    | .putOut k q b => .push .output b (.putTag k q)
    | .putTag k q => .push .output true (.restore k q)

def store (regs : K → List Bool) (scratch out : List Bool) : Stack K → List Bool
  | .reg k => regs k
  | .scratch => scratch
  | .output => out

def cfg {n : ℕ} (q : State K n) (regs : K → List Bool) (scratch out : List Bool) : Config (Stack K) (State K n) :=
  ⟨q,store regs scratch out⟩

@[simp] lemma update_reg (regs : K → List Bool) (scratch out : List Bool) (k : K) (xs : List Bool) :
    Function.update (store regs scratch out) (.reg k) xs=store (Function.update regs k xs) scratch out := by
  funext j; cases j with
  | reg j => by_cases h : j=k <;> simp [store,Function.update_apply,h]
  | scratch => simp [store]
  | output => simp [store]
@[simp] lemma update_scratch (regs : K → List Bool) (s o x : List Bool) :
    Function.update (store regs s o) .scratch x=store regs x o := by funext j;cases j <;> simp [store]
@[simp] lemma update_output (regs : K → List Bool) (s o x : List Bool) :
    Function.update (store regs s o) .output x=store regs s x := by funext j;cases j <;> simp [store]

lemma scan_run (jobs : List (Job K)) (inputKey k : K) (q : Fin (jobs.length+1))
    (regs : K → List Bool) (xs scratch out : List Bool) :
    Run (program jobs inputKey) (2*xs.length+1)
      (cfg (.scan k q) (Function.update regs k xs) scratch out)
      (cfg (.delimiter k q) (Function.update regs k []) (xs.reverse++scratch) out) := by
  induction xs generalizing scratch with
  | nil => apply Run.one; simp [Step,successors,program,cfg,store]
  | cons b bs ih =>
    have h1 : Step (program jobs inputKey)
        (cfg (.scan k q) (Function.update regs k (b::bs)) scratch out)
        (cfg (.save k q b) (Function.update regs k bs) scratch out) := by
      cases b <;> simp [Step,successors,program,cfg,store]
    have h2 : Step (program jobs inputKey)
        (cfg (.save k q b) (Function.update regs k bs) scratch out)
        (cfg (.scan k q) (Function.update regs k bs) (b::scratch) out) := by
      simp [Step,successors,program,cfg,store]
    have hh := Run.succ h1 (Run.succ h2 (ih (b::scratch)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

lemma restore_run (jobs : List (Job K)) (inputKey k : K) (q : Fin (jobs.length+1))
    (regs : K → List Bool) (xs scratch out : List Bool) :
    Run (program jobs inputKey) (4*scratch.length+1)
      (cfg (.restore k q) (Function.update regs k xs) scratch out)
      (cfg (.dispatch q) (Function.update regs k (scratch.reverse++xs)) []
        (tagBits scratch.reverse++out)) := by
  induction scratch generalizing xs out with
  | nil => apply Run.one; simp [Step,successors,program,cfg,store,tagBits]
  | cons b bs ih =>
    have h1 : Step (program jobs inputKey)
        (cfg (.restore k q) (Function.update regs k xs) (b::bs) out)
        (cfg (.putReg k q b) (Function.update regs k xs) bs out) := by
      cases b <;> simp [Step,successors,program,cfg,store]
    have h2 : Step (program jobs inputKey)
        (cfg (.putReg k q b) (Function.update regs k xs) bs out)
        (cfg (.putOut k q b) (Function.update regs k (b::xs)) bs out) := by
      simp [Step,successors,program,cfg,store]
    have h3 : Step (program jobs inputKey)
        (cfg (.putOut k q b) (Function.update regs k (b::xs)) bs out)
        (cfg (.putTag k q) (Function.update regs k (b::xs)) bs (b::out)) := by
      simp [Step,successors,program,cfg,store]
    have h4 : Step (program jobs inputKey)
        (cfg (.putTag k q) (Function.update regs k (b::xs)) bs (b::out))
        (cfg (.restore k q) (Function.update regs k (b::xs)) bs (true::b::out)) := by
      simp [Step,successors,program,cfg,store]
    have hh := Run.succ h1 (Run.succ h2 (Run.succ h3 (Run.succ h4 (ih (b::xs) (true::b::out)))))
    simpa [tagBits,List.reverse_cons,List.flatMap_append,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

/-- Copy a complete tagged field while preserving its source bit-for-bit. -/
theorem field_run (jobs : List (Job K)) (inputKey k : K) (q : Fin (jobs.length+1))
    (regs : K → List Bool) (out : List Bool) :
    Run (program jobs inputKey) (6*(regs k).length+3)
      (cfg (.scan k q) regs [] out)
      (cfg (.dispatch q) regs [] (tagBits (regs k)++false::out)) := by
  have h1 := scan_run jobs inputKey k q regs (regs k) [] out
  simp only [Function.update_eq_self,List.append_nil] at h1
  have h2 : Step (program jobs inputKey)
      (cfg (.delimiter k q) (Function.update regs k []) (regs k).reverse out)
      (cfg (.restore k q) (Function.update regs k []) (regs k).reverse (false::out)) := by
    simp [Step,successors,program,cfg,store]
  have hh := h1.trans (Run.succ h2 (restore_run jobs inputKey k q regs [] (regs k).reverse (false::out)))
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil,Function.update_eq_self] at hh
  convert hh using 1 <;> omega

end BalancedAssortments.NPCNF.StackTemplate
