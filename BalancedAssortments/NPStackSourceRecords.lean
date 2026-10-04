import BalancedAssortments.NPStackFieldDataCorrect
import BalancedAssortments.NPStackEmbedding

/-! Fixed-arity tagged record extraction by an actual finite stack program.
The arity is part of the finite program, never a decoded input loop bound. -/
namespace BalancedAssortments.NPStackSourceRecords
open NPStack
open NPStackFields (tagBits dataFields)

inductive Stack (m : ℕ) | input | scratch | field (i : Fin m)
  deriving DecidableEq, Fintype
inductive State (m : ℕ) | field (i : Fin m) (q : NPStackFieldData.ReadState) | accept
  deriving DecidableEq, Fintype

def atIndex (m j : ℕ) : State m := if h : j < m then .field ⟨j,h⟩ .tag else .accept

def fieldStack {m : ℕ} (i : Fin m) : NPStackFieldData.Stack → Stack m
  | .input => .input
  | .scratch => .scratch
  | .output => .field i

lemma fieldStack_injective {m : ℕ} (i : Fin m) : Function.Injective (fieldStack i) := by
  intro a b h; cases a <;> cases b <;> simp_all [fieldStack]

def program (m : ℕ) : Program (Stack m) (State m) where
  start := atIndex m 0
  inputStack := .input
  outputStack := .input
  code
    | .accept => .halt true
    | .field i .accept => .jump (atIndex m (i.val+1))
    | .field _ .reject => .halt false
    | .field i q => (NPStackFieldData.readProgram.code q).rename (fieldStack i) (.field i)

def store {m : ℕ} (input scratch : List Bool) (fields : Fin m → List Bool) : Stack m → List Bool
  | .input => input
  | .scratch => scratch
  | .field i => fields i

def cfg {m : ℕ} (q : State m) (input scratch : List Bool) (fields : Fin m → List Bool) : Config (Stack m) (State m) :=
  ⟨q,store input scratch fields⟩

lemma field_code {m : ℕ} (i : Fin m) :
    CodeExtends NPStackFieldData.readProgram (program m) (fieldStack i) (.field i) := by
  intro q h
  cases q <;> simp_all [program,NPStackFieldData.readProgram]

lemma field_relocated {m : ℕ} (i : Fin m) (q : NPStackFieldData.ReadState)
    (input scratch : List Bool) (fields : Fin m → List Bool) :
    Relocated (fieldStack i) (.field i) (NPStackFieldData.readConfig q input scratch (fields i))
      (cfg (.field i q) input scratch fields) := by
  refine ⟨rfl,?_⟩
  intro k; cases k <;> rfl

lemma field_read {m : ℕ} (i : Fin m) (bits suffix : List Bool) (fields : Fin m → List Bool)
    (hi : fields i=[]) :
    Run (program m) (5*bits.length+2)
      (cfg (.field i .tag) (tagBits bits++false::suffix) [] fields)
      (cfg (.field i .accept) suffix [] (Function.update fields i bits)) := by
  have h := NPStackFieldData.read_field bits suffix []
  simp only [List.append_nil] at h
  have hrel : Relocated (fieldStack i) (.field i)
      (NPStackFieldData.readConfig .tag (tagBits bits++false::suffix) [] [])
      (cfg (.field i .tag) (tagBits bits++false::suffix) [] fields) := by
    simpa [hi] using field_relocated i .tag (tagBits bits++false::suffix) [] fields
  obtain ⟨d,hd,hr,hf⟩ := h.relocate (fieldStack i) (State.field i) (fieldStack_injective i) (field_code i) hrel
  have hrel' : Relocated (fieldStack i) (.field i) (NPStackFieldData.readConfig .accept suffix [] bits)
      (cfg (.field i .accept) suffix [] (Function.update fields i bits)) := by
    simpa using field_relocated i .accept suffix [] (Function.update fields i bits)
  have hframe : Frame (fieldStack i)
      (cfg (.field i .tag) (tagBits bits++false::suffix) [] fields)
      (cfg (.field i .accept) suffix [] (Function.update fields i bits)) := by
    intro k hk
    cases k with
    | input => exact (hk .input rfl).elim
    | scratch => exact (hk .scratch rfl).elim
    | field j =>
      have hn : j≠i := by intro he;subst j;exact hk .output rfl
      simp [cfg,store,Function.update_of_ne hn]
  have he := relocated_frame_unique (fieldStack i) (.field i) hr hrel' hf hframe
  simpa only [he] using hd

lemma field_next {m : ℕ} (i : Fin m) (input : List Bool) (fields : Fin m → List Bool) :
    Step (program m) (cfg (.field i .accept) input [] fields)
      (cfg (atIndex m (i.val+1)) input [] fields) := by
  simp [Step,successors,program,cfg]

def partialFields {m : ℕ} (fields : Fin m → List Bool) (j : ℕ) : Fin m → List Bool :=
  fun i => if i.val<j then fields i else []

def recordCost (fields : List (List Bool)) : ℕ := (fields.map (fun b => 5*b.length+3)).sum

lemma partial_update {m : ℕ} (fields : Fin m → List Bool) (j : Fin m) :
    Function.update (partialFields fields j.val) j (fields j)=partialFields fields (j.val+1) := by
  funext i
  by_cases hi : i=j
  · subst i; simp [partialFields]
  · have hn : i.val≠j.val := fun h => hi (Fin.ext h)
    simp [Function.update_of_ne hi,partialFields,show (i.val<j.val)=(i.val<j.val+1) from propext (by omega)]

lemma extract_from {m : ℕ} (fields : Fin m → List Bool) (suffix : List Bool)
    (k j : ℕ) (hjk : j+k=m) :
    Run (program m) (recordCost ((List.ofFn fields).drop j))
      (cfg (atIndex m j) (dataFields ((List.ofFn fields).drop j)++suffix) [] (partialFields fields j))
      (cfg .accept suffix [] fields) := by
  induction k generalizing j with
  | zero =>
    have hj : j=m := by omega
    subst j
    have hp : partialFields fields m=fields := by funext i;simp [partialFields,i.isLt]
    simp only [List.length_ofFn,List.drop_eq_nil_iff.mpr (show (List.ofFn fields).length ≤ m from by simp),
      recordCost,List.map_nil,List.sum_nil,dataFields,List.flatMap_nil,List.nil_append,hp]
    simpa [atIndex] using Run.zero (P:=program m) (cfg .accept suffix [] fields)
  | succ k ih =>
    have hj : j < m := by omega
    let i : Fin m := ⟨j,hj⟩
    have hdrop : (List.ofFn fields).drop j=fields i::(List.ofFn fields).drop (j+1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hj)]
      simp [i]
    have hread := field_read i (fields i) (dataFields ((List.ofFn fields).drop (j+1))++suffix)
      (partialFields fields j) (by simp [partialFields,i])
    have hnext := field_next i (dataFields ((List.ofFn fields).drop (j+1))++suffix)
      (Function.update (partialFields fields j) i (fields i))
    have hup : Function.update (partialFields fields j) i (fields i)=partialFields fields (j+1) := partial_update fields i
    rw [hup] at hread hnext
    have hr := hread.trans (Run.succ hnext (ih (j+1) (by omega)))
    convert hr using 1 <;> simp [hdrop,recordCost,dataFields,atIndex,hj,i,List.append_assoc] <;> omega

/-- Extract all fixed-arity fields, leaving the exact unconsumed suffix.
The cost is linear in total payload length and the fixed number of fields. -/
theorem extract_record {m : ℕ} (fields : Fin m → List Bool) (suffix : List Bool) :
    Run (program m) (recordCost (List.ofFn fields))
      (cfg (atIndex m 0) (dataFields (List.ofFn fields)++suffix) [] (fun _ => []))
      (cfg .accept suffix [] fields) := by
  simpa [partialFields] using extract_from fields suffix m 0 (by omega)

lemma recordCost_formula (fields : List (List Bool)) :
    recordCost fields=5*(fields.map List.length).sum+3*fields.length := by
  induction fields with
  | nil => rfl
  | cons f fs ih => simp [recordCost] at *;omega

end BalancedAssortments.NPStackSourceRecords
