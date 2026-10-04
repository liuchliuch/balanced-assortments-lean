import BalancedAssortments.NPStackSourceRecords

namespace BalancedAssortments.NPStackSourceRecords
open NPStack
open NPStackFields (tagBits dataFields)
open NPStackFieldData (readTagged)

def parseFixed : ℕ → List Bool → Option (List (List Bool) × List Bool)
  | 0,input => some ([],input)
  | k+1,input => match readTagged input with
    | none => none
    | some (bits,suffix) => (parseFixed k suffix).map (fun p => (bits::p.1,p.2))

lemma parseFixed_sound (k : ℕ) (input : List Bool) (fields : List (List Bool)) (rest : List Bool)
    (h : parseFixed k input=some (fields,rest)) : fields.length=k ∧ input=dataFields fields++rest := by
  induction k generalizing input fields with
  | zero =>
    simp only [parseFixed,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩;simp [dataFields]
  | succ k ih =>
    cases hr : readTagged input with
    | none => simp [parseFixed,hr] at h
    | some p =>
      rcases p with ⟨bits,suffix⟩
      cases hp : parseFixed k suffix with
      | none => simp [parseFixed,hr,hp] at h
      | some p =>
        rcases p with ⟨fs,rs⟩
        simp [parseFixed,hr,hp] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨hlen,he⟩ := ih suffix fs hp
        exact ⟨by simp [hlen],by rw [NPStackFieldData.readTagged_sound input bits suffix hr,he];simp [dataFields,List.append_assoc]⟩

lemma parseFixed_data (fields : List (List Bool)) (rest : List Bool) :
    parseFixed fields.length (dataFields fields++rest)=some (fields,rest) := by
  induction fields with
  | nil => rfl
  | cons bits fs ih =>
    have he : dataFields (bits::fs)++rest=tagBits bits++false::(dataFields fs++rest) := by
      simp [dataFields,List.append_assoc]
    simp [he,parseFixed,NPStackFieldData.readTagged_field,ih]

lemma field_reject {m : ℕ} (i : Fin m) (input : List Bool) (fields : Fin m → List Bool)
    (hi : fields i=[]) (hbad : readTagged input=none) :
    ∃ t ≤ 3*input.length+2,∃ d,
      Run (program m) t (cfg (.field i .tag) input [] fields) d ∧ (program m).code d.pc=.halt false := by
  obtain ⟨t,ht,s,hr⟩ := NPStackFieldData.read_rejects input [] hbad
  have hrel : Relocated (fieldStack i) (State.field i)
      (NPStackFieldData.readConfig .tag input [] []) (cfg (.field i .tag) input [] fields) := by
    simpa [hi] using field_relocated i .tag input [] fields
  obtain ⟨d,hd,hh,_⟩ := hr.relocate (fieldStack i) (State.field i) (fieldStack_injective i) (field_code i) hrel
  refine ⟨t,ht,d,hd,?_⟩
  rw [hh.1]
  rfl

lemma reject_from {m : ℕ} (k j : ℕ) (hjk : j+k=m) (input : List Bool)
    (fields : Fin m → List Bool) (hf : ∀ i,j ≤ i.val → fields i=[])
    (hbad : parseFixed k input=none) :
    ∃ t ≤ k*(5*input.length+5),∃ d,
      Run (program m) t (cfg (atIndex m j) input [] fields) d ∧ (program m).code d.pc=.halt false := by
  induction k generalizing j input fields with
  | zero => simp [parseFixed] at hbad
  | succ k ih =>
    have hj : j < m := by omega
    let i : Fin m := ⟨j,hj⟩
    cases hp : readTagged input with
    | none =>
      obtain ⟨t,ht,d,hr,hd⟩ := field_reject i input fields (hf i le_rfl) hp
      refine ⟨t,?_,d,?_,hd⟩
      · nlinarith
      · simpa [atIndex,hj,i] using hr
    | some p =>
      rcases p with ⟨bits,suffix⟩
      have hb : parseFixed k suffix=none := by
        cases hh : parseFixed k suffix <;> simp [parseFixed,hp,hh] at hbad ⊢
      have hf' : ∀ a,j+1 ≤ a.val → (Function.update fields i bits) a=[] := by
        intro a ha
        have hn : a≠i := by intro he;subst a;dsimp [i] at ha;omega
        rw [Function.update_of_ne hn]
        exact hf a (by omega)
      obtain ⟨u,hu,d,hr,hd⟩ := ih (j+1) (by omega) suffix (Function.update fields i bits) hf' hb
      have h1 := field_read i bits suffix fields (hf i le_rfl)
      have h2 := field_next i suffix (Function.update fields i bits)
      have he := NPStackFieldData.readTagged_sound input bits suffix hp
      have hl : bits.length ≤ input.length ∧ suffix.length ≤ input.length := by
        rw [he];simp;omega
      refine ⟨(5*bits.length+2)+(u+1),?_,d,?_,hd⟩
      · nlinarith
      · have hh := h1.trans (Run.succ h2 hr)
        simpa [atIndex,hj,i,←he] using hh

theorem reject_malformed (m : ℕ) (input : List Bool) (hbad : parseFixed m input=none) :
    ∃ t ≤ m*(5*input.length+5),∃ d,
      Run (program m) t (cfg (atIndex m 0) input [] (fun _ => [])) d ∧ (program m).code d.pc=.halt false :=
  reject_from m 0 (by omega) input (fun _ => []) (by simp) hbad

lemma program_deterministic (m : ℕ) : Deterministic (program m) := by
  apply noChoice_deterministic
  intro q a b
  cases q with
  | accept => simp [program]
  | field i q => cases q <;> simp [program,NPStackFieldData.readProgram,Instr.rename]

/-- Complete all-input output semantics of the fixed-arity finite extractor. -/
theorem accepting_result (m : ℕ) (input : List Bool) {t : ℕ} {d : Config (Stack m) (State m)}
    (hr : Run (program m) t (cfg (atIndex m 0) input [] (fun _ => [])) d)
    (ha : accepts (program m) d) :
    ∃ fields : Fin m → List Bool,∃ rest,
      parseFixed m input=some (List.ofFn fields,rest) ∧
      d=cfg .accept rest [] fields ∧ t=recordCost (List.ofFn fields) := by
  cases hp : parseFixed m input with
  | none =>
    obtain ⟨u,_,c,hc,hh⟩ := reject_malformed m input hp
    exact False.elim (rejecting_run_excludes_acceptance (program_deterministic m) hc hh hr ha)
  | some p =>
    rcases p with ⟨fs,rest⟩
    obtain ⟨hlen,he⟩ := parseFixed_sound m input fs rest hp
    let fields : Fin m → List Bool := fun i => fs[i.val]'(by rw [hlen];exact i.isLt)
    have hfs : List.ofFn fields=fs := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i h1 h2
        simp [fields]
    have hc := extract_record fields rest
    rw [hfs,←he] at hc
    have hh := hc.halted_unique (program_deterministic m) hr rfl ha
    exact ⟨fields,rest,by simpa [hfs] using hp,hh.2.symm,by simpa [hfs] using hh.1.symm⟩

def fieldsOfList (m : ℕ) (fields : List (List Bool)) (h : fields.length=m) : Fin m → List Bool :=
  fun i => fields[i.val]'(by rw [h];exact i.isLt)

lemma ofFn_fieldsOfList (m : ℕ) (fields : List (List Bool)) (h : fields.length=m) :
    List.ofFn (fieldsOfList m fields h)=fields := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2;simp [fieldsOfList]

lemma parseFixed_run (m : ℕ) (input : List Bool) (fields : List (List Bool)) (rest : List Bool)
    (h : parseFixed m input=some (fields,rest)) :
    ∃ output : Fin m → List Bool,List.ofFn output=fields ∧
      Run (program m) (recordCost fields) (cfg (atIndex m 0) input [] (fun _ => []))
        (cfg .accept rest [] output) := by
  obtain ⟨hlen,he⟩ := parseFixed_sound m input fields rest h
  let output := fieldsOfList m fields hlen
  have ho : List.ofFn output=fields := ofFn_fieldsOfList m fields hlen
  refine ⟨output,ho,?_⟩
  simpa only [ho,←he] using extract_record output rest

lemma parseFixed_suffix_shorter (m : ℕ) (hm : 0 < m) (input : List Bool)
    (fields : List (List Bool)) (rest : List Bool) (h : parseFixed m input=some (fields,rest)) :
    rest.length < input.length := by
  obtain ⟨hlen,he⟩ := parseFixed_sound m input fields rest h
  have hn : fields≠[] := by intro hz;subst fields;simp at hlen;omega
  have hp : 0<(dataFields fields).length := by
    cases fields with
    | nil => contradiction
    | cons b bs => simp [dataFields]
  rw [he,List.length_append]
  omega

end BalancedAssortments.NPStackSourceRecords
