import BalancedAssortments.NPStackClearLink
import BalancedAssortments.NPStackSourcePairingSound

namespace BalancedAssortments.NPStack.ClearRows
open NPStack
variable {K : Type} [DecidableEq K]

def ClearState : List K→Type | [] => Unit | _::ks => Unit ⊕ ClearState ks
instance clearStateFinite : (ks : List K)→Fintype (ClearState ks)
  | [] => inferInstanceAs (Fintype Unit)
  | _::ks => letI := clearStateFinite ks;inferInstanceAs (Fintype (Unit ⊕ ClearState ks))

def clearStart : (ks : List K)→ClearState ks | [] => () | _::_ => .inl ()
def clearDone : (ks : List K)→ClearState ks | [] => () | _::ks => .inr (clearDone ks)
def clearCode : (ks : List K)→ClearState ks→Instr K (ClearState ks)
  | [],_ => .halt true
  | k::ks,.inl _ => .pop k (.inr (clearStart ks)) (.inl ()) (.inl ())
  | _::ks,.inr q => (clearCode ks q).rename id Sum.inr

def clearProgram (ks : List K) (input output : K) : Program K (ClearState ks) :=
  ⟨clearCode ks,clearStart ks,input,output⟩
def cleared : List K→(K→List Bool)→K→List Bool
  | [],s => s
  | k::ks,s => cleared ks (Function.update s k [])
def clearCost : List K→(K→List Bool)→ℕ
  | [],_ => 0
  | k::ks,s => (s k).length+1+clearCost ks (Function.update s k [])

lemma cleared_apply (ks : List K) (s : K→List Bool) (k : K) :
    cleared ks s k=if k∈ks then [] else s k := by
  induction ks generalizing s with
  | nil => simp [cleared]
  | cons j ks ih =>
    simp only [cleared,ih,List.mem_cons]
    by_cases hk : k∈ks <;> by_cases hj : k=j <;> simp [hk,hj,Function.update]

lemma clearDone_halts (ks : List K) : clearCode ks (clearDone ks)=.halt true := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simpa only [clearCode,clearDone,Instr.rename] using congrArg (Instr.rename id Sum.inr) ih

lemma clear_tail_extends (k : K) (ks : List K) (input output : K) :
    CodeExtends (clearProgram ks input output) (clearProgram (k::ks) input output) id Sum.inr := by intro q h;rfl

theorem clear_run (ks : List K) (input output : K) (s : K→List Bool) :
    Run (clearProgram ks input output) (clearCost ks s) ⟨clearStart ks,s⟩ ⟨clearDone ks,cleared ks s⟩ := by
  induction ks generalizing s with
  | nil => exact .zero _
  | cons k ks ih =>
    have h1 := clear_linked (P := clearProgram (k::ks) input output) k (.inl ()) (.inr (clearStart ks)) rfl s
    have h2 := (ih (Function.update s k [])).relocate_exact id Sum.inr Function.injective_id
      (clear_tail_extends k ks input output) (c' := ⟨.inr (clearStart ks),Function.update s k []⟩)
      (d' := ⟨.inr (clearDone ks),cleared ks (Function.update s k [])⟩)
      ⟨rfl,fun _ => rfl⟩ ⟨rfl,fun _ => rfl⟩ (by intro k hk;exact (hk k rfl).elim)
    exact h1.trans h2

lemma clear_noChoice (ks : List K) (input output : K) : NoChoice (clearProgram ks input output) := by
  induction ks with
  | nil => intro q a b;simp [clearProgram,clearCode]
  | cons k ks ih =>
    intro q a b
    cases q with
    | inl u => simp [clearProgram,clearCode]
    | inr q => exact Instr.rename_no_choice _ (ih q) id Sum.inr a b

lemma clearCost_bound (ks : List K) (s : K→List Bool) {B : ℕ} (hs : ∀ k∈ks,(s k).length≤B) :
    clearCost ks s≤ks.length*(B+1) := by
  induction ks generalizing s with
  | nil => simp [clearCost]
  | cons k ks ih =>
    have hh := ih (Function.update s k []) (by
      intro j hj
      by_cases he : j=k
      · subst j
        simp [Function.update]
      · simpa [Function.update,he] using hs j (List.mem_cons_of_mem _ hj))
    have hk := hs k (by simp)
    simp only [clearCost,List.length_cons]
    nlinarith

variable {Q : Type}

def finishProgram (P : Program K Q) (ks : List K) : Program K (Q ⊕ ClearState ks) where
  code
    | .inl q => match P.code q with
      | .halt true => .jump (.inr (clearStart ks))
      | .halt false => .halt false
      | i => i.rename id Sum.inl
    | .inr q => (clearCode ks q).rename id Sum.inr
  start := .inl P.start
  inputStack := P.inputStack
  outputStack := P.outputStack

lemma body_extends (P : Program K Q) (ks : List K) : CodeExtends P (finishProgram P ks) id Sum.inl := by
  intro q h
  cases he : P.code q <;> simp [finishProgram,he,Instr.rename]
  rename_i b
  exact (h b he).elim
lemma finish_clear_extends (P : Program K Q) (ks : List K) :
    CodeExtends (clearProgram ks P.inputStack P.outputStack) (finishProgram P ks) id Sum.inr := by intro q h;rfl

lemma body_not_accepting (P : Program K Q) (ks : List K) (q : Q) :
    (finishProgram P ks).code (.inl q)≠.halt true := by
  cases he : P.code q <;> simp [finishProgram,he,Instr.rename]
  rename_i b;cases b <;> simp

theorem body_segment (P : Program K Q) (ks : List K) (x : Config K Q)
    {T : ℕ} {out : Config K (Q ⊕ ClearState ks)}
    (hr : Run (finishProgram P ks) T ⟨.inl x.pc,x.stk⟩ out) (ha : accepts (finishProgram P ks) out) :
    ∃ u v e,Run P u x e ∧ P.code e.pc=.halt true ∧
      Run (finishProgram P ks) v ⟨.inr (clearStart ks),e.stk⟩ out ∧ u+1+v=T := by
  induction T generalizing x with
  | zero => cases hr;exact (body_not_accepting P ks x.pc ha).elim
  | succ T ih =>
    cases hr with
    | @succ _ _ next _ hs htail =>
      by_cases hh : ∃ b,P.code x.pc=.halt b
      · obtain ⟨b,hb⟩ := hh
        cases b with
        | false => simp [Step,successors,finishProgram,hb] at hs
        | true =>
          have he : next=⟨.inr (clearStart ks),x.stk⟩ := by simpa [Step,successors,finishProgram,hb] using hs
          rw [he] at htail
          exact ⟨0,T,x,.zero _,hb,htail,by omega⟩
      · have hn : ∀ b,P.code x.pc≠.halt b := by simpa using hh
        obtain ⟨y,hxy,hrel,hframe⟩ := hs.reflect id Sum.inl Function.injective_id (body_extends P ks)
          (show Relocated id Sum.inl x ⟨.inl x.pc,x.stk⟩ from ⟨rfl,fun _ => rfl⟩) hn
        have he : next=⟨.inl y.pc,y.stk⟩ := by
          cases next with
          | mk q stk =>
            have hq : q=Sum.inl y.pc := hrel.1
            have hstore : stk=y.stk := funext (fun k => hrel.2 k)
            subst q
            subst stk
            rfl
        rw [he] at htail
        obtain ⟨u,v,e,hu,hb,hrest,ht⟩ := ih y htail
        exact ⟨u+1,v,e,.succ hxy hu,hb,hrest,by omega⟩

theorem finish_accepting_store (P : Program K Q) (ks : List K) (x : Config K Q)
    {T : ℕ} {out : Config K (Q ⊕ ClearState ks)}
    (hr : Run (finishProgram P ks) T ⟨.inl x.pc,x.stk⟩ out) (ha : accepts (finishProgram P ks) out) :
    ∃ u e,Run P u x e ∧ P.code e.pc=.halt true ∧ out.stk=cleared ks e.stk := by
  obtain ⟨u,v,e,hu,he,hrest,_⟩ := body_segment P ks x hr ha
  have hd := (clear_run ks P.inputStack P.outputStack e.stk).relocate_deterministic_exact
    (clear_noChoice ks P.inputStack P.outputStack) id Sum.inr Function.injective_id (finish_clear_extends P ks)
    (c' := ⟨.inr (clearStart ks),e.stk⟩) (d' := ⟨.inr (clearDone ks),cleared ks e.stk⟩)
    ⟨rfl,fun _ => rfl⟩ ⟨rfl,fun _ => rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  obtain ⟨t,_,ht⟩ := hd.factor_halted hrest ha
  have hh := ht.from_halted (by simpa [finishProgram,Instr.rename] using congrArg (Instr.rename id Sum.inr) (clearDone_halts ks))
  exact ⟨u,e,hu,he,congrArg Config.stk hh.2.symm⟩

theorem finish_run (P : Program K Q) (ks : List K) {t : ℕ} {x e : Config K Q}
    (hr : Run P t x e) (he : P.code e.pc=.halt true) :
    Run (finishProgram P ks) (t+1+clearCost ks e.stk) ⟨.inl x.pc,x.stk⟩
      ⟨.inr (clearDone ks),cleared ks e.stk⟩ := by
  have h1 := hr.relocate_exact id Sum.inl Function.injective_id (body_extends P ks)
    (c' := ⟨.inl x.pc,x.stk⟩) (d' := ⟨.inl e.pc,e.stk⟩)
    ⟨rfl,fun _ => rfl⟩ ⟨rfl,fun _ => rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  have hj : Step (finishProgram P ks) ⟨.inl e.pc,e.stk⟩ ⟨.inr (clearStart ks),e.stk⟩ := by
    simp [Step,successors,finishProgram,he]
  have h2 := (clear_run ks P.inputStack P.outputStack e.stk).relocate_exact id Sum.inr
    Function.injective_id (finish_clear_extends P ks)
    (c' := ⟨.inr (clearStart ks),e.stk⟩) (d' := ⟨.inr (clearDone ks),cleared ks e.stk⟩)
    ⟨rfl,fun _ => rfl⟩ ⟨rfl,fun _ => rfl⟩ (by intro k hk;exact (hk k rfl).elim)
  exact (h1.trans (Run.one hj)).trans h2

theorem finish_noChoice (P : Program K Q) (ks : List K) (hn : NoChoice P) : NoChoice (finishProgram P ks) := by
  intro q a b
  cases q with
  | inl q =>
    have hh:=hn q
    cases he : P.code q <;> simp_all [finishProgram,Instr.rename]
    rename_i bit;cases bit <;> simp
  | inr q => exact Instr.rename_no_choice _ (clear_noChoice ks P.inputStack P.outputStack q) id Sum.inr a b

def rowKeys {W : Type} : List (Fin 9 ⊕ W) := (List.finRange 9).map Sum.inl

theorem finish_clearsRows {W : Type} [DecidableEq W] (P : Program (Fin 9 ⊕ W) Q) :
    NPStackSourcePairing.ClearsRows (finishProgram P rowKeys) := by
  intro row work t e hr ha i
  obtain ⟨u,d,hu,hd,he⟩ := finish_accepting_store P rowKeys ⟨P.start,NPStackSourcePairing.rowStore row work⟩ hr ha
  rw [he,cleared_apply]
  simp [rowKeys,List.mem_finRange]

end BalancedAssortments.NPStack.ClearRows
