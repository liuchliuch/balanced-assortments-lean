import BalancedAssortments.NPStackTapeSimulation
import BalancedAssortments.NPStackReverse

noncomputable section
namespace BalancedAssortments.NPStack.TapeInitialize
open NPMachine NPMachine.FiniteBridge
open TapeMachine
variable {K Q : Type*} [Fintype K] [Fintype Q] [DecidableEq K]

def liftInstr : Instr K Q → Instr (Option K) (ReverseState ⊕ Q)
  | .halt b => .halt b
  | .jump q => .jump (.inr q)
  | .push k b q => .push (some k) b (.inr q)
  | .pop k qe qf qt => .pop (some k) (.inr qe) (.inr qf) (.inr qt)
  | .choice q r => .choice (.inr q) (.inr r)

/-- A fresh track is reserved for initialization; source tracks are unchanged. -/
def liftedProgram (P : NPStack.Program K Q) : NPStack.Program (Option K) (ReverseState ⊕ Q) where
  start := .inl .read
  inputStack := none
  outputStack := some P.outputStack
  code
    | .inr q => liftInstr (P.code q)
    | .inl .read => .pop none (.inr P.start) (.inl .pushFalse) (.inl .pushTrue)
    | .inl .pushFalse => .push (some P.inputStack) false (.inl .read)
    | .inl .pushTrue => .push (some P.inputStack) true (.inl .read)
    | .inl .done => .jump (.inr P.start)

def extendedStacks (s : K → List Bool) : Option K → List Bool
  | none => []
  | some k => s k

def reversingStacks (P : NPStack.Program K Q) (xs ys : List Bool) : Option K → List Bool
  | none => xs
  | some k => if k=P.inputStack then ys else []

lemma reverse_stack_run (P : NPStack.Program K Q) (xs ys : List Bool) :
    NPStack.Run (liftedProgram P) (2*xs.length+1)
      ⟨.inl .read,reversingStacks P xs ys⟩
      ⟨.inr P.start,reversingStacks P [] (xs.reverse++ys)⟩ := by
  induction xs generalizing ys with
  | nil =>
    apply NPStack.Run.one
    simp [NPStack.Step,successors,liftedProgram,reversingStacks]
  | cons b xs ih =>
    have hpop : NPStack.Step (liftedProgram P) ⟨.inl .read,reversingStacks P (b::xs) ys⟩
        ⟨.inl (if b then .pushTrue else .pushFalse),reversingStacks P xs ys⟩ := by
      have hu : Function.update (reversingStacks P (b::xs) ys) none xs = reversingStacks P xs ys := by
        funext k; cases k <;> simp [reversingStacks]
      cases b <;> simp [NPStack.Step,successors,liftedProgram,reversingStacks,←hu]
    have hpush : NPStack.Step (liftedProgram P)
        ⟨.inl (if b then .pushTrue else .pushFalse),reversingStacks P xs ys⟩
        ⟨.inl .read,reversingStacks P xs (b::ys)⟩ := by
      have hu : Function.update (reversingStacks P xs ys) (some P.inputStack) (b::ys) =
          reversingStacks P xs (b::ys) := by
        funext k; cases k with
        | none => simp [reversingStacks]
        | some k =>
          by_cases hk : k=P.inputStack
          · subst k; simp [reversingStacks]
          · simp [reversingStacks,hk]
      cases b <;> simp [NPStack.Step,successors,liftedProgram,reversingStacks,←hu]
    have hh := NPStack.Run.succ hpop (NPStack.Run.succ hpush (ih (b::ys)))
    simpa [List.reverse_cons,List.append_assoc,Nat.mul_add,Nat.add_assoc] using hh

inductive InitControl (K Q : Type*)
  | scan (first : Bool)
  | back
  | run (q : TapeMachine.Control (Option K) (ReverseState ⊕ Q))
  deriving DecidableEq, Fintype

abbrev InitCell (K : Type*) := TapeMachine.Cell (Option K)

def scanCell (first : Bool) (b : Option Bool) : Symbol (InitCell K) :=
  .work (first,fun k => if k=none then b else none)

def initActions (P : NPStack.Program K Q) : InitControl K Q → Symbol (InitCell K) →
    List (Action (InitControl K Q) (InitCell K))
  | .scan first,.bit b => [(.scan false,scanCell first (some b),.right)]
  | .scan first,.blank => if first then [(.run (.normal (.inl .read)),scanCell true none,.stay)]
      else [(.back,.blank,.left)]
  | .scan _,.work _ => []
  | .back,a => if (readCell a).1 then [(.run (.normal (.inl .read)),a,.stay)] else [(.back,a,.left)]
  | .run q,a => (TapeMachine.actions (liftedProgram P) q a).map (fun x => (.run x.1,x.2))

def initAccepting (P : NPStack.Program K Q) : InitControl K Q → Bool
  | .run q => TapeMachine.accepting (liftedProgram P) q
  | _ => false

def initialized (P : NPStack.Program K Q) : FiniteBridge.Program (InitControl K Q) (InitCell K) :=
  tableProgram (.scan true) (initAccepting P) (initActions P)

def rawTape (word : List Bool) : Tape (Option K) := fun p =>
  if 0≤p then match word[p.toNat]? with | some b => .bit b | none => .blank else .blank

/-- Partially converted input: exactly the first j cells have been written. -/
def scannedTape (word : List Bool) (j : ℕ) : Tape (Option K) := fun p =>
  if 0≤p ∧ p<(j : ℤ) then scanCell (decide (p=0)) word[p.toNat]? else rawTape word p

def cfg (t : Tape (Option K)) (q : InitControl K Q) (p : ℤ) :
    Configuration (InitControl K Q) (InitCell K) := ⟨q,p,t⟩

lemma init_action (P : NPStack.Program K Q) (t : Tape (Option K)) (q q' : InitControl K Q)
    (p : ℤ) (a : Symbol (InitCell K)) (m : Move)
    (h : (q',a,m)∈initActions P q (t p)) :
    FiniteBridge.Step (initialized P) (cfg t q p)
      (cfg (Function.update t p a) q' (p+m.displacement)) :=
  (table_step _ _ _ _ _).2 ⟨(q',a,m),h,rfl⟩

lemma scanned_zero (word : List Bool) : scannedTape (K:=K) word 0=rawTape word := by
  funext p; simp [scannedTape]

lemma scanned_at (word : List Bool) (j : ℕ) (hj : j<word.length) :
    scannedTape (K:=K) word j j=.bit word[j] := by
  simp [scannedTape,rawTape,List.getElem?_eq_getElem hj]

lemma scanned_succ (word : List Bool) (j : ℕ) (hj : j<word.length) :
    Function.update (scannedTape (K:=K) word j) j
      (scanCell (decide (j=0)) (some word[j])) = scannedTape word (j+1) := by
  funext p
  by_cases hp : p=(j:ℤ)
  · subst p; simp [scannedTape,List.getElem?_eq_getElem hj]
  · rw [Function.update_of_ne hp]
    have he : (0≤p ∧ p<(j:ℤ)) ↔ (0≤p ∧ p<((j+1:ℕ):ℤ)) := by omega
    simp only [scannedTape,he]

lemma scan_run (P : NPStack.Program K Q) (word : List Bool) (j : ℕ) (hj : j≤word.length) :
    FiniteBridge.Run (initialized P) j
      (cfg (rawTape word) (.scan true) 0)
      (cfg (scannedTape word j) (.scan (decide (j=0))) j) := by
  induction j with
  | zero =>
    simpa [scanned_zero] using (FiniteBridge.Run.zero (P := initialized P)
      (cfg (rawTape (K:=K) word) (InitControl.scan true : InitControl K Q) 0))
  | succ j ih =>
    have hlt : j<word.length := by omega
    have hs := init_action P (scannedTape word j) (.scan (decide (j=0))) (.scan false) j
      (scanCell (decide (j=0)) (some word[j])) .right
      (by rw [scanned_at word j hlt];simp [initActions])
    rw [scanned_succ word j hlt] at hs
    have hs' : FiniteBridge.Step (initialized P)
        (cfg (scannedTape word j) (.scan (decide (j=0))) j)
        (cfg (scannedTape word (j+1)) (.scan (decide (j+1=0))) (j+1)) := by
      simpa [Move.displacement] using hs
    exact (ih (by omega)).trans (FiniteBridge.Run.one hs')

lemma scanned_represents (P : NPStack.Program K Q) (word : List Bool) (hw : word≠[]) :
    Represents (reversingStacks P word.reverse []) (scannedTape word word.length) := by
  have hl : 0<word.length := List.length_pos_iff.mpr hw
  have outside : ∀ p : ℤ, ¬(0≤p ∧ p<(word.length:ℤ)) → rawTape (K:=K) word p=.blank := by
    intro p h
    by_cases hp : 0≤p
    · have he : word[p.toNat]?=none := List.getElem?_eq_none (by omega)
      simp [rawTape,hp,he]
    · simp [rawTape,hp]
  constructor
  · intro p
    by_cases h : 0≤p ∧ p<(word.length:ℤ)
    · simp only [scannedTape,if_pos h,scanCell,readCell]
    · have hn : p≠0 := by omega
      simp only [scannedTape,if_neg h,outside p h,readCell,hn,decide_false]
  · intro k p
    by_cases h : 0≤p ∧ p<(word.length:ℤ)
    · simp only [scannedTape,if_pos h,scanCell,readCell]
      cases k <;> simp [reversingStacks,h.1]
    · simp only [scannedTape,if_neg h,outside p h,readCell]
      by_cases hp : 0≤p
      · have he : word[p.toNat]?=none := List.getElem?_eq_none (by omega)
        cases k <;> simp [reversingStacks,hp,he]
      · simp [hp]

lemma init_back_run (P : NPStack.Program K Q) (t : Tape (Option K))
    (hb : ∀ j : ℕ,(readCell (t j)).1=decide (j=0)) (j : ℕ) :
    FiniteBridge.Run (initialized P) (j+1) (cfg t .back j)
      (cfg t (.run (.normal (.inl .read))) 0) := by
  induction j with
  | zero =>
    have hh := init_action P t .back (.run (.normal (.inl .read))) 0 (t 0) .stay
      (by simp [initActions,show (readCell (t 0)).1=true by simpa using hb 0])
    apply FiniteBridge.Run.one
    simpa [Move.displacement,Function.update_eq_self] using hh
  | succ j ih =>
    have hh := init_action P t .back .back (j+1) (t (j+1)) .left
      (by simp [initActions,show (readCell (t (j+1))).1=false by simpa using hb (j+1)])
    have hs : FiniteBridge.Step (initialized P) (cfg t .back (j+1)) (cfg t .back j) := by
      simpa [Move.displacement,Function.update_eq_self] using hh
    exact FiniteBridge.Run.succ hs ih

lemma scan_complete (P : NPStack.Program K Q) (word : List Bool) :
    ∃ s≤2*word.length+2,∃ t,Represents (reversingStacks P word.reverse []) t ∧
      FiniteBridge.Run (initialized P) s (FiniteBridge.initial (initialized P) word)
        (cfg t (.run (.normal (.inl .read))) 0) := by
  by_cases hw : word=[]
  · subst word
    let t : Tape (Option K) := Function.update (rawTape []) 0 (scanCell true none)
    have hr : Represents (reversingStacks P [].reverse []) t := by
      constructor
      · intro p
        by_cases hp : p=0
        · subst p; simp [t,scanCell,readCell]
        · simp [t,Function.update_of_ne hp,rawTape,readCell,hp]
      · intro k p
        by_cases hp : p=0
        · subst p; cases k <;> simp [t,scanCell,readCell,reversingStacks]
        · cases k <;> simp [t,Function.update_of_ne hp,rawTape,readCell,reversingStacks]
    refine ⟨1,by simp,t,hr,FiniteBridge.Run.one ?_⟩
    have hh := init_action P (rawTape []) (.scan true) (.run (.normal (.inl .read))) 0
      (scanCell true none) .stay (by simp [rawTape,initActions])
    change FiniteBridge.Step (initialized P) (cfg (rawTape []) (.scan true) 0) (cfg t (.run (.normal (.inl .read))) 0)
    simpa only [Move.displacement,add_zero] using hh
  · have hl : 0<word.length := List.length_pos_iff.mpr hw
    let n := word.length
    let t := scannedTape (K:=K) word n
    have hr := scanned_represents P word hw
    have hend : t (n:ℤ)=.blank := by simp [t,n,scannedTape,rawTape]
    have hs := scan_run P word n (by rfl)
    have hh := init_action P t (.scan false) .back n .blank .left
      (by rw [hend];simp [initActions])
    have htupdate : Function.update t (n:ℤ) .blank=t := by rw [←hend]; exact Function.update_eq_self _ _
    rw [htupdate] at hh
    have hb := init_back_run P t (represents_bottom _ _ hr) (n-1)
    have hh' : FiniteBridge.Step (initialized P) (cfg t (.scan (decide (n=0))) n)
        (cfg t .back (n-1:ℕ)) := by
      have hn : n≠0 := by dsimp [n];omega
      have he : (n:ℤ)+Move.left.displacement=((n-1:ℕ):ℤ) := by simp [Move.displacement]; dsimp [n];omega
      simpa [hn,he] using hh
    refine ⟨n+1+(n-1+1),by dsimp [n];omega,t,hr,?_⟩
    have hall := (hs.trans (FiniteBridge.Run.one hh')).trans hb
    simpa [cfg,FiniteBridge.initial,initialized,tableProgram,rawTape] using hall

/-- Existing finite core transitions are embedded without extra work. -/
def embed (c : Configuration (TapeMachine.Control (Option K) (ReverseState ⊕ Q)) (InitCell K)) :
    Configuration (InitControl K Q) (InitCell K) := ⟨.run c.state,c.head,c.tape⟩

lemma embed_step (P : NPStack.Program K Q) {c d}
    (h : FiniteBridge.Step (core (liftedProgram P)) c d) :
    FiniteBridge.Step (initialized P) (embed c) (embed d) := by
  obtain ⟨x,hx,rfl⟩ := (table_step _ _ _ _ _).1 h
  apply (table_step _ _ _ _ _).2
  refine ⟨(.run x.1,x.2),?_,rfl⟩
  exact List.mem_map.mpr ⟨x,hx,rfl⟩

lemma embed_run (P : NPStack.Program K Q) {s : ℕ} {c d}
    (h : FiniteBridge.Run (core (liftedProgram P)) s c d) :
    FiniteBridge.Run (initialized P) s (embed c) (embed d) := by
  induction h with
  | zero => exact FiniteBridge.Run.zero _
  | succ hs hr ih => exact FiniteBridge.Run.succ (embed_step P hs) ih

/-- A closed quadratic number of actual one-tape transitions. -/
def initCost (n : ℕ) : ℕ := 2*n+2+(2*n+1)*(2*(n+(2*n+1))+3)

theorem initialized_run (P : NPStack.Program K Q) (word : List Bool) :
    ∃ s ≤ initCost word.length,∃ t,
      Represents (extendedStacks (NPStack.initial P word).stk) t ∧
      FiniteBridge.Run (initialized P) s (FiniteBridge.initial (initialized P) word)
        (cfg t (.run (.normal (.inr P.start))) 0) := by
  obtain ⟨s,hs,t,hrep,hscan⟩ := scan_complete P word
  have hrev := reverse_stack_run P word.reverse []
  have hheight : ∀ k,(reversingStacks P word.reverse [] k).length≤word.length := by
    intro k; cases k <;> simp [reversingStacks]
  obtain ⟨u,hu,t',hrep',hrun⟩ := TapeMachine.run_simulates hrev t hrep word.length hheight
  have he : reversingStacks P [] (word.reverse.reverse++[]) =
      extendedStacks (NPStack.initial P word).stk := by
    funext k
    cases k with
    | none => rfl
    | some k => by_cases hk : k=P.inputStack <;> simp [reversingStacks,extendedStacks,NPStack.initial,Function.update_apply,hk]
  rw [he] at hrep'
  refine ⟨s+u,?_,t',hrep',?_⟩
  · simp only [List.length_reverse] at hu
    unfold initCost; omega
  · exact hscan.trans (embed_run P hrun)

end BalancedAssortments.NPStack.TapeInitialize
