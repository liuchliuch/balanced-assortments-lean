import BalancedAssortments.NPSATStackFresh

noncomputable section
namespace BalancedAssortments.NPSATStackVariableTokens
open NPStack NPStack.Structured NPCNF.Encoding NPStackFields
abbrev Reg := NPSATStackVariables.Reg ⊕ Unit

def itemMap : NPSATStackItem.Reg → Reg := fun k=>.inl (.inl k)
def catalog : Reg := itemMap (.inr .catalog)
def formula : Reg := itemMap (.inr .formula)
def query : Reg := itemMap (.inr .query)
def scratch : Reg := itemMap (.inr .scratch)
def wire : Reg := itemMap (.inr .wire)
def vars : Reg := itemMap (.inr .catalogWork)
def clauses : Reg := itemMap (.inr .formulaWork)
def remaining : Reg := .inl NPSATStackVariables.remaining
def fresh : Reg := .inr ()

def variableAtom : Atom Reg := embeddedAtom
  (Structured.program NPSATStackVariables.loop NPSATStackVariables.remaining NPSATStackVariables.wire)
  (finish NPSATStackVariables.loop) (code_finish _) (program_noChoice _ _ _)
  Sum.inl remaining wire

def tokensAtom : Atom Reg := embeddedAtom
  (Structured.program NPSATStackItem.tokens (.inr .catalog) (.inr .wire))
  (finish NPSATStackItem.tokens) (code_finish _) (program_noChoice _ _ _) itemMap catalog wire

def build : Block Reg :=
  .seq (.atom (copyAtom catalog scratch remaining))
    (.seq (.atom variableAtom)
      (.seq (.atom (copyAtom fresh scratch query)) (.atom tokensAtom)))

def store (rest cat form fr q vars cls out : List Bool) : Store Reg
  | .inl (.inl k) => NPSATStackItem.store cat form q vars cls [] [] out k
  | .inl (.inr _) => rest
  | .inr _ => fr

@[simp] lemma update_remaining (rest cat form fr q vars cls out v : List Bool) :
    Function.update (store rest cat form fr q vars cls out) remaining v=store v cat form fr q vars cls out := by
  funext k;rcases k with k|k
  · rcases k with k|k <;> simp [remaining,NPSATStackVariables.remaining,store]
  · simp [remaining,store]
@[simp] lemma update_query (rest cat form fr q vars cls out v : List Bool) :
    Function.update (store rest cat form fr q vars cls out) query v=store rest cat form fr v vars cls out := by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp [query,itemMap,store,NPSATStackItem.store]
    · simp [query,itemMap,store]
  · simp [query,itemMap,store]
@[simp] lemma update_wire (rest cat form fr q vars cls out v : List Bool) :
    Function.update (store rest cat form fr q vars cls out) wire v=store rest cat form fr q vars cls v := by
  funext k;rcases k with k|k
  · rcases k with k|k
    · rcases k with k|k <;> cases k <;> simp [wire,itemMap,store,NPSATStackItem.store]
    · simp [wire,itemMap,store]
  · simp [wire,itemMap,store]

@[simp] lemma store_remaining (rest cat form fr q vs cs out : List Bool) : store rest cat form fr q vs cs out remaining=rest := rfl
@[simp] lemma store_catalog (rest cat form fr q vs cs out : List Bool) : store rest cat form fr q vs cs out catalog=cat := rfl
@[simp] lemma store_fresh (rest cat form fr q vs cs out : List Bool) : store rest cat form fr q vs cs out fresh=fr := rfl
@[simp] lemma store_query (rest cat form fr q vs cs out : List Bool) : store rest cat form fr q vs cs out query=q := rfl

lemma build_exec (labels : List (List Bool)) (F : BitFormula) (fr out : List Bool) (B : ℕ)
    (hw : ∀label∈labels,label.length≤B) (hF : ∀c∈F,c.length≤3)
    (hfcat : ∀label∈labels,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value label)
    (hfform : ∀c∈F,∀l∈c,ComplexityTimeBinary.value fr≠ComplexityTimeBinary.value l.labelBits) :
    ∃t ≤ 5*(dataFields labels).length+NPSATStackVariables.budget labels F labels B+
      5*fr.length+NPSATStackItem.tokensBudget labels F fr B+7,
      Exec build (store [] (dataFields labels) (dataFields (formulaFields F)) fr [] [] [] out)
        (store [] (dataFields labels) (dataFields (formulaFields F)) fr fr
          (List.replicate labels.length false) (List.replicate F.length false)
          (NPSATStackVariables.output labels F labels out)) t := by
  let cat := dataFields labels
  let form := dataFields (formulaFields F)
  let result := NPSATStackVariables.output labels F labels out
  have hcopy := copyAtom_run catalog scratch remaining
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap,catalog,scratch,remaining,itemMap,NPSATStackVariables.remaining])
    (store [] cat form fr [] [] [] out) rfl
  have h1 : Exec (.atom (copyAtom catalog scratch remaining))
      (store [] cat form fr [] [] [] out) (store cat cat form fr [] [] [] out) (5*cat.length+2) := by
    simpa only [store_catalog,store_remaining,List.append_nil,update_remaining] using hcopy
  obtain ⟨tv,htv,hv⟩ := NPSATStackVariables.loop_exec labels F labels out B hw hF
  have h2 : Exec (.atom variableAtom) (store cat cat form fr [] [] [] out)
      (store [] cat form fr [] [] [] result) tv := by
    apply embeddedAtom_exec
      (Structured.program NPSATStackVariables.loop NPSATStackVariables.remaining NPSATStackVariables.wire)
      (finish NPSATStackVariables.loop) (code_finish _) (program_noChoice _ _ _)
      Sum.inl Sum.inl_injective remaining wire (hv.compiles _ _)
      (store cat cat form fr [] [] [] out) (store [] cat form fr [] [] [] result)
    · intro a;rcases a with a|a <;> rfl
    · intro a;rcases a with a|a <;> rfl
    · intro k hk;rcases k with k|k
      · exact False.elim (hk k rfl)
      · rfl
  have hfc := copyAtom_run fresh scratch query
    (by intro a b h;cases a <;> cases b <;> simp_all [Macros.copyMap,fresh,scratch,query,itemMap])
    (store [] cat form fr [] [] [] result) rfl
  have h3 : Exec (.atom (copyAtom fresh scratch query))
      (store [] cat form fr [] [] [] result) (store [] cat form fr fr [] [] result) (5*fr.length+2) := by
    simpa only [store_fresh,store_query,List.append_nil,update_query] using hfc
  obtain ⟨tt,htt,ht⟩ := NPSATStackItem.tokens_exec labels F fr result B hw hF hfcat hfform
  have h4 : Exec (.atom tokensAtom) (store [] cat form fr fr [] [] result)
      (store [] cat form fr fr (List.replicate labels.length false) (List.replicate F.length false) result) tt := by
    apply embeddedAtom_exec
      (Structured.program NPSATStackItem.tokens (.inr .catalog) (.inr .wire))
      (finish NPSATStackItem.tokens) (code_finish _) (program_noChoice _ _ _)
      itemMap (fun _ _ h=>Sum.inl_injective (Sum.inl_injective h)) catalog wire (ht.compiles _ _)
      (store [] cat form fr fr [] [] result)
      (store [] cat form fr fr (List.replicate labels.length false) (List.replicate F.length false) result)
    · intro a;rfl
    · intro a;rfl
    · intro k hk;rcases k with k|k
      · rcases k with k|k
        · exact False.elim (hk k rfl)
        · rfl
      · rfl
  have hall := h1.seq (h2.seq (h3.seq h4))
  exact ⟨_,by dsimp only [cat] at *;omega,hall⟩

end BalancedAssortments.NPSATStackVariableTokens
