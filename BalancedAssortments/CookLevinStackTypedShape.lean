import BalancedAssortments.CookLevinStackTypedExactlyOne
import BalancedAssortments.CookLevinStackTypedAddresses

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

lemma state_family_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (ht : value (e 5)=t.val) :
    fholds σ (Typed.fixedExactlyOne ((List.range (M.stateExtra+1)).map (fun s => state (x 5) (c s)))) e f ↔
      OneHot σ (fun s => (Var.state t s : TVar M W T)) := by
  rw [fixedExactlyOne_range]
  simp only [OneHot,denote_state,denote_x,denote_c,hd.states,ht,index_state]

lemma tape_family_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (p : Fin W)
    (ht : value (e 5)=t.val) (hp : value (e 6)=p.val) :
    fholds σ (Typed.fixedExactlyOne ((List.range (M.symbolExtra+3)).map (fun a => tape (x 5) (x 6) (c a)))) e f ↔
      OneHot σ (fun a => (Var.tape t p a : TVar M W T)) := by
  rw [fixedExactlyOne_range]
  simp only [OneHot,denote_tape,denote_x,denote_c,hd.states,hd.symbols,hd.time,hd.width,ht,hp,index_tape]

lemma choice_family_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin T) (ht : value (e 5)=t.val) :
    fholds σ (Typed.fixedExactlyOne ((List.range (M.rules.length+1)).map (fun r => choice (x 5) (c r)))) e f ↔
      OneHot σ (fun r => (Var.choice t r : TVar M W T)) := by
  rw [fixedExactlyOne_range]
  simp only [OneHot,denote_choice,denote_x,denote_c,hd.states,hd.symbols,hd.time,hd.width,hd.rules,ht,index_choice]

def headAtLeast : FormulaCode := Typed.dynamicClause (Typed.cloop 6 13 (.literal (head (x 5) (x 6),true)))
def headAtMost : FormulaCode :=
  Typed.loop 6 13 (Typed.loop 8 13 (.branch (succ (x 6)) (x 8)
    (Typed.clause [(head (x 5) (x 6),false),(head (x 5) (x 8),false)]) .empty))

lemma head_atLeast_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (ht : value (e 5)=t.val)
    (hf : (f 13).length=W) :
    fholds σ headAtLeast e f ↔ ∃ p : Fin W,σ (index (Var.head t p : TVar M W T))=true := by
  subst W
  simp only [headAtLeast,Typed.dynamicClause,fholds_clause,cholds_cloop,cholds_literal,evalLiteral_true,
    denote_head,denote_x,index_head]
  simp [Function.update,StackCount.counterBits_value,hd.states,hd.time,hd.width,ht]

lemma head_atMost_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (ht : value (e 5)=t.val)
    (hf : (f 13).length=W) :
    fholds σ headAtMost e f ↔ ∀ i j : Fin W,i.val<j.val →
      ¬(σ (index (Var.head t i : TVar M W T))=true ∧ σ (index (Var.head t j : TVar M W T))=true) := by
  subst W
  simp only [headAtMost,fholds_loop,fholds_branch,negative_pair_holds,fholds_empty]
  simp [denote_succ,denote_x,denote_head,Function.update,StackCount.counterBits_value,
    hd.states,hd.time,hd.width,ht,index_head,Nat.succ_le_iff]

lemma oneHot_ordered (σ : Assignment) {q g W T R n : ℕ} (v : Fin n → Var q g W T R) :
    ((∃ i,σ (index (v i))=true) ∧ ∀ i j : Fin n,i.val<j.val →
      ¬(σ (index (v i))=true ∧ σ (index (v j))=true)) ↔ OneHot σ v := by
  constructor
  · rintro ⟨⟨i,hi⟩,hp⟩
    refine ⟨i,hi,?_⟩
    intro j hj
    apply Fin.ext
    by_contra hne
    by_cases hlt : i.val<j.val
    · exact hp i j hlt ⟨hi,hj⟩
    · exact hp j i (by omega) ⟨hj,hi⟩
  · rintro ⟨i,hi,hu⟩
    refine ⟨⟨i,hi⟩,?_⟩
    intro j k hjk hh
    have hj := hu j hh.1
    have hk := hu k hh.2
    subst j;subst k
    omega

lemma heads_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (ht : value (e 5)=t.val)
    (hf : (f 13).length=W) :
    (fholds σ headAtLeast e f ∧ fholds σ headAtMost e f) ↔
      OneHot σ (fun p => (Var.head t p : TVar M W T)) := by
  rw [head_atLeast_holds M W T σ e f hd t ht hf,head_atMost_holds M W T σ e f hd t ht hf]
  exact oneHot_ordered σ _

lemma loop_holds_length (σ : Assignment) (e f) (i : Fin 9) (src n : ℕ) (p : FormulaCode)
    (hf : (f src).length=n) :
    fholds σ (Typed.loop i src p) e f ↔ ∀ j : Fin n,
      fholds σ p (Function.update e i (StackCount.counterBits j.val)) f := by
  subst n
  exact fholds_loop σ e f i src p

def shapeRow (M : Machine) : FormulaCode := Typed.all [
  Typed.fixedExactlyOne ((List.range (M.stateExtra+1)).map (fun s => state (x 5) (c s))),
  headAtLeast,headAtMost,
  Typed.loop 6 13 (Typed.fixedExactlyOne ((List.range (M.symbolExtra+3)).map
    (fun a => tape (x 5) (x 6) (c a))))]

lemma shape_row_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (t : Fin (T+1)) (ht : value (e 5)=t.val)
    (hf : (f 13).length=W) :
    fholds σ (shapeRow M) e f ↔
      OneHot σ (fun s => (Var.state t s : TVar M W T)) ∧
      OneHot σ (fun p => (Var.head t p : TVar M W T)) ∧
      ∀ p : Fin W,OneHot σ (fun a => (Var.tape t p a : TVar M W T)) := by
  have hs := state_family_holds M W T σ e f hd t ht
  have hh := heads_holds M W T σ e f hd t ht hf
  have hp : fholds σ (Typed.loop 6 13 (Typed.fixedExactlyOne ((List.range (M.symbolExtra+3)).map
      (fun a => tape (x 5) (x 6) (c a))))) e f ↔
      ∀ p : Fin W,OneHot σ (fun a => (Var.tape t p a : TVar M W T)) := by
    rw [loop_holds_length σ e f 6 13 W _ hf]
    apply forall_congr'
    intro p
    exact tape_family_holds M W T σ _ f (hd.update 6 (by decide) _) t p
      (by simpa [Function.update] using ht) (by simp [StackCount.counterBits_value])
  simp only [shapeRow,fholds_all,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq]
  constructor
  · rintro ⟨a,b,c,d⟩
    exact ⟨hs.mp a,hh.mp ⟨b,c⟩,hp.mp d⟩
  · rintro ⟨a,b,c⟩
    exact ⟨hs.mpr a,(hh.mpr b).1,(hh.mpr b).2,hp.mpr c⟩

/-- Exact equivalence of the compiled schema's one-hot clauses with the source
mathematical tableau shape, including zero-length time and tape families. -/
theorem typed_shape_holds (M : Machine) (W T : ℕ) (σ : Assignment) (e f)
    (hd : Dimensions M W T e) (hrows : (f 12).length=T+1)
    (htimes : (f 11).length=T) (hwidth : (f 13).length=W) :
    fholds σ (Typed.shape M) e f ↔ ShapeHolds M W T σ := by
  change fholds σ (.seq (Typed.loop 5 12 (shapeRow M))
    (Typed.loop 5 11 (Typed.fixedExactlyOne ((List.range (M.rules.length+1)).map
      (fun r => choice (x 5) (c r)))))) e f ↔ _
  rw [fholds_seq,loop_holds_length σ e f 5 12 (T+1) _ hrows,
    loop_holds_length σ e f 5 11 T _ htimes]
  have hr (t : Fin (T+1)) := shape_row_holds M W T σ
    (Function.update e 5 (StackCount.counterBits t.val)) f (hd.update 5 (by decide) _) t
    (by simp [StackCount.counterBits_value]) hwidth
  have hc (t : Fin T) := choice_family_holds M W T σ
    (Function.update e 5 (StackCount.counterBits t.val)) f (hd.update 5 (by decide) _) t
    (by simp [StackCount.counterBits_value])
  simp_rw [hr,hc]
  constructor
  · rintro ⟨h,c⟩
    exact ⟨fun t => (h t).1,fun t => (h t).2.1,fun t => (h t).2.2,c⟩
  · rintro ⟨s,h,a,c⟩
    exact ⟨fun t => ⟨s t,h t,a t⟩,c⟩

theorem shape_holds (M : Machine) (word : List Bool) (T : ℕ) (σ : Assignment) :
    fholds σ (Typed.shape M) (StackInitialize.scalarEnv M word T) (StackInitialize.specStore M word T) ↔
      ShapeHolds M (windowWidth word T) T σ :=
  typed_shape_holds M _ T σ _ _ (dimensions_scalar M word T)
    (by simp) (by simp) (by simp)

end BalancedAssortments.CookLevin.StackTableau
