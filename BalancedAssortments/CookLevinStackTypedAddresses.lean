import BalancedAssortments.CookLevinStackTypedLogic
import BalancedAssortments.CookLevinStackInitialize

noncomputable section
namespace BalancedAssortments.CookLevin.StackTableau
open NPCNF NPMachine ComplexityTimeBinary

@[simp] lemma scalar_values (M : Machine) (word : List Bool) (T : ℕ) :
    (fun i => value (StackInitialize.scalarEnv M word T i))=
      ![M.stateExtra+1,M.symbolExtra+3,windowWidth word T,T,M.rules.length+1,0,0,word.length,0] := by
  funext i
  rw [StackInitialize.scalarEnv_eq]
  fin_cases i <;> simp [StackCount.counterBits_value,windowWidth,value]

structure Dimensions (M : Machine) (W T : ℕ) (e : Fin 9 → List Bool) : Prop where
  states : value (e 0)=M.stateExtra+1
  symbols : value (e 1)=M.symbolExtra+3
  width : value (e 2)=W
  time : value (e 3)=T
  rules : value (e 4)=M.rules.length+1

lemma dimensions_scalar (M : Machine) (word : List Bool) (T : ℕ) :
    Dimensions M (windowWidth word T) T (StackInitialize.scalarEnv M word T) := by
  have h := scalar_values M word T
  constructor <;> exact congrFun h _

lemma Dimensions.update {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool}
    (h : Dimensions M W T e) (i : Fin 9) (hi : 5 ≤ i.val) (bits : List Bool) :
    Dimensions M W T (Function.update e i bits) := by
  have hn (k : Fin 9) (hk : k.val<5) : k≠i := by
    intro he;subst i;omega
  rcases h with ⟨h0,h1,h2,h3,h4⟩
  constructor
  · simpa [Function.update_of_ne (hn 0 (by decide))] using h0
  · simpa [Function.update_of_ne (hn 1 (by decide))] using h1
  · simpa [Function.update_of_ne (hn 2 (by decide))] using h2
  · simpa [Function.update_of_ne (hn 3 (by decide))] using h3
  · simpa [Function.update_of_ne (hn 4 (by decide))] using h4

lemma address_state {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool}
    (h : Dimensions M W T e) (a b : E) (t : Fin (T+1)) (s : Fin (M.stateExtra+1))
    (ht : denote e a=t.val) (hs : denote e b=s.val) :
    denote e (state a b)=index (Var.state t s : TVar M W T) := by
  simp [denote_state,h.states,ht,hs,index_state]
lemma address_head {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool}
    (h : Dimensions M W T e) (a b : E) (t : Fin (T+1)) (p : Fin W)
    (ht : denote e a=t.val) (hp : denote e b=p.val) :
    denote e (head a b)=index (Var.head t p : TVar M W T) := by
  simp [denote_head,h.states,h.time,h.width,ht,hp,index_head]
lemma address_tape {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool}
    (h : Dimensions M W T e) (a b c : E) (t : Fin (T+1)) (p : Fin W) (s : Fin (M.symbolExtra+3))
    (ht : denote e a=t.val) (hp : denote e b=p.val) (hs : denote e c=s.val) :
    denote e (tape a b c)=index (Var.tape t p s : TVar M W T) := by
  simp [denote_tape,h.states,h.symbols,h.width,h.time,ht,hp,hs,index_tape]
lemma address_choice {M : Machine} {W T : ℕ} {e : Fin 9 → List Bool}
    (h : Dimensions M W T e) (a b : E) (t : Fin T) (r : Fin (M.rules.length+1))
    (ht : denote e a=t.val) (hr : denote e b=r.val) :
    denote e (choice a b)=index (Var.choice t r : TVar M W T) := by
  simp [denote_choice,h.states,h.symbols,h.width,h.time,h.rules,ht,hr,index_choice]

@[simp] lemma updated_counter (e : Fin 9 → List Bool) (i : Fin 9) (n : ℕ) :
    denote (Function.update e i (StackCount.counterBits n)) (x i)=n := by
  simp [StackCount.counterBits_value]

end BalancedAssortments.CookLevin.StackTableau
