import BalancedAssortments.NPStackFieldCorrect
import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.NPCNFEncoding

/-! Repeated raw-field parsing by a finite Boolean-stack program. A field's
payload is emitted as true,bit pairs followed by false, preserving record
boundaries without introducing an unbounded instruction or recursive oracle. -/
namespace BalancedAssortments.NPStackFields
open NPStack
abbrev Stack := Sum NPStackField.Stack Unit
inductive State | probe | restoreFalse | restoreTrue | field (q : NPStackField.State) |
  emit | tagFalse | tagTrue | bitFalse | bitTrue | delimiter |
  reverse | reverseFalse | reverseTrue | accept
  deriving DecidableEq, Fintype

def input : Stack := .inl .input
def output : Stack := .inl .output
def accumulator : Stack := .inr ()

def program : Program Stack State where
  code
    | .probe => .pop input .reverse .restoreFalse .restoreTrue
    | .restoreFalse => .push input false (.field .header)
    | .restoreTrue => .push input true (.field .header)
    | .field .accept => .jump .emit
    | .field .reject => .halt false
    | .field q => (NPStackField.program.code q).rename Sum.inl State.field
    | .emit => .pop output .delimiter .tagFalse .tagTrue
    | .tagFalse => .push accumulator true .bitFalse
    | .tagTrue => .push accumulator true .bitTrue
    | .bitFalse => .push accumulator false .emit
    | .bitTrue => .push accumulator true .emit
    | .delimiter => .push accumulator false .probe
    | .reverse => .pop accumulator .accept .reverseFalse .reverseTrue
    | .reverseFalse => .push output false .reverse
    | .reverseTrue => .push output true .reverse
    | .accept => .halt true
  start := .probe
  inputStack := input
  outputStack := output

def cfg (q : State) (i c r o acc : List Bool) : Config Stack State :=
  ⟨q,fun k => match k with
    | .inl .input => i
    | .inl .count => c
    | .inl .reversed => r
    | .inl .output => o
    | .inr _ => acc⟩

lemma field_code : CodeExtends NPStackField.program program Sum.inl State.field := by
  intro q h
  cases q <;> simp_all [program,NPStackField.program]

lemma field_relocated (q : NPStackField.State) (i c r o acc : List Bool) :
    Relocated Sum.inl State.field (NPStackField.cfg q i c r o) (cfg (.field q) i c r o acc) := by
  refine ⟨rfl,?_⟩
  intro k; cases k <;> rfl

lemma field_frame (q : State) (i c r o acc : List Bool) (q' : State) (i' c' r' o' : List Bool) :
    Frame Sum.inl (cfg q i c r o acc) (cfg q' i' c' r' o' acc) := by
  intro k hk
  cases k with
  | inl k => exact False.elim (hk k rfl)
  | inr u => rfl

/-- Invoke the finite field subroutine while preserving the caller accumulator.
The final source halt is patched to a return jump, not invoked as an oracle. -/
lemma field_run {t : ℕ} {q q' : NPStackField.State} {i c r o i' c' r' o' : List Bool}
    (h : Run NPStackField.program t (NPStackField.cfg q i c r o) (NPStackField.cfg q' i' c' r' o'))
    (acc : List Bool) :
    Run program t (cfg (.field q) i c r o acc) (cfg (.field q') i' c' r' o' acc) := by
  obtain ⟨d,hd,hr,hf⟩ := h.relocate Sum.inl State.field Sum.inl_injective field_code (field_relocated q i c r o acc)
  have he : d=cfg (.field q') i' c' r' o' acc :=
    relocated_frame_unique Sum.inl State.field hr (field_relocated q' i' c' r' o' acc) hf
      (field_frame _ _ _ _ _ _ _ _ _ _ _)
  rw [he] at hd
  exact hd

def tagBits (bits : List Bool) : List Bool := bits.flatMap (fun b => [true,b])
def dataFields (fields : List (List Bool)) : List Bool := fields.flatMap (fun bits => tagBits bits++[false])

lemma probe_cons (b : Bool) (bs acc : List Bool) :
    Run program 2 (cfg .probe (b::bs) [] [] [] acc) (cfg (.field .header) (b::bs) [] [] [] acc) := by
  cases b
  · apply Run.succ (d := cfg .restoreFalse bs [] [] [] acc)
    · simp [Step,successors,program,cfg,input]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
    · apply Run.one
      simp [Step,successors,program,cfg,input]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
  · apply Run.succ (d := cfg .restoreTrue bs [] [] [] acc)
    · simp [Step,successors,program,cfg,input]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp
    · apply Run.one
      simp [Step,successors,program,cfg,input]; funext k; cases k with
      | inl j => cases j <;> simp
      | inr u => simp

end BalancedAssortments.NPStackFields
