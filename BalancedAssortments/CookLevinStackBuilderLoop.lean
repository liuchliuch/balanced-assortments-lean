import BalancedAssortments.CookLevinStackBuilderState

noncomputable section
namespace BalancedAssortments.CookLevin.StackBuilder
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)
open StackAssign

lemma loopState_width {n : ℕ} (s : Store ℕ) (index : Fin n) (p out : ℕ)
    (bits rest acc : List Bool) (B : ℕ) (ho : n≤out) (hp : out<p)
    (hbits : bits.length≤B) (hs : ∀ j : Fin n,(s j.val).length≤B) :
    ∀ j : Fin n,(loopState s index p out bits rest acc j.val).length≤B := by
  intro j
  change (inputView n (loopState s index p out bits rest acc) j).length≤B
  rw [loopState_view s index p out bits rest acc ho hp]
  by_cases hj : j=index
  · subst j;simpa using hbits
  · simpa [Function.update,hj,inputView] using hs j

def coreLoop {n : ℕ} (work privateBase : ℕ) (index : Fin n) (bodyFalse bodyTrue : Block ℕ) : Block ℕ :=
  .loop privateBase (.seq bodyFalse (increment work index)) (.seq bodyTrue (increment work index))

/-- A real indexed Boolean-list loop, using a physical unary stack and an actual
binary increment circuit. The body premise is an actual Exec of fixed finite
syntax, and is discharged by structural compiler induction. -/
theorem coreLoop_exec {n : ℕ} (work p out : ℕ) (index : Fin n) (s : Store ℕ)
    (bodyFalse bodyTrue : Block ℕ) (pref : ℕ → Bool → List Bool) (M B C : ℕ)
    (ho : n≤out) (hp : out<p) (hwp : p+3≤work)
    (hw : Fresh s work (StackIndices.slots (incrementExpr index)))
    (hs : ∀ j : Fin n,(s j.val).length≤B) (hmB : M+1≤B)
    (hbody : ∀ i,i≤M → ∀ bit rest acc,
      ∃ t≤C,Exec (if bit then bodyTrue else bodyFalse)
        (loopState s index p out (StackCount.counterBits i) rest acc)
        (loopState s index p out (StackCount.counterBits i) rest (pref i bit++acc)) t)
    (xs : List Bool) (i : ℕ) (acc : List Bool) (hlen : i+xs.length≤M) :
    ∃ t≤xs.length*(C+(assignTime (incrementExpr index)).eval B+3)+1,
      Exec (coreLoop work p index bodyFalse bodyTrue)
        (loopState s index p out (StackCount.counterBits i) xs acc)
        (loopState s index p out (StackCount.counterBits (i+xs.length)) [] (loopValue pref i xs++acc)) t := by
  induction xs generalizing i acc with
  | nil =>
    refine ⟨1,by simp,?_⟩
    simpa [coreLoop,loopValue] using
      (Exec.loop_nil (f := .seq bodyFalse (increment work index)) (t := .seq bodyTrue (increment work index))
        (loopState_counter s index p out (StackCount.counterBits i) [] acc ho hp))
  | cons bit xs ih =>
    have him : i≤M := by simp only [List.length_cons] at hlen;omega
    obtain ⟨ta,hta,ha⟩ := hbody i him bit xs acc
    let before := loopState s index p out (StackCount.counterBits i) xs (pref i bit++acc)
    have hiwidth : (StackCount.counterBits i).length≤B := (StackCount.counterBits_width i).trans (by omega)
    have hwidth := loopState_width s index p out (StackCount.counterBits i) xs (pref i bit++acc) B ho hp hiwidth hs
    have hfresh := loopState_fresh s index p out work _ (StackCount.counterBits i) xs (pref i bit++acc) ho hp hwp hw
    obtain ⟨tb,htb,hb⟩ := assignExpr_exec work index (incrementExpr index) before B (by omega) hfresh hwidth
    have hresult : ((incrementExpr index).run (inputView n before)).1=StackCount.counterBits (i+1) := by
      have hbefore : before index.val=StackCount.counterBits i := loopState_index s index p out _ _ _ ho
      rw [increment_result,hbefore,StackCount.counterBits_succ]
    rw [hresult] at hb
    dsimp only [before] at hb
    rw [loopState_update_index s index p out _ _ xs (pref i bit++acc) ho] at hb
    have he : Exec (.seq (if bit then bodyTrue else bodyFalse) (increment work index))
        (Function.update (loopState s index p out (StackCount.counterBits i) (bit::xs) acc) p xs)
        (loopState s index p out (StackCount.counterBits (i+1)) xs (pref i bit++acc)) (ta+tb+1) := by
      rw [loopState_update_counter s index p out _ _ _ acc ho hp]
      exact Exec.seq ha hb
    obtain ⟨tc,htc,hc⟩ := ih (i+1) (pref i bit++acc) (by simp only [List.length_cons] at hlen;omega)
    have hpop : loopState s index p out (StackCount.counterBits i) (bit::xs) acc p=bit::xs :=
      loopState_counter s index p out _ _ _ ho hp
    have hh : Exec (coreLoop work p index bodyFalse bodyTrue)
        (loopState s index p out (StackCount.counterBits i) (bit::xs) acc)
        (loopState s index p out (StackCount.counterBits (i+1+xs.length)) [] (loopValue pref (i+1) xs++(pref i bit++acc)))
        ((ta+tb+1)+tc+2) := by
      cases bit
      · exact Exec.loop_false hpop he hc
      · exact Exec.loop_true hpop he hc
    refine ⟨(ta+tb+1)+tc+2,?_,?_⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · simpa only [List.length_cons,loopValue,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

end BalancedAssortments.CookLevin.StackBuilder
