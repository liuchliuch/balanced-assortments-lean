import BalancedAssortments.NPStackTapeMachine

namespace BalancedAssortments.NPStack.TapeMachine
open NPMachine NPMachine.FiniteBridge
variable {K : Type*} [Fintype K] [DecidableEq K]

lemma lookup_snoc (xs : List Bool) (b : Bool) (i : ℕ) :
    (xs++[b])[i]? = if i=xs.length then some b else xs[i]? := by
  by_cases he : i=xs.length
  · subst i; simp
  · rw [if_neg he]
    by_cases hi : i<xs.length
    · exact List.getElem?_append_left hi
    · rw [List.getElem?_eq_none (by simp;omega),List.getElem?_eq_none (by omega)]

lemma track_write (a : Symbol (Cell K)) (k j : K) (b : Option Bool) :
    (readCell (writeTrack a k b)).2 j = if j=k then b else (readCell a).2 j := by
  simp [writeTrack,readCell,Function.update_apply]

lemma bottom_write (a : Symbol (Cell K)) (k : K) (b : Option Bool) :
    (readCell (writeTrack a k b)).1=(readCell a).1 := rfl

lemma update_bottom (stk : K → List Bool) (tape : Tape K) (h : Represents stk tape)
    (k : K) (j : ℤ) (b : Option Bool) :
    ∀ p,(readCell ((Function.update tape j (writeTrack (tape j) k b)) p)).1=decide (p=0) := by
  intro p
  by_cases hp : p=j
  · subst p
    simpa only [Function.update_self,bottom_write] using h.1 j
  · simpa only [Function.update_of_ne hp] using h.1 p

lemma push_represents (stk : K → List Bool) (tape : Tape K) (h : Represents stk tape)
    (k : K) (b : Bool) :
    Represents (Function.update stk k (b::stk k))
      (Function.update tape (stk k).length (writeTrack (tape (stk k).length) k (some b))) := by
  refine ⟨update_bottom stk tape h k _ _,?_⟩
  intro j p
  by_cases hp : p=((stk k).length : ℤ)
  · subst p
    rw [Function.update_self,track_write]
    by_cases hj : j=k
    · subst j
      simp [Function.update_self,List.reverse_cons]
    · rw [if_neg hj,Function.update_of_ne hj]
      exact h.2 j _
  · rw [Function.update_of_ne hp]
    by_cases hj : j=k
    · subst j
      rw [Function.update_self,h.2 k p]
      by_cases hpos : 0≤p
      · simp only [if_pos hpos,List.reverse_cons,lookup_snoc,List.length_reverse]
        rw [if_neg (show p.toNat ≠ (stk k).length from by omega)]
      · simp [hpos]
    · rw [Function.update_of_ne hj]
      exact h.2 j p

lemma pop_represents (stk : K → List Bool) (tape : Tape K) (h : Represents stk tape)
    (k : K) (b : Bool) (bs : List Bool) (hk : stk k=b::bs) :
    Represents (Function.update stk k bs)
      (Function.update tape bs.length (writeTrack (tape bs.length) k none)) := by
  refine ⟨update_bottom stk tape h k _ _,?_⟩
  intro j p
  by_cases hp : p=(bs.length : ℤ)
  · subst p
    rw [Function.update_self,track_write]
    by_cases hj : j=k
    · subst j
      simp
    · rw [if_neg hj,Function.update_of_ne hj]
      exact h.2 j _
  · rw [Function.update_of_ne hp]
    by_cases hj : j=k
    · subst j
      rw [Function.update_self,h.2 k p,hk]
      by_cases hpos : 0≤p
      · simp only [if_pos hpos,List.reverse_cons,lookup_snoc,List.length_reverse]
        rw [if_neg (show p.toNat ≠ bs.length from by omega)]
      · simp [hpos]
    · rw [Function.update_of_ne hj]
      exact h.2 j p

end BalancedAssortments.NPStack.TapeMachine
