import BalancedAssortments.CookLevinRawInitial

namespace BalancedAssortments.CookLevin.StackTableau
open NPMachine

lemma initial_hl (M : Machine) (word : List Bool) (T : ℕ) (p : Fin T) : ((windowInitial M word T).tape ⟨p.val,by unfold windowWidth;omega⟩).val=2 := by
  have hn : ¬0≤(p.val : ℤ)-(T : ℤ) := by omega
  change (inputTape M word ((p.val : ℤ)-(T : ℤ))).val=2
  rw [inputTape,if_neg hn]
  rfl

lemma initial_hm (M : Machine) (word : List Bool) (T : ℕ) (p : Fin word.length) :
    ((windowInitial M word T).tape ⟨T+p.val,by unfold windowWidth;omega⟩).val=word[p.val].toNat := by
  have hn : 0≤((T+p.val : ℕ) : ℤ)-(T : ℤ) := by omega
  have he : (((T+p.val : ℕ) : ℤ)-(T : ℤ)).toNat=p.val := by omega
  change (inputTape M word (((T+p.val : ℕ) : ℤ)-(T : ℤ))).val=word[p.val].toNat
  rw [inputTape,if_pos hn,he,List.getElem?_eq_getElem p.isLt]
  cases hb : word[p.val] <;> simp [bitSymbol,hb]

lemma initial_hr (M : Machine) (word : List Bool) (T : ℕ) (p : Fin (T+1)) :
    ((windowInitial M word T).tape ⟨T+word.length+p.val,by unfold windowWidth;omega⟩).val=2 := by
  have hn : 0≤((T+word.length+p.val : ℕ) : ℤ)-(T : ℤ) := by omega
  have he : (((T+word.length+p.val : ℕ) : ℤ)-(T : ℤ)).toNat=word.length+p.val := by omega
  change (inputTape M word (((T+word.length+p.val : ℕ) : ℤ)-(T : ℤ))).val=2
  rw [inputTape,if_pos hn,he,List.getElem?_eq_none (show word.length≤word.length+p.val by omega)]
  rfl

/-- The three physical initialization loops cover exactly the finite tape,
including the extra right blank and the empty-input/zero-clock cases. -/
theorem initial_partition (M : Machine) (word : List Bool) (T : ℕ) (P : ℕ → ℕ → Prop) :
    (∀ p : Fin (windowWidth word T),P p.val ((windowInitial M word T).tape p).val) ↔
      (∀ p : Fin T,P p.val 2) ∧
      (∀ p : Fin word.length,P (T+p.val) (word[p.val].toNat)) ∧
      (∀ p : Fin (T+1),P (T+word.length+p.val) 2) := by
  have hl := initial_hl M word T
  have hm := initial_hm M word T
  have hr := initial_hr M word T
  constructor
  · intro h
    refine ⟨fun p => ?_,fun p => ?_,fun p => ?_⟩
    · simpa only [hl p] using h ⟨p.val,by unfold windowWidth;omega⟩
    · simpa only [hm p] using h ⟨T+p.val,by unfold windowWidth;omega⟩
    · simpa only [hr p] using h ⟨T+word.length+p.val,by unfold windowWidth;omega⟩
  · rintro ⟨hleft,hmid,hright⟩ p
    by_cases hp : p.val<T
    · have he : ((windowInitial M word T).tape p).val=2 := hl ⟨p.val,hp⟩
      rw [he];exact hleft ⟨p.val,hp⟩
    · by_cases hm' : p.val<T+word.length
      · let j : Fin word.length := ⟨p.val-T,by omega⟩
        have hj : T+j.val=p.val := by dsimp [j];omega
        have he := hm j
        have hh := hmid j
        rw [← he] at hh
        simpa only [hj] using hh
      · let j : Fin (T+1) := ⟨p.val-(T+word.length),by have := p.isLt;unfold windowWidth at this;omega⟩
        have hj : T+word.length+j.val=p.val := by dsimp [j];omega
        have he := hr j
        have hh := hright j
        rw [← he] at hh
        simpa only [hj] using hh
end BalancedAssortments.CookLevin.StackTableau
