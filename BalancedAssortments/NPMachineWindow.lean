import BalancedAssortments.NPMachineModel

/-! Finite tape windows with exact simulation into the concrete integer-indexed
machine. The padding width is input length + 2T + 1, not an assumed oracle bound. -/
noncomputable section
namespace BalancedAssortments.NPMachine

structure WindowConfig (M : Machine) (W : ℕ) where
  state : Fin (M.stateExtra+1)
  head : Fin W
  tape : Fin W → Fin (M.symbolExtra+3)

@[ext] theorem Config.ext {M : Machine} {c d : Config M}
    (hs : c.state=d.state) (hh : c.head=d.head) (ht : c.tape=d.tape) : c=d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl

@[ext] theorem WindowConfig.ext {M : Machine} {W : ℕ} {c d : WindowConfig M W}
    (hs : c.state=d.state) (hh : c.head=d.head) (ht : c.tape=d.tape) : c=d := by
  cases c
  cases d
  cases hs
  cases hh
  cases ht
  rfl

def position (T : ℕ) {W : ℕ} (i : Fin W) : ℤ := (i.val : ℤ)-T

lemma position_injective (T W : ℕ) : Function.Injective (position T (W := W)) := by
  intro i j h
  apply Fin.ext
  have hh : (i.val : ℤ) = j.val := by unfold position at h; linarith
  exact_mod_cast hh

lemma position_range (T W : ℕ) (k : ℤ) :
    (∃ i : Fin W, position T i = k) ↔ -(T : ℤ) ≤ k ∧ k < (W : ℤ)-T := by
  constructor
  · rintro ⟨i,rfl⟩
    have hi := i.isLt
    have hi' : (i.val : ℤ) < W := by exact_mod_cast hi
    have hi0 : (0 : ℤ) ≤ i.val := by positivity
    unfold position
    constructor <;> linarith
  · rintro ⟨hl,hu⟩
    have hp : 0 ≤ k+T := by linarith
    have hu' : k+T < W := by linarith
    have hn : (k+T).toNat < W := by omega
    refine ⟨⟨(k+T).toNat,hn⟩,?_⟩
    unfold position
    rw [Int.toNat_of_nonneg hp]
    ring

def liftWindow (M : Machine) (T : ℕ) {W : ℕ} (c : WindowConfig M W) : Config M :=
  ⟨c.state,position T c.head,
    Function.extend (position T) c.tape (fun _ => blank M)⟩

lemma liftWindow_tape (M : Machine) (T : ℕ) {W : ℕ} (c : WindowConfig M W) (i : Fin W) :
    (liftWindow M T c).tape (position T i) = c.tape i := by
  change Function.extend (position T) c.tape (fun _ => blank M) (position T i)=c.tape i
  exact (position_injective T W).extend_apply c.tape (fun _ => blank M) i

lemma extend_update {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    (e : α → β) (he : Function.Injective e) (f : α → γ) (default : β → γ) (i : α) (v : γ) :
    Function.extend e (Function.update f i v) default =
      Function.update (Function.extend e f default) (e i) v := by
  funext x
  by_cases hx : ∃ j,e j=x
  · obtain ⟨j,rfl⟩ := hx
    rw [he.extend_apply]
    by_cases hj : j=i
    · subst j; simp
    · have hje : e j ≠ e i := fun h => hj (he h)
      rw [Function.update_of_ne hj,Function.update_of_ne hje,he.extend_apply]
  · have hxi : x ≠ e i := by intro h; apply hx; exact ⟨i,h.symm⟩
    rw [Function.extend_apply' _ _ _ hx,Function.update_of_ne hxi,Function.extend_apply' _ _ _ hx]

/-- Finite-window transition semantics use the same global transition record.
An attempted head move outside the finite window has no successor. -/
def WindowStep (M : Machine) {W : ℕ} (c d : WindowConfig M W) : Prop :=
  ∃ r ∈ M.rules,
    c.state=r.source ∧ c.tape c.head=r.read ∧ d.state=r.target ∧
    (d.head.val : ℤ)=(c.head.val : ℤ)+r.move.displacement ∧
    d.tape=Function.update c.tape c.head r.write

def WindowAccepts (M : Machine) {W : ℕ} (c : WindowConfig M W) : Prop := M.accepting c.state=true

def WindowPaddedStep (M : Machine) {W : ℕ} (c d : WindowConfig M W) : Prop :=
  WindowStep M c d ∨ (WindowAccepts M c ∧ d=c)

lemma windowStep_lifts (M : Machine) (T : ℕ) {W : ℕ} {c d : WindowConfig M W}
    (h : WindowStep M c d) : Step M (liftWindow M T c) (liftWindow M T d) := by
  obtain ⟨r,hr,hstate,hread,htarget,hhead,htape⟩ := h
  refine ⟨r,hr,⟨hstate,?_⟩,?_⟩
  · change (liftWindow M T c).tape (position T c.head)=r.read
    rw [liftWindow_tape]
    exact hread
  · apply Config.ext
    · exact htarget
    · change position T d.head = position T c.head+r.move.displacement
      unfold position
      linarith
    · change Function.extend (position T) d.tape (fun _ => blank M) =
        Function.update (Function.extend (position T) c.tape (fun _ => blank M))
          (position T c.head) r.write
      rw [htape,extend_update _ (position_injective T W)]

lemma windowPaddedStep_lifts (M : Machine) (T : ℕ) {W : ℕ} {c d : WindowConfig M W}
    (h : WindowPaddedStep M c d) : PaddedStep M (liftWindow M T c) (liftWindow M T d) := by
  rcases h with h | ⟨ha,rfl⟩
  · exact Or.inl (windowStep_lifts M T h)
  · exact Or.inr ⟨ha,rfl⟩

def projectWindow (M : Machine) (T W : ℕ) (c : Config M)
    (hc : ∃ i : Fin W,position T i=c.head) : WindowConfig M W :=
  ⟨c.state,Classical.choose hc,fun i => c.tape (position T i)⟩

lemma projectWindow_head (M : Machine) (T W : ℕ) (c : Config M)
    (hc : ∃ i : Fin W,position T i=c.head) :
    position T (projectWindow M T W c hc).head=c.head := Classical.choose_spec hc

lemma step_projects (M : Machine) (T W : ℕ) {c d : Config M}
    (hc : ∃ i : Fin W,position T i=c.head) (hd : ∃ i : Fin W,position T i=d.head)
    (h : Step M c d) : WindowStep M (projectWindow M T W c hc) (projectWindow M T W d hd) := by
  obtain ⟨r,hr,⟨hstate,hread⟩,rfl⟩ := h
  refine ⟨r,hr,hstate,?_,rfl,?_,?_⟩
  · change c.tape (position T (Classical.choose hc))=r.read
    rw [Classical.choose_spec hc]
    exact hread
  · have hch := projectWindow_head M T W c hc
    have hdh := projectWindow_head M T W (execute c r) hd
    dsimp only [position,execute,projectWindow] at hch hdh
    change ((Classical.choose hd).val : ℤ) = ((Classical.choose hc).val : ℤ)+r.move.displacement
    linarith
  · funext j
    change Function.update c.tape c.head r.write (position T j) =
      Function.update (fun i => c.tape (position T i)) (Classical.choose hc) r.write j
    by_cases hj : j=Classical.choose hc
    · subst j
      have he : position T (Classical.choose hc)=c.head := Classical.choose_spec hc
      rw [he]
      simp
    · have hneq : position T j ≠ c.head := fun h =>
        hj (position_injective T W (h.trans (Classical.choose_spec hc).symm))
      rw [Function.update_of_ne hneq,Function.update_of_ne hj]

lemma paddedStep_projects (M : Machine) (T W : ℕ) {c d : Config M}
    (hc : ∃ i : Fin W,position T i=c.head) (hd : ∃ i : Fin W,position T i=d.head)
    (h : PaddedStep M c d) : WindowPaddedStep M (projectWindow M T W c hc) (projectWindow M T W d hd) := by
  rcases h with h | ⟨ha,rfl⟩
  · exact Or.inl (step_projects M T W hc hd h)
  · exact Or.inr ⟨ha,rfl⟩

def windowWidth (word : List Bool) (T : ℕ) : ℕ := word.length+2*T+1

def windowInitial (M : Machine) (word : List Bool) (T : ℕ) : WindowConfig M (windowWidth word T) :=
  ⟨M.start,⟨T,by unfold windowWidth;omega⟩,fun i => inputTape M word (position T i)⟩

lemma inputTape_outside_window (M : Machine) (word : List Bool) (T : ℕ) (k : ℤ)
    (hk : ¬∃ i : Fin (windowWidth word T),position T i=k) : inputTape M word k=blank M := by
  rw [position_range] at hk
  by_cases hn : k<0
  · simp [inputTape,not_le.mpr hn]
  · have hn' : 0 ≤ k := le_of_not_gt hn
    have hlarge : (word.length : ℤ) ≤ k := by unfold windowWidth at hk; push_cast at hk; omega
    have hindex : word.length ≤ k.toNat := by omega
    simp [inputTape,hn',List.getElem?_eq_none hindex]

lemma lift_windowInitial (M : Machine) (word : List Bool) (T : ℕ) :
    liftWindow M T (windowInitial M word T)=initial M word := by
  apply Config.ext
  · rfl
  · simp [liftWindow,windowInitial,initial,position]
  · funext k
    by_cases hk : ∃ i : Fin (windowWidth word T),position T i=k
    · obtain ⟨i,rfl⟩ := hk
      exact liftWindow_tape M T (windowInitial M word T) i
    · dsimp only [liftWindow,windowInitial,initial]
      rw [Function.extend_apply' _ _ _ hk,inputTape_outside_window M word T k hk]

end BalancedAssortments.NPMachine
