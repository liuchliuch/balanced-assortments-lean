import BalancedAssortments.NPStackClockedFallback

namespace BalancedAssortments.NPStack.Clocked
open NPStack NPStack.Macros

def store {K CK : Type*} (clock : CK → List Bool) (source : Timeout.Stack K → List Bool) (work : List Bool) : Stack K CK → List Bool
  | .inl k => clock k
  | .inr (.inl k) => source k
  | .inr (.inr _) => work

lemma clock_run (P C : FiniteProgram) (fallback : List Bool) {t : ℕ} {c d : Config C.K C.Q}
    (h : Run C.program t c d) (s : Timeout.Stack P.K → List Bool) (w : List Bool) :
    Run (program P C fallback) t ⟨.clock c.pc,store c.stk s w⟩ ⟨.clock d.pc,store d.stk s w⟩ := by
  exact h.relocate_exact clockStack Label.clock Sum.inl_injective (clock_extends P C fallback)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => exact False.elim (hk k rfl)
        | inr k => cases k <;> rfl)

lemma timed_run (P C : FiniteProgram) (fallback : List Bool) {t : ℕ}
    {c d : Config (Timeout.Stack P.K) (Timeout.State P.Q)}
    (h : Run (Timeout.program P.program) t c d) (s : C.K → List Bool) (w : List Bool) :
    Run (program P C fallback) t ⟨.timed c.pc,store s c.stk w⟩ ⟨.timed d.pc,store s d.stk w⟩ := by
  exact h.relocate_exact timedStack Label.timed timedStack_injective (timed_extends P C fallback)
    ⟨rfl,fun _=>rfl⟩ ⟨rfl,fun _=>rfl⟩
    (by intro k hk;cases k with
        | inl k => rfl
        | inr k => cases k with
          | inl k => exact False.elim (hk k rfl)
          | inr u => rfl)

lemma initial_store (P C : FiniteProgram) (fallback word : List Bool) :
    initial (program P C fallback) word=
      ⟨.copyWord .readSource,store (initial C.program word).stk (fun _=>[]) []⟩ := by
  unfold initial program store clockStack
  congr 1
  funext k;cases k with
  | inl k => simp [Function.comp_def]
  | inr k => cases k <;> simp

lemma copy_word (P C : FiniteProgram) (fallback word : List Bool) :
    Run (program P C fallback) (5*word.length+3) (initial (program P C fallback) word)
      ⟨.clock C.program.start,store (initial C.program word).stk (Timeout.liftStore (initial P.program word).stk []) []⟩ := by
  let s0 := store (initial C.program word).stk (fun _ : Timeout.Stack P.K=>[]) []
  let s1 := store (initial C.program word).stk (Timeout.liftStore (initial P.program word).stk []) []
  have h := (copy_run word []).relocate_exact (wordMap P C) Label.copyWord (wordMap_injective P C) (word_extends P C fallback)
    (c' := ⟨.copyWord .readSource,s0⟩) (d' := ⟨.copyWord .done,s1⟩)
    ⟨rfl,by intro k;cases k <;> simp [s0,store,wordMap,clockStack,timedStack,scratch,initial,copyConfig,copyStacks]⟩
    ⟨rfl,by intro k;cases k <;> simp [s1,store,wordMap,clockStack,timedStack,scratch,initial,copyConfig,copyStacks,Timeout.liftStore]⟩
    (by
      intro k hk
      cases k with
      | inl k => rfl
      | inr k => cases k with
        | inl k => cases k with
          | inl k =>
            by_cases he : k=P.program.inputStack
            · subst k;exact False.elim (hk .target rfl)
            · simp [s0,s1,store,Timeout.liftStore,initial,he]
          | inr u => rfl
        | inr u => rfl)
  have hret : Step (program P C fallback) ⟨.copyWord .done,s1⟩ ⟨.clock C.program.start,s1⟩ := by
    simp [Step,successors,program,code,returnCode,copyProgram]
  rw [initial_store]
  convert h.trans (Run.one hret) using 1 <;> omega

lemma copy_fuel (P C : FiniteProgram) (fallback word fuel : List Bool) (cs : C.K → List Bool)
    (hc : cs C.program.outputStack=fuel) :
    Run (program P C fallback) (5*fuel.length+3)
      ⟨.copyFuel .readSource,store cs (Timeout.liftStore (initial P.program word).stk []) []⟩
      ⟨.timed (.tick P.program.start),store cs (Timeout.liftStore (initial P.program word).stk fuel) []⟩ := by
  let s0 := store cs (Timeout.liftStore (initial P.program word).stk []) []
  let s1 := store cs (Timeout.liftStore (initial P.program word).stk fuel) []
  have h := (copy_run fuel []).relocate_exact (fuelMap P C) Label.copyFuel (fuelMap_injective P C) (fuel_extends P C fallback)
    (c' := ⟨.copyFuel .readSource,s0⟩) (d' := ⟨.copyFuel .done,s1⟩)
    ⟨rfl,by intro k;cases k <;> simp [s0,store,fuelMap,clockStack,timedStack,scratch,copyConfig,copyStacks,Timeout.liftStore,hc]⟩
    ⟨rfl,by intro k;cases k <;> simp [s1,store,fuelMap,clockStack,timedStack,scratch,copyConfig,copyStacks,Timeout.liftStore,hc]⟩
    (by
      intro k hk
      cases k with
      | inl k => rfl
      | inr k => cases k with
        | inl k => cases k with
          | inl k => rfl
          | inr u => cases u;exact False.elim (hk .target rfl)
        | inr u => rfl)
  have hret : Step (program P C fallback) ⟨.copyFuel .done,s1⟩ ⟨.timed (.tick P.program.start),s1⟩ := by
    simp [Step,successors,program,code,returnCode,copyProgram]
  convert h.trans (Run.one hret) using 1 <;> omega

/-- Paid raw-input preparation: copy word, execute actual clock code, copy
physical fuel, then enter the timed source program. -/
theorem seed_run (P C : FiniteProgram) (fallback word fuel : List Bool) {t : ℕ} {c : Config C.K C.Q}
    (hr : Run C.program t (initial C.program word) c) (ha : accepts C.program c)
    (ho : c.stk C.program.outputStack=fuel) :
    Run (program P C fallback) (t+5*word.length+5*fuel.length+7)
      (initial (program P C fallback) word)
      ⟨.timed (.tick P.program.start),store c.stk (Timeout.liftStore (initial P.program word).stk fuel) []⟩ := by
  have h1 := copy_word P C fallback word
  have h2 := clock_run P C fallback hr (Timeout.liftStore (initial P.program word).stk []) []
  have h3 : Step (program P C fallback)
      ⟨.clock c.pc,store c.stk (Timeout.liftStore (initial P.program word).stk []) []⟩
      ⟨.copyFuel .readSource,store c.stk (Timeout.liftStore (initial P.program word).stk []) []⟩ := by
    change C.program.code c.pc=.halt true at ha
    simp [Step,successors,program,code,returnCode,ha]
  have h4 := copy_fuel P C fallback word fuel c.stk ho
  have hh := h1.trans (h2.trans (Run.succ h3 h4))
  convert hh using 1 <;> omega

end BalancedAssortments.NPStack.Clocked
