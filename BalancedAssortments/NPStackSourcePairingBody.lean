import BalancedAssortments.NPStackSourcePairingReject
import BalancedAssortments.NPStackEmbeddingSound

namespace BalancedAssortments.NPStackSourcePairing
open NPStack
variable {W Q : Type*} [DecidableEq W]

def bodyConfig (s c scratch : List Bool) (x : Config (Fin 9 ⊕ W) Q) : Config (Stack W) (State Q) :=
  cfg (.body x.pc) s c scratch (fun i => x.stk (.inl i)) (fun w => x.stk (.inr w))

lemma bodyConfig_relocated (s c scratch : List Bool) (x : Config (Fin 9 ⊕ W) Q) :
    Relocated Stack.body State.body x (bodyConfig s c scratch x) := by
  refine ⟨rfl,?_⟩;intro k;cases k <;> rfl

lemma bodyConfig_frame (s c scratch : List Bool) (x y : Config (Fin 9 ⊕ W) Q) :
    Frame Stack.body (bodyConfig s c scratch x) (bodyConfig s c scratch y) := by
  intro k hk
  cases k with
  | source => rfl
  | certificate => rfl
  | scratch => rfl
  | body k => exact (hk k rfl).elim

lemma body_not_accepting (body : Program (Fin 9 ⊕ W) Q) (q : Q) :
    (program body).code (.body q)≠.halt true := by
  cases h : body.code q <;> simp [program,h,Instr.rename]
  rename_i b
  cases b <;> simp [program,h]

/-- Recover a literal finite body execution from any accepting wrapper run.
The body may be nondeterministic; protected stream tracks cannot be modified. -/
theorem body_segment (body : Program (Fin 9 ⊕ W) Q) (s c scratch : List Bool)
    (x : Config (Fin 9 ⊕ W) Q) {T : ℕ} {d : Config (Stack W) (State Q)}
    (hr : Run (program body) T (bodyConfig s c scratch x) d) (ha : accepts (program body) d) :
    ∃ u v e,Run body u x e ∧ body.code e.pc=.halt true ∧
      Run (program body) v
        (cfg .probe s c scratch (fun i => e.stk (.inl i)) (fun w => e.stk (.inr w))) d ∧ u+1+v=T := by
  induction T generalizing x with
  | zero =>
    cases hr
    exact False.elim (body_not_accepting body x.pc ha)
  | succ T ih =>
    cases hr with
    | @succ _ _ next _ hs htail =>
      by_cases hhalt : ∃ b,body.code x.pc=.halt b
      · obtain ⟨b,hb⟩ := hhalt
        cases b with
        | false => simp [Step,successors,program,bodyConfig,cfg,hb] at hs
        | true =>
          have he : next=cfg .probe s c scratch (fun i => x.stk (.inl i)) (fun w => x.stk (.inr w)) := by
            simpa [Step,successors,program,bodyConfig,cfg,hb] using hs
          rw [he] at htail
          exact ⟨0,T,x,.zero _,hb,htail,by omega⟩
      · have hn : ∀ b,body.code x.pc≠.halt b := by simpa using hhalt
        obtain ⟨y,hxy,hrel,hframe⟩ := hs.reflect Stack.body State.body
          (by intro a b h;cases h;rfl) (body_code body) (bodyConfig_relocated s c scratch x) hn
        have he := relocated_frame_unique Stack.body State.body hrel
          (bodyConfig_relocated s c scratch y) hframe (bodyConfig_frame s c scratch x y)
        rw [he] at htail
        obtain ⟨u,v,e,hu,hb,hrest,ht⟩ := ih y htail
        exact ⟨u+1,v,e,.succ hxy hu,hb,hrest,by omega⟩

end BalancedAssortments.NPStackSourcePairing
