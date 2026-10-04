import BalancedAssortments.NPStackStructured

namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]
abbrev Store (K : Type*) := K → List Bool

/-- Source execution counts every pop, push, branch entry and return jump that
the finite control-graph compiler emits. This is an operational derivation. -/
inductive Exec : Block K → Store K → Store K → ℕ → Prop
  | skip (s) : Exec .skip s s 1
  | atom {p : Atom K} {s t : Store K} {n : ℕ} (input output : K) :
      Run (program (.atom p) input output) n ⟨p.start,s⟩ ⟨p.exit,t⟩ → Exec (.atom p) s t n
  | push (s) (k) (bit) : Exec (.push k bit) s (Function.update s k (bit::s k)) 1
  | seq {a b s u v n m} : Exec a s u n → Exec b u v m → Exec (.seq a b) s v (n+m+1)
  | branch_nil {k e f t s v n} : s k=[] → Exec e s v n → Exec (.branch k e f t) s v (n+2)
  | branch_false {k e f t s v bs n} : s k=false::bs → Exec f (Function.update s k bs) v n → Exec (.branch k e f t) s v (n+2)
  | branch_true {k e f t s v bs n} : s k=true::bs → Exec t (Function.update s k bs) v n → Exec (.branch k e f t) s v (n+2)
  | loop_nil {k f t s} : s k=[] → Exec (.loop k f t) s s 1
  | loop_false {k f t s u v bs n m} : s k=false::bs → Exec f (Function.update s k bs) u n →
      Exec (.loop k f t) u v m → Exec (.loop k f t) s v (n+m+2)
  | loop_true {k f t s u v bs n m} : s k=true::bs → Exec t (Function.update s k bs) u n →
      Exec (.loop k f t) u v m → Exec (.loop k f t) s v (n+m+2)

lemma sameStore_lift {Q R : Type*} {P : Program K Q} {S : Program K R} (fq : Q → R)
    (hc : CodeExtends P S id fq) {n : ℕ} {q r : Q} {s t : Store K}
    (h : Run P n ⟨q,s⟩ ⟨r,t⟩) : Run S n ⟨fq q,s⟩ ⟨fq r,t⟩ := by
  apply h.relocate_exact id fq Function.injective_id hc
  · exact ⟨rfl,fun _ => rfl⟩
  · exact ⟨rfl,fun _ => rfl⟩
  · intro k hk; exact False.elim (hk k rfl)

lemma seq_left_extends (a b : Block K) (input output : K) :
    CodeExtends (program a input output) (program (.seq a b) input output) id Sum.inl := by
  intro q hq
  have hn : q≠finish a := by intro he;subst q;exact hq true (code_finish a)
  simp [program,code,hn]
lemma seq_right_extends (a b : Block K) (input output : K) :
    CodeExtends (program b input output) (program (.seq a b) input output) id Sum.inr := by intro q hq;rfl
lemma branch_empty_extends (k : K) (e f t : Block K) (input output : K) :
    CodeExtends (program e input output) (program (.branch k e f t) input output) id (fun q => .inr (.inl q)) := by
  intro q hq
  have hn : q≠finish e := by intro he;subst q;exact hq true (code_finish e)
  simp [program,code,hn]
lemma branch_false_extends (k : K) (e f t : Block K) (input output : K) :
    CodeExtends (program f input output) (program (.branch k e f t) input output) id (fun q => .inr (.inr (.inl q))) := by
  intro q hq
  have hn : q≠finish f := by intro he;subst q;exact hq true (code_finish f)
  simp [program,code,hn]
lemma branch_true_extends (k : K) (e f t : Block K) (input output : K) :
    CodeExtends (program t input output) (program (.branch k e f t) input output) id (fun q => .inr (.inr (.inr q))) := by
  intro q hq
  have hn : q≠finish t := by intro he;subst q;exact hq true (code_finish t)
  simp [program,code,hn]
lemma loop_false_extends (k : K) (f t : Block K) (input output : K) :
    CodeExtends (program f input output) (program (.loop k f t) input output) id (fun q => .inr (.inl q)) := by
  intro q hq
  have hn : q≠finish f := by intro he;subst q;exact hq true (code_finish f)
  simp [program,code,hn]
lemma loop_true_extends (k : K) (f t : Block K) (input output : K) :
    CodeExtends (program t input output) (program (.loop k f t) input output) id (fun q => .inr (.inr q)) := by
  intro q hq
  have hn : q≠finish t := by intro he;subst q;exact hq true (code_finish t)
  simp [program,code,hn]

/-- Every source derivation becomes an exact-count run of finite primitive
Boolean-stack bytecode. Loop back edges are explicit jumps. -/
theorem Exec.compiles {b : Block K} {s t : Store K} {n : ℕ} (h : Exec b s t n) (input output : K) :
    Run (program b input output) n ⟨entry b,s⟩ ⟨finish b,t⟩ := by
  induction h with
  | @atom p s t n i o hr =>
    exact sameStore_lift id (by intro q hq; change p.instructions q=(p.instructions q).rename id id; cases p.instructions q <;> rfl) hr
  | skip s => exact Run.one (by simp [Step,successors,program,code,entry,finish])
  | push s k bit => exact Run.one (by simp [Step,successors,program,code,entry,finish])
  | @seq a b s u v n m ha hb iha ihb =>
    have h1 := sameStore_lift Sum.inl (seq_left_extends a b input output) iha
    have h2 := sameStore_lift Sum.inr (seq_right_extends a b input output) ihb
    have hj : Step (program (.seq a b) input output) ⟨.inl (finish a),u⟩ ⟨.inr (entry b),u⟩ := by
      simp [Step,successors,program,code]
    simpa [entry,finish,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1.trans (Run.succ hj h2)
  | @branch_nil k e f t s v n hs he ih =>
    have hh := sameStore_lift (fun q => Sum.inr (Sum.inl q)) (branch_empty_extends k e f t input output) ih
    have hj : Step (program (.branch k e f t) input output) ⟨.inr (.inl (finish e)),v⟩ ⟨.inl true,v⟩ := by
      simp [Step,successors,program,code]
    have hp : Step (program (.branch k e f t) input output) ⟨.inl false,s⟩ ⟨.inr (.inl (entry e)),s⟩ := by
      simp [Step,successors,program,code,hs]
    simpa [entry,finish,Nat.add_assoc] using Run.succ hp (hh.trans (Run.one hj))
  | @branch_false k e f t s v bs n hs he ih =>
    have hh := sameStore_lift (fun q => Sum.inr (Sum.inr (Sum.inl q))) (branch_false_extends k e f t input output) ih
    have hj : Step (program (.branch k e f t) input output) ⟨.inr (.inr (.inl (finish f))),v⟩ ⟨.inl true,v⟩ := by
      simp [Step,successors,program,code]
    have hp : Step (program (.branch k e f t) input output) ⟨.inl false,s⟩ ⟨.inr (.inr (.inl (entry f))),Function.update s k bs⟩ := by
      simp [Step,successors,program,code,hs]
    simpa [entry,finish,Nat.add_assoc] using Run.succ hp (hh.trans (Run.one hj))
  | @branch_true k e f t s v bs n hs he ih =>
    have hh := sameStore_lift (fun q => Sum.inr (Sum.inr (Sum.inr q))) (branch_true_extends k e f t input output) ih
    have hj : Step (program (.branch k e f t) input output) ⟨.inr (.inr (.inr (finish t))),v⟩ ⟨.inl true,v⟩ := by
      simp [Step,successors,program,code]
    have hp : Step (program (.branch k e f t) input output) ⟨.inl false,s⟩ ⟨.inr (.inr (.inr (entry t))),Function.update s k bs⟩ := by
      simp [Step,successors,program,code,hs]
    simpa [entry,finish,Nat.add_assoc] using Run.succ hp (hh.trans (Run.one hj))
  | loop_nil hs => exact Run.one (by simp [Step,successors,program,code,entry,finish,hs])
  | @loop_false k f t s u v bs n m hs hb hl ihb ihl =>
    have hh := sameStore_lift (fun q => Sum.inr (Sum.inl q)) (loop_false_extends k f t input output) ihb
    have hj : Step (program (.loop k f t) input output) ⟨.inr (.inl (finish f)),u⟩ ⟨.inl false,u⟩ := by
      simp [Step,successors,program,code]
    have hp : Step (program (.loop k f t) input output) ⟨.inl false,s⟩ ⟨.inr (.inl (entry f)),Function.update s k bs⟩ := by
      simp [Step,successors,program,code,hs]
    simpa [entry,finish,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.succ hp (hh.trans (Run.succ hj ihl))
  | @loop_true k f t s u v bs n m hs hb hl ihb ihl =>
    have hh := sameStore_lift (fun q => Sum.inr (Sum.inr q)) (loop_true_extends k f t input output) ihb
    have hj : Step (program (.loop k f t) input output) ⟨.inr (.inr (finish t)),u⟩ ⟨.inl false,u⟩ := by
      simp [Step,successors,program,code]
    have hp : Step (program (.loop k f t) input output) ⟨.inl false,s⟩ ⟨.inr (.inr (entry t)),Function.update s k bs⟩ := by
      simp [Step,successors,program,code,hs]
    simpa [entry,finish,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.succ hp (hh.trans (Run.succ hj ihl))

end BalancedAssortments.NPStack.Structured
