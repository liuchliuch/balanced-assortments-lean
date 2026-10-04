import BalancedAssortments.CookLevinStackEmit

/-! Streaming ordinary CNF clauses with explicit finite template code. Each
literal's address is computed from the current binary register environment. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackEmit
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (inputView)

abbrev LiteralTemplate (n : ℕ) := BitExpr n × Bool

def templateSlots {n : ℕ} : List (LiteralTemplate n) → ℕ
  | [] => 3
  | l::ls => max (StackIndices.slots l.1) (templateSlots ls)
lemma templateSlots_three {n : ℕ} (ls : List (LiteralTemplate n)) : 3≤templateSlots ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih => exact ih.trans (Nat.le_max_right _ _)

def payloadFields {n : ℕ} (ls : List (LiteralTemplate n)) (s : Store ℕ) : List (List Bool) :=
  ls.flatMap (fun l => [[l.2],(l.1.run (inputView n s)).1])
def templateClause {n : ℕ} (ls : List (LiteralTemplate n)) (s : Store ℕ) : Encoding.BitClause :=
  ls.map (fun l => ⟨(l.1.run (inputView n s)).1,l.2⟩)

lemma encodeFields_append (xs ys : List (List Bool)) :
    Encoding.encodeFields (xs++ys)=Encoding.encodeFields xs++Encoding.encodeFields ys := by
  induction xs <;> simp_all [Encoding.encodeFields,List.append_assoc]
lemma clauseFields_template {n : ℕ} (ls : List (LiteralTemplate n)) (s : Store ℕ) :
    Encoding.clauseFields (templateClause ls s)=payloadFields ls s++[[]] := by
  induction ls <;> simp_all [templateClause,payloadFields,Encoding.clauseFields]

def emitLiterals {n : ℕ} (base out : ℕ) : List (LiteralTemplate n) → Block ℕ
  | [] => .skip
  | l::ls => .seq (emitLiterals base out ls) (emitLiteral base out l.1 l.2)
noncomputable def literalsTime {n : ℕ} : List (LiteralTemplate n) → Polynomial ℕ
  | [] => 1
  | l::ls => literalsTime ls+emitLiteralTime l.1+1

lemma payloadFields_update {n : ℕ} (ls : List (LiteralTemplate n)) (s : Store ℕ)
    (out : ℕ) (bits : List Bool) (ho : n≤out) :
    payloadFields ls (Function.update s out bits)=payloadFields ls s := by
  simp only [payloadFields,StackIndices.inputView_update n out s bits ho]

lemma emitLiterals_exec {n : ℕ} (base out : ℕ) (ls : List (LiteralTemplate n)) (s : Store ℕ) (w : ℕ)
    (hi : n≤out) (ho : out<base) (hf : Fresh s base (templateSlots ls))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(literalsTime ls).eval w,
      Exec (emitLiterals base out ls) s
        (Function.update s out (Encoding.encodeFields (payloadFields ls s)++s out)) t := by
  induction ls generalizing s with
  | nil => refine ⟨1,by simp [literalsTime],?_⟩;simpa [emitLiterals,payloadFields,Encoding.encodeFields] using Exec.skip s
  | cons l ls ih =>
    have hft : Fresh s base (templateSlots ls) := hf.subrange (by omega) (by simp only [templateSlots];omega)
    obtain ⟨ta,hta,ha⟩ := ih s hft hw
    let prefixBits := Encoding.encodeFields (payloadFields ls s)
    let u := Function.update s out (prefixBits++s out)
    have hfu : Fresh u base (StackIndices.slots l.1) :=
      (hf.subrange (by omega) (by simp only [templateSlots];omega)).update_outside (Or.inl ho) _
    have hview : inputView n u=inputView n s := StackIndices.inputView_update n out s _ hi
    have hwu : ∀ i : Fin n,(u i.val).length≤w := by
      intro i;change (inputView n u i).length≤w;rw [hview];exact hw i
    obtain ⟨tb,htb,hb⟩ := emitLiteral_exec base out l.1 l.2 u w (by omega) ho hfu hwu
    rw [hview] at hb
    have he : Function.update u out
        (Encoding.encodePayload [l.2]++Encoding.encodePayload (l.1.run (inputView n s)).1++u out)=
        Function.update s out (Encoding.encodeFields (payloadFields (l::ls) s)++s out) := by
      simp [u,prefixBits,payloadFields,Encoding.encodeFields,List.append_assoc,encodeFields_append]
    rw [he] at hb
    refine ⟨ta+tb+1,?_,Exec.seq ha hb⟩
    simp only [literalsTime,Polynomial.eval_add,Polynomial.eval_one]
    omega

def emitClause {n : ℕ} (base out : ℕ) (ls : List (LiteralTemplate n)) : Block ℕ :=
  .seq (emitConst base out []) (.seq (emitLiterals base out ls) (emitConst base out [true]))
noncomputable def clauseTime {n : ℕ} (ls : List (LiteralTemplate n)) : Polynomial ℕ := literalsTime ls+27

def clausePrefix {n : ℕ} (ls : List (LiteralTemplate n)) (s : Store ℕ) : List Bool :=
  Encoding.encodeFields ([true]::Encoding.clauseFields (templateClause ls s))

/-- Exact original CNF grammar: a clause tag, polarity/address field pairs,
and the empty-field clause terminator. Empty clauses are represented literally. -/
theorem emitClause_exec {n : ℕ} (base out : ℕ) (ls : List (LiteralTemplate n)) (s : Store ℕ) (w : ℕ)
    (hi : n≤out) (ho : out<base) (hf : Fresh s base (templateSlots ls))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(clauseTime ls).eval w,
      Exec (emitClause base out ls) s (Function.update s out (clausePrefix ls s++s out)) t := by
  have hf3 : Fresh s base 3 := hf.subrange (by omega) (by have := templateSlots_three ls;omega)
  have h0 := emitConst_exec base out [] s ho hf3
  let u := Function.update s out (Encoding.encodePayload []++s out)
  have hfu : Fresh u base (templateSlots ls) := hf.update_outside (Or.inl ho) _
  have hview : inputView n u=inputView n s := StackIndices.inputView_update n out s _ hi
  have hwu : ∀ i : Fin n,(u i.val).length≤w := by
    intro i;change (inputView n u i).length≤w;rw [hview];exact hw i
  obtain ⟨t,ht,h1⟩ := emitLiterals_exec base out ls u w hi ho hfu hwu
  rw [payloadFields_update ls s out _ hi] at h1
  let v := Function.update u out (Encoding.encodeFields (payloadFields ls s)++u out)
  have hfv : Fresh v base 3 :=
    (hfu.subrange (by omega) (by have := templateSlots_three ls;omega)).update_outside (Or.inl ho) _
  have h2 := emitConst_exec base out [true] v ho hfv
  have he : Function.update v out (Encoding.encodePayload [true]++v out)=
      Function.update s out (clausePrefix ls s++s out) := by
    simp [v,u,clausePrefix,clauseFields_template,encodeFields_append,Encoding.encodeFields,List.append_assoc]
  rw [he] at h2
  refine ⟨8+(t+17+1)+1,?_,?_⟩
  · simp only [clauseTime,Polynomial.eval_add,Polynomial.eval_ofNat];omega
  · simpa using Exec.seq h0 (Exec.seq h1 h2)

end BalancedAssortments.CookLevin.StackEmit
