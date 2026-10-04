import BalancedAssortments.CookLevinStackIndicesCorrect
import BalancedAssortments.NPStackStructuredFieldAtoms

/-! Actual finite-stack literal emission. Label bits are computed by compiled
binary circuits and self-delimiting fields are pushed by primitive bytecode. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackEmit
open NPCNF NPStack NPStack.Structured ComplexityTimeBinary
open StackClock (Fresh)
open StackIndices (pushBits pushBits_exec inputView)

lemma encodeMap_injective {base out : ℕ} (h : out<base) :
    Function.Injective (Macros.encodeMap base (base+1) (base+2) out) := by
  intro i j he
  cases i <;> cases j <;> simp only [Macros.encodeMap] at he <;> first | rfl | omega

lemma cleared_output (s : Store ℕ) (base out : ℕ) (bits result : List Bool) (h : s base=[]) :
    Macros.writes (Function.update s base bits) [(base,[]),(out,result)]=Function.update s out result := by
  simp only [Macros.writes,Function.update_idem]
  have hh : Function.update s base []=s := by rw [← h];exact Function.update_eq_self base s
  rw [hh]

def emitConst (base out : ℕ) (bits : List Bool) : Block ℕ :=
  .seq (pushBits base bits) (.atom (encodeAtom base (base+1) (base+2) out))

lemma emitConst_exec (base out : ℕ) (bits : List Bool) (s : Store ℕ) (ho : out<base)
    (hf : Fresh s base 3) :
    Exec (emitConst base out bits) s
      (Function.update s out (Encoding.encodePayload bits++s out)) (9*bits.length+8) := by
  have h0 : s base=[] := hf base (by omega) (by omega)
  have h1 : s (base+1)=[] := hf (base+1) (by omega) (by omega)
  have h2 : s (base+2)=[] := hf (base+2) (by omega) (by omega)
  have ha := pushBits_exec base bits s
  rw [h0,List.append_nil] at ha
  let u := Function.update s base bits
  have hu : u base=bits := by simp [u]
  have huout : u out=s out := by simp [u,Function.update,show out≠base by omega]
  have hu1 : u (base+1)=[] := by simp [u,Function.update,h1]
  have hu2 : u (base+2)=[] := by simp [u,Function.update,h2]
  have hb := encodeAtom_exec base (base+1) (base+2) out (encodeMap_injective ho) u hu1 hu2
  rw [hu,huout] at hb
  rw [cleared_output s base out bits _ h0] at hb
  have hh := Exec.seq ha hb
  convert hh using 1 <;> omega

def emitExpr {n : ℕ} (base out : ℕ) (e : BitExpr n) : Block ℕ :=
  .seq (StackIndices.compile base e) (.atom (encodeAtom base (base+1) (base+2) out))
noncomputable def emitExprTime {n : ℕ} (e : BitExpr n) : Polynomial ℕ :=
  StackIndices.timePolynomial e+7*e.widthPoly+7

lemma emitExpr_exec {n : ℕ} (base out : ℕ) (e : BitExpr n) (s : Store ℕ) (w : ℕ)
    (hb : n≤base) (ho : out<base) (hf : Fresh s base (StackIndices.slots e))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(emitExprTime e).eval w,
      Exec (emitExpr base out e) s
        (Function.update s out (Encoding.encodePayload (e.run (inputView n s)).1++s out)) t := by
  have hslots := StackIndices.slots_lower e
  have h0 : s base=[] := hf base (by omega) (by omega)
  have h1 : s (base+1)=[] := hf (base+1) (by omega) (by omega)
  have h2 : s (base+2)=[] := hf (base+2) (by omega) (by omega)
  obtain ⟨ta,hta,ha⟩ := StackIndices.compile_exec e base s w hb hf hw
  let bits := (e.run (inputView n s)).1
  let u := Function.update s base bits
  have hu : u base=bits := by simp [u]
  have huout : u out=s out := by simp [u,Function.update,show out≠base by omega]
  have hu1 : u (base+1)=[] := by simp [u,Function.update,h1]
  have hu2 : u (base+2)=[] := by simp [u,Function.update,h2]
  have he := encodeAtom_exec base (base+1) (base+2) out (encodeMap_injective ho) u hu1 hu2
  rw [hu,huout,cleared_output s base out bits _ h0] at he
  have hx := e.run_width (inputView n s) hw
  refine ⟨ta+(7*bits.length+6)+1,?_,Exec.seq ha he⟩
  simp only [emitExprTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change bits.length≤_ at hx
  omega

def emitLiteral {n : ℕ} (base out : ℕ) (e : BitExpr n) (sign : Bool) : Block ℕ :=
  .seq (emitExpr base out e) (emitConst base out [sign])
noncomputable def emitLiteralTime {n : ℕ} (e : BitExpr n) : Polynomial ℕ := emitExprTime e+18

lemma emitLiteral_exec {n : ℕ} (base out : ℕ) (e : BitExpr n) (sign : Bool) (s : Store ℕ) (w : ℕ)
    (hb : n≤base) (ho : out<base) (hf : Fresh s base (StackIndices.slots e))
    (hw : ∀ i : Fin n,(s i.val).length≤w) :
    ∃ t≤(emitLiteralTime e).eval w,
      Exec (emitLiteral base out e sign) s
        (Function.update s out (Encoding.encodePayload [sign]++Encoding.encodePayload (e.run (inputView n s)).1++s out)) t := by
  obtain ⟨ta,hta,ha⟩ := emitExpr_exec base out e s w hb ho hf hw
  let bits := (e.run (inputView n s)).1
  let u := Function.update s out (Encoding.encodePayload bits++s out)
  have hu : Fresh u base 3 :=
    (hf.subrange (by omega) (by have := StackIndices.slots_lower e;omega)).update_outside (Or.inl ho) _
  have he := emitConst_exec base out [sign] u ho hu
  have hout : Function.update u out (Encoding.encodePayload [sign]++u out)=
      Function.update s out (Encoding.encodePayload [sign]++Encoding.encodePayload bits++s out) := by
    simp [u,List.append_assoc]
  rw [hout] at he
  refine ⟨ta+17+1,?_,?_⟩
  · simp only [emitLiteralTime,Polynomial.eval_add,Polynomial.eval_ofNat];omega
  · simpa using Exec.seq ha he

end BalancedAssortments.CookLevin.StackEmit
