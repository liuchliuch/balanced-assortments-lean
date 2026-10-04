import BalancedAssortments.CookLevinStackClockProgram
import BalancedAssortments.NPStackStructuredFieldAtoms
import BalancedAssortments.NPCNFEncoding

/-! Genuine finite-stack front end carrying both the original input and its
polynomial clock to a separately compiled bounded-tableau constructor. -/
noncomputable section
namespace BalancedAssortments.CookLevin.StackClock
open NPStack NPStack.Structured NPCNF

def seedOutput (e : FuelExpr) : ℕ := slots e+1
def seedBlock (e : FuelExpr) : Block ℕ :=
  .seq (compile 1 e)
    (.seq (.atom (encodeAtom 1 2 3 (seedOutput e))) (.atom (encodeAtom 0 2 3 (seedOutput e))))
def seedBits (e : FuelExpr) (word : List Bool) : List Bool :=
  Encoding.encodeFields [word,clockBits e word]
noncomputable def seedTime (e : FuelExpr) : Polynomial ℕ :=
  timePolynomial e+7*e.polynomial+7*Polynomial.X+14

def seedProgram (e : FuelExpr) : FiniteProgram := finiteBlock (seedBlock e) 0 (seedOutput e)
lemma seedProgram_noChoice (e : FuelExpr) : NoChoice (seedProgram e).program :=
  restrictProgram_noChoice (program (seedBlock e) 0 (seedOutput e)) _
    (finiteRegisterBound_code _) (finiteRegisterBound_input _) (finiteRegisterBound_output _) (program_noChoice _ _ _)

lemma seedProgram_outputs (e : FuelExpr) (word : List Bool) :
    OutputsIn (seedProgram e).program word (seedBits e word) ((seedTime e).eval word.length) := by
  let out := seedOutput e
  let s : Store ℕ := Function.update (fun _ => []) 0 word
  let fuel := clockBits e word
  let u := Function.update s 1 fuel
  have hout : 3<out := by have := slots_lower e;dsimp [out,seedOutput];omega
  have hsw : s 0=word := by simp [s]
  have hsFresh : Fresh s 1 (slots e) := by
    intro k hk hk';simp [s,Function.update,show k≠0 by omega]
  have hr := compile_exec e 1 s (by decide) hsFresh
  rw [hsw] at hr
  have hu1 : u 1=fuel := by simp [u]
  have hu0 : u 0=word := by simp [u,s]
  have hu2 : u 2=[] := by simp [u,s]
  have hu3 : u 3=[] := by simp [u,s]
  have huo : u out=[] := by simp [u,s,Function.update,show out≠1 by omega,show out≠0 by omega]
  have hi1 : Function.Injective (Macros.encodeMap 1 2 3 out) := by
    intro i j he
    cases i <;> cases j <;> simp only [Macros.encodeMap] at he <;> first | rfl | omega
  have h1 := encodeAtom_exec 1 2 3 out hi1 u hu2 hu3
  rw [hu1,huo,List.append_nil] at h1
  let v := Macros.writes u [(1,[]),(out,FPTASCostProgram.serializeBits fuel)]
  have hv0 : v 0=word := by simp [v,Macros.writes,u,s,Function.update,show 0≠out by omega]
  have hv2 : v 2=[] := by simp [v,Macros.writes,u,s,Function.update,show 2≠out by omega]
  have hv3 : v 3=[] := by simp [v,Macros.writes,u,s,Function.update,show 3≠out by omega]
  have hvo : v out=FPTASCostProgram.serializeBits fuel := by simp [v,Macros.writes]
  have hi0 : Function.Injective (Macros.encodeMap 0 2 3 out) := by
    intro i j he
    cases i <;> cases j <;> simp only [Macros.encodeMap] at he <;> first | rfl | omega
  have h0 := encodeAtom_exec 0 2 3 out hi0 v hv2 hv3
  rw [hv0,hvo] at h0
  let last := Macros.writes v [(0,[]),(out,FPTASCostProgram.serializeBits word++FPTASCostProgram.serializeBits fuel)]
  have hlast : last out=seedBits e word := by
    simp [last,Macros.writes,seedBits,Encoding.encodeFields,Encoding.encodePayload,FPTASCostProgram.serializeBits,fuel]
  have hh := Exec.seq hr (Exec.seq h1 h0)
  have hcost : (timePolynomial e).eval word.length+((7*fuel.length+6)+(7*word.length+6)+1)+1≤(seedTime e).eval word.length := by
    simp [seedTime,fuel,clockBits]
    omega
  let P := program (seedBlock e) 0 out
  have he : OutputsIn P word (seedBits e word) ((seedTime e).eval word.length) := by
    refine ⟨_,hcost,⟨finish (seedBlock e),last⟩,?_,?_,?_⟩
    · exact hh.compiles 0 out
    · exact code_finish _
    · exact hlast
  exact finitelyNamed_outputs P he

/-- An actual finite deterministic polynomial-time transducer, ready for
PolynomialProgram.comp with a bounded-tableau constructor. -/
def seedPolynomialProgram (e : FuelExpr) : PolynomialProgram (seedBits e) where
  code := seedProgram e
  noChoice := seedProgram_noChoice e
  clock := seedTime e
  computes := seedProgram_outputs e

end BalancedAssortments.CookLevin.StackClock
