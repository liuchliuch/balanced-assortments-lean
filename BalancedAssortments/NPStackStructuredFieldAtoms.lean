import BalancedAssortments.NPStackStructuredAtoms

noncomputable section
namespace BalancedAssortments.NPStack.Structured
open NPStack
variable {K : Type*} [DecidableEq K]

def encodeMacro (input reversed count out : K) : Bool → Macros.Macro K Bool
  | false => .encode input reversed count out true
  | true => .halt true

def encodeAtom (input reversed count out : K) : Atom K :=
  let P := Macros.compile (encodeMacro input reversed count out) false input out
  atomOfProgram P (.main true) rfl (Macros.compile_noChoice _ _ _ _)

lemma encodeAtom_exec (input reversed count out : K)
    (hi : Function.Injective (Macros.encodeMap input reversed count out))
    (s : Store K) (hr : s reversed=[]) (hc : s count=[]) :
    Exec (.atom (encodeAtom input reversed count out)) s
      (Macros.writes s [(input,[]),(out,FPTASCostProgram.serializeBits (s input)++s out)])
      (7*(s input).length+6) := by
  let P := Macros.compile (encodeMacro input reversed count out) false input out
  have hh := Macros.encode_call (encodeMacro input reversed count out) false input out
    (q := false) (next := true) rfl hi s hr hc
  exact Exec.of_program_run P (.main true) rfl (Macros.compile_noChoice _ _ _ _) hh input out

end BalancedAssortments.NPStack.Structured
