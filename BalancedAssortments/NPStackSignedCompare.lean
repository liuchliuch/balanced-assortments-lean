import BalancedAssortments.NPStackAdd
import BalancedAssortments.NPStackCompareNormalizeSound
import BalancedAssortments.NPStackEmbedding
import BalancedAssortments.ComplexityTimeVerifier

namespace BalancedAssortments.NPStack
open ComplexityTimeBinary ComplexityTimeVerifier

inductive SignedCompareStack | ap | an | bp | bn | leftSum | rightSum | scratch | output
  deriving DecidableEq, Fintype
inductive SignedCompareState | addLeft (q : AddState) | addRight (q : AddState) | compare (q : CompareState)
  deriving DecidableEq, Fintype

def signedLeftMap : AddStack→SignedCompareStack
  | .left => .ap | .right => .bn | .scratch => .scratch | .output => .leftSum

def signedRightMap : AddStack→SignedCompareStack
  | .left => .bp | .right => .an | .scratch => .scratch | .output => .rightSum

def signedCompareMap : CompareStack→SignedCompareStack
  | .left => .leftSum | .right => .rightSum | .result => .output

def signedCompareProgram : Program SignedCompareStack SignedCompareState where
  code
    | .addLeft .done => .jump (.addRight (.readX false))
    | .addLeft q => (addProgram.code q).rename signedLeftMap SignedCompareState.addLeft
    | .addRight .done => .jump (.compare (.readLeft .eq))
    | .addRight q => (addProgram.code q).rename signedRightMap SignedCompareState.addRight
    | .compare q => (compareProgram.code q).rename signedCompareMap SignedCompareState.compare
  start := .addLeft (.readX false)
  inputStack := .ap
  outputStack := .output

def signedStacks (ap an bp bn ls rs sc out : List Bool) : SignedCompareStack→List Bool
  | .ap => ap | .an => an | .bp => bp | .bn => bn
  | .leftSum => ls | .rightSum => rs | .scratch => sc | .output => out

def signedConfig (q : SignedCompareState) (ap an bp bn ls rs sc out : List Bool) :
    Config SignedCompareStack SignedCompareState := ⟨q,signedStacks ap an bp bn ls rs sc out⟩

private theorem left_injective : Function.Injective signedLeftMap := by
  intro a b h;cases a <;> cases b <;> simp_all [signedLeftMap]
private theorem right_injective : Function.Injective signedRightMap := by
  intro a b h;cases a <;> cases b <;> simp_all [signedRightMap]
private theorem compare_injective : Function.Injective signedCompareMap := by
  intro a b h;cases a <;> cases b <;> simp_all [signedCompareMap]

private theorem left_extends : CodeExtends addProgram signedCompareProgram signedLeftMap SignedCompareState.addLeft := by
  intro q h;cases q <;> simp_all [signedCompareProgram,addProgram]
private theorem right_extends : CodeExtends addProgram signedCompareProgram signedRightMap SignedCompareState.addRight := by
  intro q h;cases q <;> simp_all [signedCompareProgram,addProgram]
private theorem compare_extends : CodeExtends compareProgram signedCompareProgram signedCompareMap SignedCompareState.compare := by
  intro q h;rfl

lemma signed_add_left (ap an bp bn out : List Bool) :
    Run signedCompareProgram (5*max ap.length bn.length+6)
      (signedConfig (.addLeft (.readX false)) ap an bp bn [] [] [] out)
      (signedConfig (.addLeft .done) [] an bp [] (addCarry ap bn false).1 [] [] out) := by
  apply (add_run ap bn false).relocate_exact signedLeftMap SignedCompareState.addLeft left_injective left_extends
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · intro k hk
    have h1 := hk .left; have h2 := hk .right; have h3 := hk .scratch; have h4 := hk .output
    cases k <;> simp_all [signedLeftMap,signedConfig,signedStacks]

lemma signed_add_right (an bp ls out : List Bool) :
    Run signedCompareProgram (5*max bp.length an.length+6)
      (signedConfig (.addRight (.readX false)) [] an bp [] ls [] [] out)
      (signedConfig (.addRight .done) [] [] [] [] ls (addCarry bp an false).1 [] out) := by
  apply (add_run bp an false).relocate_exact signedRightMap SignedCompareState.addRight right_injective right_extends
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · intro k hk
    have h1 := hk .left; have h2 := hk .right; have h3 := hk .scratch; have h4 := hk .output
    cases k <;> simp_all [signedRightMap,signedConfig,signedStacks]

lemma signed_compare (ls rs out : List Bool) :
    Run signedCompareProgram (2*max ls.length rs.length+3)
      (signedConfig (.compare (.readLeft .eq)) [] [] [] [] ls rs [] out)
      (signedConfig (.compare .done) [] [] [] [] [] [] [] (leBits ls rs::out)) := by
  apply (compare_leBits_run ls rs out).relocate_exact signedCompareMap SignedCompareState.compare compare_injective compare_extends
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · constructor
    · rfl
    · intro k;cases k <;> rfl
  · intro k hk
    have h1 := hk .left; have h2 := hk .right; have h3 := hk .result
    cases k <;> simp_all [signedCompareMap,signedConfig,signedStacks]

def signedCompareTime (x y : ZBits) : ℕ :=
  (5*max x.1.length y.2.length+6)+1+(5*max y.1.length x.2.length+6)+1+
    (2*max (addCarry x.1 y.2 false).1.length (addCarry y.1 x.2 false).1.length+3)

/-- Concrete finite-control composition of two ripple adders and the binary
comparator. The result exactly matches the signed bit-list comparator. -/
theorem signedCompare_run (x y : ZBits) (out : List Bool) :
    Run signedCompareProgram (signedCompareTime x y)
      (signedConfig (.addLeft (.readX false)) x.1 x.2 y.1 y.2 [] [] [] out)
      (signedConfig (.compare .done) [] [] [] [] [] [] [] ((zle x y).1::out)) := by
  have h1 := signed_add_left x.1 x.2 y.1 y.2 out
  have h2 := signed_add_right x.2 y.1 (addCarry x.1 y.2 false).1 out
  have h3 := signed_compare (addCarry x.1 y.2 false).1 (addCarry y.1 x.2 false).1 out
  have j1 : Step signedCompareProgram
      (signedConfig (.addLeft .done) [] x.2 y.1 [] (addCarry x.1 y.2 false).1 [] [] out)
      (signedConfig (.addRight (.readX false)) [] x.2 y.1 [] (addCarry x.1 y.2 false).1 [] [] out) := by
    simp [Step,successors,signedCompareProgram,signedConfig]
  have j2 : Step signedCompareProgram
      (signedConfig (.addRight .done) [] [] [] [] (addCarry x.1 y.2 false).1 (addCarry y.1 x.2 false).1 [] out)
      (signedConfig (.compare (.readLeft .eq)) [] [] [] [] (addCarry x.1 y.2 false).1 (addCarry y.1 x.2 false).1 [] out) := by
    simp [Step,successors,signedCompareProgram,signedConfig]
  exact (((h1.trans (Run.one j1)).trans h2).trans (Run.one j2)).trans h3

theorem signedCompareTime_bound (x y : ZBits) :
    signedCompareTime x y≤12*max (width x) (width y)+19 := by
  simp only [signedCompareTime,addCarry_length,width]
  omega

def finiteSignedCompare : FiniteProgram where
  K := SignedCompareStack
  Q := SignedCompareState
  program := signedCompareProgram

end BalancedAssortments.NPStack
