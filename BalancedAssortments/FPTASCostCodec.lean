import BalancedAssortments.FPTASCostCompleteGuarantee
import BalancedAssortments.NPCNFEmission
import BalancedAssortments.ComplexityTimeSourceParsing

/-! Flat self-delimiting input/output interface for the raw binary policy
program. Framing preserves unreduced fractions and zero-padded binary words. -/
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
namespace BalancedAssortments.FPTASCostCodec
open KnapsackCostRational FPTASCostSeeds FPTASCostOutput

structure Input where
  alpha : Fraction
  epsilon : Fraction
  rank : List Bool
  products : List Product

def productFields : List Product → List (List Bool)
  | [] => []
  | (r,v)::ps => r.numerator::r.denominator::v.numerator::v.denominator::productFields ps

def fields (x : Input) : List (List Bool) :=
  x.alpha.numerator::x.alpha.denominator::x.epsilon.numerator::x.epsilon.denominator::x.rank::productFields x.products

lemma productFields_length (ps : List Product) : (productFields ps).length = 4*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨r,v⟩; simp [productFields,ih]; omega

lemma productFields_volume (ps : List Product) :
    NPCNF.Encoding.fieldVolume (productFields ps) =
      (ps.map (fun p => FPTASCostProgram.fractionSize p.1+FPTASCostProgram.fractionSize p.2)).sum+4*ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨r,v⟩
    simp only [productFields,NPCNF.Encoding.fieldVolume,List.map_cons,List.sum_cons,List.length_cons] at *
    dsimp only [FPTASCostProgram.fractionSize] at *
    omega

def parseProducts : List (List Bool) → Option (List Product) × ℕ
  | [] => (some [],1)
  | rn::rd::vn::vd::xs =>
    let tail := parseProducts xs
    (tail.1.map (fun ps => ((⟨rn,rd⟩ : Fraction),(⟨vn,vd⟩ : Fraction))::ps),tail.2+12)
  | _ => (none,5)

def pack : List (List Bool) → Option Input × ℕ
  | an::ad::en::ed::ks::xs =>
    let ps := parseProducts xs
    (ps.1.map (fun products => ⟨⟨an,ad⟩,⟨en,ed⟩,ks,products⟩),ps.2+12)
  | _ => (none,6)

def encode (x : Input) : List Bool := NPCNF.Encoding.encodeFields (fields x)

lemma fields_volume (x : Input) : NPCNF.Encoding.fieldVolume (fields x) =
    FPTASCostProgram.fractionSize x.alpha+FPTASCostProgram.fractionSize x.epsilon+x.rank.length+5+
    (x.products.map (fun p => FPTASCostProgram.fractionSize p.1+FPTASCostProgram.fractionSize p.2)).sum+4*x.products.length := by
  have hh := productFields_volume x.products
  simp only [fields,NPCNF.Encoding.fieldVolume,List.map_cons,List.sum_cons] at *
  dsimp only [FPTASCostProgram.fractionSize] at *
  omega

lemma fields_length (x : Input) : (fields x).length = 5+4*x.products.length := by
  simp [fields,productFields_length]; omega

lemma volume_le_encoding (fs : List (List Bool)) :
    NPCNF.Encoding.fieldVolume fs ≤ (NPCNF.Encoding.encodeFields fs).length := by
  rw [NPCNF.Encoding.encodeFields_length]
  unfold NPCNF.Encoding.fieldVolume
  induction fs <;> simp_all <;> omega

lemma inputSize_le_encode (x : Input) :
    FPTASCostProgram.inputSize x.alpha x.epsilon (⟨x.rank,[true]⟩ : Fraction) x.products ≤ (encode x).length := by
  have hh := volume_le_encoding (fields x)
  rw [fields_volume] at hh
  dsimp only [encode,FPTASCostProgram.inputSize,FPTASCostProgram.fractionSize]
  simp only [List.length_cons,List.length_nil] at *
  dsimp only [FPTASCostProgram.fractionSize] at hh
  omega

def parse (bs : List Bool) : Option Input × ℕ :=
  let raw := EncodingTime.parse bs
  match raw.1 with
  | none => (none,raw.2+4)
  | some fs => let out := pack fs; (out.1,raw.2+out.2+4)

lemma parseProducts_fields (ps : List Product) : (parseProducts (productFields ps)).1 = some ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨⟨rn,rd⟩,⟨vn,vd⟩⟩; simp [productFields,parseProducts,ih]

lemma pack_fields (x : Input) : (pack (fields x)).1 = some x := by
  cases x with
  | mk a e k ps => cases a; cases e; simp [fields,pack,parseProducts_fields]

@[simp] theorem parse_encode (x : Input) : (parse (encode x)).1 = some x := by
  simp [parse,encode,NPCNF.Encoding.parseFields_encode,pack_fields]

lemma parseProducts_cost (fs : List (List Bool)) : (parseProducts fs).2 ≤ 12*fs.length+5 := by
  fun_induction parseProducts fs
  · simp
  · rename_i a b c d xs tail ih
    subst tail
    simp only [List.length_cons]
    omega
  · omega

lemma pack_cost (fs : List (List Bool)) : (pack fs).2 ≤ 12*fs.length+17 := by
  unfold pack
  split
  · rename_i a b c d k xs
    have hh := parseProducts_cost xs
    simp only [List.length_cons]
    omega
  · omega

theorem parse_cost (bits : List Bool) : (parse bits).2 ≤ 100*(bits.length+1)^2 := by
  have hp := EncodingTime.parse_cost bits
  have hsq : 0 < (bits.length+1)^2 := by positivity
  unfold parse
  cases he : (EncodingTime.parse bits).1 with
  | none => simp only [he]; nlinarith
  | some fs =>
    have hv := ComplexityTimeSourceParsing.parse_volume bits fs he
    have hl := ComplexityTimeSourceParsing.field_count_le_volume fs
    have hc := pack_cost fs
    simp only [he]
    nlinarith

/-- Three framed fields per policy atom: numerator, denominator, incidence mask. -/
def policyFields : List PolicyAtom → List (List Bool) × ℕ
  | [] => ([],1)
  | (p,mask)::ps =>
    let tail := policyFields ps
    (p.numerator::p.denominator::mask::tail.1,tail.2+8)

def emitPolicy (ps : List PolicyAtom) : List Bool × ℕ :=
  let fs := policyFields ps
  let out := NPCNF.Encoding.emitFields fs.1
  (out.1,fs.2+out.2+4)

def parsePolicy : List (List Bool) → Option (List PolicyAtom)
  | [] => some []
  | pn::pd::mask::xs => (parsePolicy xs).map (fun ps => ((⟨pn,pd⟩ : Fraction),mask)::ps)
  | _ => none

lemma policy_roundtrip (ps : List PolicyAtom) : parsePolicy (policyFields ps).1 = some ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨⟨pn,pd⟩,mask⟩; simp [policyFields,parsePolicy,ih]

theorem emitPolicy_roundtrip (ps : List PolicyAtom) :
    (EncodingTime.parse (emitPolicy ps).1).1.bind parsePolicy = some ps := by
  simp [emitPolicy,NPCNF.Encoding.emitFields_eq,NPCNF.Encoding.parseFields_encode,policy_roundtrip]

lemma policyFields_cost (ps : List PolicyAtom) : (policyFields ps).2 = 8*ps.length+1 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => rcases p with ⟨p,m⟩; simp only [policyFields,List.length_cons,ih]; omega

lemma policyFields_volume (ps : List PolicyAtom) {w n : ℕ}
    (hw : ∀ p ∈ ps,p.1.Width w ∧ p.2.length ≤ n) :
    NPCNF.Encoding.fieldVolume (policyFields ps).1 ≤ ps.length*(2*w+n+3) := by
  induction ps with
  | nil => simp [policyFields,NPCNF.Encoding.fieldVolume]
  | cons p ps ih =>
    rcases p with ⟨p,m⟩
    have hh := hw (p,m) (by simp)
    have ht := ih (fun q hq => hw q (by simp [hq]))
    simp only [policyFields,NPCNF.Encoding.fieldVolume,List.map_cons,List.sum_cons,List.length_cons] at *
    dsimp only [Fraction.Width] at hh
    nlinarith

theorem emitPolicy_cost (ps : List PolicyAtom) {w n : ℕ}
    (hw : ∀ p ∈ ps,p.1.Width w ∧ p.2.length ≤ n) :
    (emitPolicy ps).2 ≤ 8*ps.length+12*(ps.length*(2*w+n+3))+6 := by
  have hv := policyFields_volume ps hw
  have hc := NPCNF.Encoding.emitFields_cost (policyFields ps).1
  simp only [emitPolicy,policyFields_cost]
  omega

theorem emitPolicy_length (ps : List PolicyAtom) {w n : ℕ}
    (hw : ∀ p ∈ ps,p.1.Width w ∧ p.2.length ≤ n) :
    (emitPolicy ps).1.length ≤ 2*(ps.length*(2*w+n+3)) := by
  have hv := policyFields_volume ps hw
  have hc := NPCNF.Encoding.encoded_length_le_volume (policyFields ps).1
  simp only [emitPolicy,NPCNF.Encoding.emitFields_eq]
  omega

/-- Flat input to flat output, with explicit parser and emitter costs. Invalid
framing returns none. Mathematical validity remains the theorem's precondition. -/
def run (bs : List Bool) : Option (List Bool) × ℕ :=
  let input := parse bs
  match input.1 with
  | none => (none,input.2+4)
  | some x =>
    let policy := FPTASCostComplete.runPolicyBits x.alpha x.epsilon x.rank x.products
    let output := emitPolicy policy.1
    (some output.1,input.2+policy.2+output.2+8)

theorem run_encode (x : Input) :
    (run (encode x)).1 = some (emitPolicy
      (FPTASCostComplete.runPolicyBits x.alpha x.epsilon x.rank x.products).1).1 := by
  simp [run,parse_encode]

theorem run_roundtrip (x : Input) :
    ((run (encode x)).1.bind (fun bs => (EncodingTime.parse bs).1.bind parsePolicy)) =
      some (FPTASCostComplete.runPolicyBits x.alpha x.epsilon x.rank x.products).1 := by
  rw [run_encode]
  exact emitPolicy_roundtrip _

end BalancedAssortments.FPTASCostCodec
