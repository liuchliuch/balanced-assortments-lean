import BalancedAssortments.NPCNFThreeCatalogued
import BalancedAssortments.NPCNFValidation

namespace BalancedAssortments.NPCNF.Encoding
open ComplexityTimeBinary

def BitLiteral.neg (l : BitLiteral) : BitLiteral := ⟨l.labelBits,!l.positive⟩
def bitPositive (v : List Bool) : BitLiteral := ⟨v,true⟩
def bitNegative (v : List Bool) : BitLiteral := ⟨v,false⟩

@[simp] lemma decode_neg (l : BitLiteral) : l.neg.decode = l.decode.neg := rfl
@[simp] lemma decode_bitPositive (v : List Bool) : (bitPositive v).decode = positive (value v) := rfl
@[simp] lemma decode_bitNegative (v : List Bool) : (bitNegative v).decode = negative (value v) := rfl

def bitGate (a b : BitLiteral) (z : List Bool) : BitFormula :=
  [[a.neg,bitPositive z],[b.neg,bitPositive z],[a,b,bitNegative z]]

lemma bitGate_decode (a b : BitLiteral) (z : List Bool) :
    (bitGate a b z).map (List.map BitLiteral.decode) = orGate a.decode b.decode (value z) := rfl

/-- Actual fresh-label allocation is a binary increment, never Nat.succ on a
decoded label. The counter magnitude controls no list allocation. -/
def bitChain (next : List Bool) (a : BitLiteral) : BitClause → (BitFormula × List Bool) × ℕ
  | [] => (([[a]],next),8)
  | b::bs =>
      let step := addCarry next [true] false
      let tail := bitChain step.1 (bitPositive next) bs
      ((bitGate a b next++tail.1.1,tail.1.2),step.2+tail.2+64)

def bitClause (next : List Bool) : BitClause → (BitFormula × List Bool) × ℕ
  | [] => (([[]],next),8)
  | a::as => bitChain next a as

def bitFormula (next : List Bool) : BitFormula → (BitFormula × List Bool) × ℕ
  | [] => (([],next),4)
  | c::cs =>
      let head := bitClause next c
      let tail := bitFormula head.1.2 cs
      ((head.1.1++tail.1.1,tail.1.2),head.2+tail.2+head.1.1.length+8)

lemma bitChain_decode (next : List Bool) (a : BitLiteral) (rest : BitClause) :
    ((bitChain next a rest).1.1.map (List.map BitLiteral.decode),value (bitChain next a rest).1.2) =
      chain (value next) a.decode (rest.map BitLiteral.decode) := by
  induction rest generalizing next a with
  | nil => rfl
  | cons b bs ih =>
    have hh := ih (addCarry next [true] false).1 (bitPositive next)
    simp only [addCarry_value,value,Bool.toNat_true,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,
      decode_bitPositive] at hh
    simp only [bitChain,List.map_append,bitGate_decode,List.map_cons,chain]
    rw [Prod.mk.injEq] at hh ⊢
    exact ⟨congrArg (orGate a.decode b.decode (value next)++·) hh.1,hh.2⟩

lemma bitClause_decode (next : List Bool) (c : BitClause) :
    ((bitClause next c).1.1.map (List.map BitLiteral.decode),value (bitClause next c).1.2) =
      clauseToThree (value next) (c.map BitLiteral.decode) := by
  cases c with
  | nil => rfl
  | cons a as => exact bitChain_decode next a as

/-- Exact output-formula and counter refinement for arbitrary raw binary labels,
including padded encodings and all degenerate source clauses. -/
theorem bitFormula_decode (next : List Bool) (F : BitFormula) :
    ((bitFormula next F).1.1.map (List.map BitLiteral.decode),value (bitFormula next F).1.2) =
      toThree (value next) (F.map (List.map BitLiteral.decode)) := by
  induction F generalizing next with
  | nil => rfl
  | cons c cs ih =>
    have hh := bitClause_decode next c
    have ht := ih (bitClause next c).1.2
    rw [Prod.mk.injEq] at hh ht ⊢
    rw [hh.2] at ht
    simp only [bitFormula,List.map_append,List.map_cons,toThree]
    exact ⟨by rw [hh.1,ht.1],ht.2⟩

lemma bitChain_next_width (next : List Bool) (a : BitLiteral) (rest : BitClause) :
    (bitChain next a rest).1.2.length ≤ next.length+2*rest.length := by
  induction rest generalizing next a with
  | nil => simp [bitChain]
  | cons b bs ih =>
    have hh := ih (addCarry next [true] false).1 (bitPositive next)
    simp only [addCarry_length,List.length_cons,List.length_nil] at hh
    simp only [bitChain,List.length_cons]
    omega

lemma bitChain_clause_count (next : List Bool) (a : BitLiteral) (rest : BitClause) :
    (bitChain next a rest).1.1.length = 3*rest.length+1 := by
  have hh := congrArg (fun p : Formula × ℕ => p.1.length) (bitChain_decode next a rest)
  simpa only [List.length_map,chain_clause_count] using hh

lemma bitChain_cost (next : List Bool) (a : BitLiteral) (rest : BitClause) :
    (bitChain next a rest).2 ≤ 128*(rest.length+1)*(next.length+2*rest.length+2) := by
  induction rest generalizing next a with
  | nil => simp [bitChain]; omega
  | cons b bs ih =>
    have hh := ih (addCarry next [true] false).1 (bitPositive next)
    simp only [addCarry_length,List.length_cons,List.length_nil] at hh
    have hmax : max next.length 1 ≤ next.length+1 := by omega
    have hm := Nat.mul_le_mul_left (bs.length+1) hmax
    simp only [bitChain,addCarry_cost,List.length_cons,List.length_nil]
    simp only [Nat.zero_add] at hh ⊢
    nlinarith

def bitLiteralCount (F : BitFormula) : ℕ := (F.map List.length).sum

@[simp] lemma decode_literalCount (F : BitFormula) :
    literalCount (F.map (List.map BitLiteral.decode)) = bitLiteralCount F := by
  simp [literalCount,bitLiteralCount,List.map_map,Function.comp_def]

lemma bitClause_next_width (next : List Bool) (c : BitClause) :
    (bitClause next c).1.2.length ≤ next.length+2*c.length := by
  cases c with
  | nil => simp [bitClause]
  | cons a as =>
    have hh := bitChain_next_width next a as
    simp only [bitClause,List.length_cons]
    omega

lemma bitClause_clause_count (next : List Bool) (c : BitClause) :
    (bitClause next c).1.1.length ≤ 3*c.length+1 := by
  cases c with
  | nil => simp [bitClause]
  | cons a as => simp [bitClause,bitChain_clause_count]

lemma bitClause_cost (next : List Bool) (c : BitClause) :
    (bitClause next c).2 ≤ 128*(c.length+1)*(next.length+2*c.length+2) := by
  cases c with
  | nil => simp [bitClause]; omega
  | cons a as =>
    have hh := bitChain_cost next a as
    simp only [bitClause,List.length_cons]
    nlinarith

lemma bitFormula_next_width (next : List Bool) (F : BitFormula) :
    (bitFormula next F).1.2.length ≤ next.length+2*bitLiteralCount F := by
  induction F generalizing next with
  | nil => simp [bitFormula,bitLiteralCount]
  | cons c cs ih =>
    have hhead := bitClause_next_width next c
    have htail := ih (bitClause next c).1.2
    simp only [bitFormula,bitLiteralCount,List.map_cons,List.sum_cons] at *
    omega

theorem bitFormula_cost (next : List Bool) (F : BitFormula) :
    (bitFormula next F).2 ≤
      256*(F.length+bitLiteralCount F+1)*(next.length+2*bitLiteralCount F+2) := by
  induction F generalizing next with
  | nil => simp [bitFormula,bitLiteralCount]; omega
  | cons c cs ih =>
    have hh := bitClause_cost next c
    have hl := bitClause_clause_count next c
    have hn := bitClause_next_width next c
    have ht := ih (bitClause next c).1.2
    have hwidth : (bitClause next c).1.2.length+2*bitLiteralCount cs+2 ≤
        next.length+2*(c.length+bitLiteralCount cs)+2 := by omega
    have hm := Nat.mul_le_mul_left (256*(cs.length+bitLiteralCount cs+1)) hwidth
    simp only [bitFormula,List.length_cons]
    change _ ≤ 256*(cs.length+1+(c.length+bitLiteralCount cs)+1)*(next.length+2*(c.length+bitLiteralCount cs)+2)
    nlinarith

lemma bitGate_width {a b : BitLiteral} {z : List Bool} {B : ℕ}
    (ha : a.labelBits.length ≤ B) (hb : b.labelBits.length ≤ B) (hz : z.length ≤ B) :
    ∀ c ∈ bitGate a b z,∀ l ∈ c,l.labelBits.length ≤ B := by
  simp [bitGate,BitLiteral.neg,bitPositive,bitNegative]
  exact ⟨⟨ha,hz⟩,⟨hb,hz⟩,ha,hb,hz⟩

lemma bitChain_width {next : List Bool} {a : BitLiteral} {rest : BitClause} {B : ℕ}
    (hn : next.length ≤ B) (ha : a.labelBits.length ≤ B) (hr : ∀ l ∈ rest,l.labelBits.length ≤ B) :
    ∀ c ∈ (bitChain next a rest).1.1,∀ l ∈ c,l.labelBits.length ≤ B+2*rest.length := by
  induction rest generalizing next a B with
  | nil =>
    intro c hc l hl
    simp only [bitChain,List.mem_singleton] at hc
    subst c
    simp only [List.mem_singleton] at hl
    subst l
    simpa using ha
  | cons b bs ih =>
    have hb := hr b (by simp)
    have hn' : (addCarry next [true] false).1.length ≤ B+2 := by
      rw [addCarry_length]
      simp only [List.length_cons,List.length_nil]
      omega
    have ht := ih hn' (show (bitPositive next).labelBits.length ≤ B+2 by simpa using hn.trans (by omega))
      (fun l hl => (hr l (by simp [hl])).trans (by omega))
    intro c hc l hl
    simp only [bitChain,List.mem_append] at hc
    rcases hc with hc | hc
    · exact (bitGate_width ha hb hn c hc l hl).trans (by omega)
    · have hh := ht c hc l hl
      simp only [List.length_cons]
      omega

lemma bitClause_width {next : List Bool} {c : BitClause} {B : ℕ}
    (hn : next.length ≤ B) (hc : ∀ l ∈ c,l.labelBits.length ≤ B) :
    ∀ d ∈ (bitClause next c).1.1,∀ l ∈ d,l.labelBits.length ≤ B+2*c.length := by
  cases c with
  | nil => intro d hd l hl; simp [bitClause] at hd; subst d; simp at hl
  | cons a as =>
    have hh := bitChain_width (rest := as) hn (hc a (by simp)) (fun l hl => hc l (by simp [hl]))
    intro d hd l hl
    exact (hh d hd l hl).trans (by simp only [List.length_cons]; omega)

theorem bitFormula_width {next : List Bool} {F : BitFormula} {B : ℕ}
    (hn : next.length ≤ B) (hf : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ B) :
    ∀ d ∈ (bitFormula next F).1.1,∀ l ∈ d,l.labelBits.length ≤ B+2*bitLiteralCount F := by
  induction F generalizing next B with
  | nil => intro d hd; simp [bitFormula] at hd
  | cons c cs ih =>
    have hhead := bitClause_width hn (hf c (by simp))
    have hn' : (bitClause next c).1.2.length ≤ B+2*c.length :=
      (bitClause_next_width next c).trans (Nat.add_le_add_right hn _)
    have htail := ih hn' (fun c' hc' l hl => (hf c' (by simp [hc']) l hl).trans (by omega))
    intro d hd l hl
    simp only [bitFormula,List.mem_append] at hd
    rcases hd with hd | hd
    · exact (hhead d hd l hl).trans (by simp only [bitLiteralCount,List.map_cons,List.sum_cons]; omega)
    · have hh := htail d hd l hl
      simpa only [bitLiteralCount,List.map_cons,List.sum_cons,Nat.mul_add,Nat.add_assoc] using hh

end BalancedAssortments.NPCNF.Encoding
