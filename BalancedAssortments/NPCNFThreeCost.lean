import BalancedAssortments.NPCNFValidationCost

namespace BalancedAssortments.NPCNF.Encoding

lemma rawLabels_length (F : BitFormula) : (rawLabels F).length = bitLiteralCount F := by
  simp [rawLabels,bitLiteralCount,List.length_flatten,Function.comp_def]

lemma bitFormula_size (next : List Bool) (F : BitFormula) :
    (bitFormula next F).1.1.length ≤ 3*bitLiteralCount F+F.length ∧
      bitLiteralCount (bitFormula next F).1.1 ≤ 7*bitLiteralCount F+F.length := by
  have hh := toThree_size (ComplexityTimeBinary.value next) (F.map (List.map BitLiteral.decode))
  have he := congrArg Prod.fst (bitFormula_decode next F)
  have hel : (bitFormula next F).1.1.length = (toThree (ComplexityTimeBinary.value next) (F.map (List.map BitLiteral.decode))).1.length := by
    simpa only [List.length_map] using congrArg List.length he
  have hem : bitLiteralCount (bitFormula next F).1.1 = literalCount (toThree (ComplexityTimeBinary.value next) (F.map (List.map BitLiteral.decode))).1 := by
    simpa only [decode_literalCount] using congrArg literalCount he
  simpa only [← hel,← hem,decode_literalCount,List.length_map] using And.intro hh.1 hh.2.1

lemma rawLabels_width {F : BitFormula} {b : ℕ} (h : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ b) :
    ∀ x ∈ rawLabels F,x.length ≤ b := by
  intro x hx
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hx
  obtain ⟨c,hc,hl⟩ := List.mem_flatten.mp hl
  exact h c hc l hl

lemma catalogueBits_measure {F : BitFormula} {b : ℕ} (h : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ b) :
    rawMeasure (catalogueBits F).1 ≤ (b+3)*(2*bitLiteralCount F)+3*F.length+4 := by
  have hlabels := rawLabels_width h
  have hcat : ∀ x ∈ (catalogueBits F).1.catalog,x.length ≤ b := by
    intro x hx
    exact hlabels x (dedupLabels_member hx)
  have hm := rawMeasure_bound hcat h
  have hl := dedupLabels_length (rawLabels F)
  rw [rawLabels_length] at hl
  have hmul := Nat.mul_le_mul_left (b+3) hl
  change rawMeasure (catalogueBits F).1 ≤
    (b+3)*((dedupLabels (rawLabels F)).1.length+bitLiteralCount F)+3*F.length+4 at hm
  nlinarith

lemma catalogueBits_cost {F : BitFormula} {b : ℕ} (h : ∀ c ∈ F,∀ l ∈ c,l.labelBits.length ≤ b) :
    (catalogueBits F).2 ≤ 32*(bitLiteralCount F+1)^2*(b+1)+2*bitLiteralCount F+F.length+4 := by
  have hd := dedupLabels_cost (rawLabels_width h)
  rw [rawLabels_length] at hd
  change _ ≤ _ at hd
  simp only [catalogueBits]
  have hflat : F.flatten.length = bitLiteralCount F := by simp [bitLiteralCount,List.length_flatten]
  rw [hflat]
  omega

/-- Polynomial construction size despite arbitrary sparse binary variable labels. -/
theorem reduceRaw_measure (input : Raw) :
    rawMeasure (reduceRaw input).1 ≤ 256*(rawMeasure input+1)^2 := by
  let L := rawMeasure input
  let start := (freshBits input.catalog).1
  let result := (bitFormula start input.formula).1.1
  have hw := rawMeasure_widths input
  have hn := rawMeasure_counts input
  have hs : start.length ≤ L+2 := freshBits_width hw.1
  have hf : ∀ c ∈ input.formula,∀ l ∈ c,l.labelBits.length ≤ L+2 :=
    fun c hc l hl => (hw.2 c hc l hl).trans (by omega)
  have ho := bitFormula_width hs hf
  have hos : ∀ c ∈ result,∀ l ∈ c,l.labelBits.length ≤ 3*L+2 := by
    intro c hc l hl
    exact (ho c hc l hl).trans (by have hh := hn.2.2; omega)
  have hsize := bitFormula_size start input.formula
  have hM : bitLiteralCount result ≤ 8*L := by nlinarith [hn.2.1,hn.2.2]
  have hC : result.length ≤ 4*L := by nlinarith [hn.2.1,hn.2.2]
  have hm := catalogueBits_measure hos
  have hp := Nat.mul_le_mul_left (3*L+2+3) (Nat.mul_le_mul_left 2 hM)
  change rawMeasure (catalogueBits result).1 ≤ 256*(L+1)^2
  nlinarith

/-- Charged raw bit-program cost: fresh-label max scan/increments, gate/list
construction and semantic output-catalog deduplication are all included. -/
theorem reduceRaw_cost (input : Raw) :
    (reduceRaw input).2 ≤ 32768*(rawMeasure input+1)^3 := by
  let L := rawMeasure input
  let start := freshBits input.catalog
  let result := bitFormula start.1 input.formula
  have hw := rawMeasure_widths input
  have hn := rawMeasure_counts input
  have hs := freshBits_cost hw.1
  have hswidth : start.1.length ≤ L+2 := freshBits_width hw.1
  have hf := bitFormula_cost start.1 input.formula
  have hformulaInputs : ∀ c ∈ input.formula,∀ l ∈ c,l.labelBits.length ≤ L+2 :=
    fun c hc l hl => (hw.2 c hc l hl).trans (by omega)
  have ho := bitFormula_width hswidth hformulaInputs
  have howidth : ∀ c ∈ result.1.1,∀ l ∈ c,l.labelBits.length ≤ 3*L+2 := by
    intro c hc l hl
    exact (ho c hc l hl).trans (by have hh := hn.2.2; omega)
  have hout := bitFormula_size start.1 input.formula
  have hM : bitLiteralCount result.1.1 ≤ 8*L := by nlinarith [hn.2.1,hn.2.2]
  have hC : result.1.1.length ≤ 4*L := by nlinarith [hn.2.1,hn.2.2]
  have hc := catalogueBits_cost howidth
  have hstart : start.2 ≤ 20*(L+1)^2+5 := by
    have hp := Nat.mul_le_mul_right (20*(L+1)) (Nat.add_le_add_right hn.1 1)
    change start.2 ≤ (input.catalog.length+1)*(20*(L+1))+5 at hs
    nlinarith
  have hformula : result.2 ≤ 2048*(L+1)^2 := by
    have h1 : input.formula.length+bitLiteralCount input.formula+1 ≤ 2*(L+1) := by omega
    have h2 : start.1.length+2*bitLiteralCount input.formula+2 ≤ 4*(L+1) := by omega
    have hp := Nat.mul_le_mul h1 h2
    nlinarith
  have hcatSq := Nat.pow_le_pow_left (Nat.add_le_add_right hM 1) 2
  have hcatProd := Nat.mul_le_mul_right (3*L+2+1) (Nat.mul_le_mul_left 32 hcatSq)
  have hcat : (catalogueBits result.1.1).2 ≤ 8192*(L+1)^3 := by nlinarith
  change start.2+result.2+(catalogueBits result.1.1).2+8 ≤ 32768*(L+1)^3
  nlinarith

end BalancedAssortments.NPCNF.Encoding
