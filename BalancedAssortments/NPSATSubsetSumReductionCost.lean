import BalancedAssortments.NPSATSubsetSumReduction

namespace BalancedAssortments.NPSATSubsetSum
open NPCNF NPCNF.Encoding ComplexityTimeBinary ComplexityTimeReduction

def rawReductionBudget (L : ℕ) : ℕ :=
  128*(L+1)^3+8*L+constructBudget L+(9*integerWidth L+6)*(4*L+1)+40

def reductionBudget (L : ℕ) : ℕ := 64*(L+1)^2+rawReductionBudget L+16

def outputBudget (L : ℕ) : ℕ := (2*integerWidth L+1)*(4*L+1)+20

lemma rawReductionBudget_mono {L M : ℕ} (h : L≤M) : rawReductionBudget L≤rawReductionBudget M := by
  unfold rawReductionBudget
  gcongr
  · exact constructBudget_mono h
  · exact integerWidth_mono h

lemma reduceRaw_cost (raw : Raw) : (reduceRaw raw).2≤rawReductionBudget (rawMeasure raw) := by
  have hv := validate_cost raw
  have ht := checkThree_cost raw.formula
  have hn := (rawMeasure_counts raw).2.1
  have hc := construct_cost raw
  have hw := construct_target_width raw
  have hi := construct_items_width raw
  have hlen := construct_items_length raw
  have he := serializeFields_cost_uniform ((construct raw).1.1::(construct raw).1.2)
    (integerWidth (rawMeasure raw)) (by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hw hi)
  simp only [List.length_cons] at he
  have hmul := Nat.mul_le_mul_left (9*integerWidth (rawMeasure raw)+6) (Nat.add_le_add_right hlen 1)
  unfold reduceRaw
  dsimp only
  split_ifs <;> dsimp only <;> unfold rawReductionBudget <;> omega

lemma serializeFields_length_uniform (fields : List (List Bool)) (W : ℕ)
    (h : ∀ x ∈ fields,x.length≤W) : (serializeFields fields).1.length≤(2*W+1)*fields.length := by
  induction fields with
  | nil => simp [serializeFields]
  | cons x xs ih =>
    have hx := serializeField_length x
    have hw := h x (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [serializeFields,List.length_append,List.length_cons]
    nlinarith

lemma reduceRaw_length (raw : Raw) : (reduceRaw raw).1.length≤outputBudget (rawMeasure raw) := by
  have hw := construct_target_width raw
  have hi := construct_items_width raw
  have hn := construct_items_length raw
  have he := serializeFields_length_uniform ((construct raw).1.1::(construct raw).1.2)
    (integerWidth (rawMeasure raw)) (by simpa only [List.mem_cons,forall_eq_or_imp] using And.intro hw hi)
  simp only [List.length_cons] at he
  have hmul := Nat.mul_le_mul_left (2*integerWidth (rawMeasure raw)+1) (Nat.add_le_add_right hn 1)
  unfold reduceRaw
  dsimp only
  split_ifs <;> dsimp only <;> unfold outputBudget
  · have h : fixedYes.length=6 := by norm_num [fixedYes,ComplexityEncoding.encodeFields,ComplexityEncoding.encodeNat_length]
    omega
  · omega
  · have h : fixedNo.length=8 := by
      have hsize : Nat.size 2=2 := by simpa using (Nat.size_pow (n := 1))
      norm_num [fixedNo,ComplexityEncoding.encodeFields,ComplexityEncoding.encodeNat_length,hsize]
    omega

lemma outputBudget_mono {L M : ℕ} (h : L≤M) : outputBudget L≤outputBudget M := by
  unfold outputBudget
  gcongr
  exact integerWidth_mono h

/-- Cost of the entire total reduction on arbitrary original input bitstrings. -/
theorem reduceThree_cost (bits : List Bool) : (reduceThree bits).2≤reductionBudget bits.length := by
  have hp := NPCNF.Encoding.parse_cost bits
  unfold reduceThree
  cases hs : (NPCNF.Encoding.parse bits).1 with
  | none => simp only [hs]; unfold reductionBudget; omega
  | some raw =>
    have hr := (reduceRaw_cost raw).trans (rawReductionBudget_mono (parsed_rawMeasure_bound hs))
    simp only [hs]
    unfold reductionBudget
    omega

theorem reduceThree_length (bits : List Bool) : (reduceThree bits).1.length≤outputBudget bits.length := by
  unfold reduceThree
  cases hs : (NPCNF.Encoding.parse bits).1 with
  | none =>
    simp only [hs]
    have h : fixedNo.length=8 := by
      have hsize : Nat.size 2=2 := by simpa using (Nat.size_pow (n := 1))
      norm_num [fixedNo,ComplexityEncoding.encodeFields,ComplexityEncoding.encodeNat_length,hsize]
    unfold outputBudget
    omega
  | some raw =>
    simp only [hs]
    exact (reduceRaw_length raw).trans (outputBudget_mono (parsed_rawMeasure_bound hs))

noncomputable def reductionPolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let packing := 4096*(2*X+1)^2*(X+13)^2
  let width := 2*X*(X+12)
  let item := X*(24*(X+1))+X*(64*(X+1)^3+4)+packing+X+8
  let construction := (X*(2*item+6)+1)+(3*X+1)+16*(X+1)^2+
    (2*X*(packing+X+4)+1)+(5*X+4)+packing+2*X+12
  64*(X+1)^2+128*(X+1)^3+8*X+construction+(9*width+6)*(4*X+1)+56

noncomputable def outputPolynomial : Polynomial ℕ :=
  (2*(2*Polynomial.X*(Polynomial.X+12))+1)*(4*Polynomial.X+1)+20

lemma reductionPolynomial_eval (L : ℕ) : reductionPolynomial.eval L=reductionBudget L := by
  simp only [reductionPolynomial,reductionBudget,rawReductionBudget,constructBudget,itemBudget,packingBudget,integerWidth,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  ring
lemma outputPolynomial_eval (L : ℕ) : outputPolynomial.eval L=outputBudget L := by
  simp [outputPolynomial,outputBudget,integerWidth]

/-- A concrete total bitstring reduction, with semantic equivalence, polynomial
bit-operation counter and polynomial output length all concerning the same
executed program. This is independent of any claim that 3SAT is NP-complete. -/
theorem total_three_sat_reduction (bits : List Bool) :
    (PositiveSubsetSumLanguage (reduceThree bits).1 ↔ ThreeCNFLanguage bits) ∧
      (reduceThree bits).2≤reductionPolynomial.eval bits.length ∧
      (reduceThree bits).1.length≤outputPolynomial.eval bits.length := by
  rw [reductionPolynomial_eval,outputPolynomial_eval]
  exact ⟨reduceThree_correct bits,reduceThree_cost bits,reduceThree_length bits⟩

end BalancedAssortments.NPSATSubsetSum
