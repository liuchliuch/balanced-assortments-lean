import BalancedAssortments.NPCNFStackCatalogueCalls

namespace BalancedAssortments.NPCNF.StackCatalogue
open NPStack NPStack.Macros
open NPStackFields (tagBits dataFields)
open ComplexityTimeBinary
open Encoding (catalogFields)

def chooseMaximum (label m : List Bool) : List Bool := if leBits label m then m else label

def chooseCost (label m : List Bool) : ℕ := if leBits label m then 0 else m.length+1+(5*label.length+4)

def maximumCost (label m : List Bool) : ℕ :=
  (5*label.length+4)+(5*m.length+4)+(2*max label.length m.length+5)+1+chooseCost label m

lemma maximum_call (label rest m cat : List Bool) :
    Run program (maximumCost label m)
      (cfg .copyQuery (store rest m [] label [] cat [] [] []))
      (cfg .emitLabel (store rest (chooseMaximum label m) [] label [] cat [] [] [])) := by
  have hs := (copy_query_call label rest m cat).trans ((copy_maximum_call label rest m cat).trans
    ((compare_call label rest m cat).trans (.one (inspect_order (leBits label m) label rest m cat))))
  cases h : leBits label m with
  | true => simpa [maximumCost,chooseCost,chooseMaximum,h,Nat.add_assoc] using hs
  | false =>
    simp only [h,Bool.false_eq_true,↓reduceIte] at hs
    have hh := hs.trans (replace_maximum_call label rest m cat)
    simpa [maximumCost,chooseCost,chooseMaximum,h,Nat.add_assoc] using hh

def recordCost (label : List Bool) (seen : List (List Bool)) (m : List Bool) : ℕ :=
  11+(5*label.length+4)+(NPStackCatalogueMember.memberCost label seen+2)+1+maximumCost label m+(5*label.length+5)

lemma record_run (label rest m : List Bool) (seen : List (List Bool)) (hn : value label∉seen.map value) :
    Run program (recordCost label seen m)
      (cfg .readTag (store (tagBits [true]++false::(tagBits label++false::rest)) m [] [] [] (dataFields seen) [] [] []))
      (cfg .readTag (store rest (chooseMaximum label m) [] [] [] (dataFields (label::seen)) [] [] [])) := by
  have hmem := member_call label rest m seen
  simp only [hn,decide_false] at hmem
  have hh := (header_call true (tagBits label++false::rest) m (dataFields seen)).trans
    ((read_label_call label rest m (dataFields seen)).trans (hmem.trans
      (.succ (inspect_member false label rest m (dataFields seen))
        ((maximum_call label rest m (dataFields seen)).trans
          (emit_label_call label rest (chooseMaximum label m) (dataFields seen))))))
  convert hh using 1 <;> simp [recordCost,dataFields,List.append_assoc] <;> omega

def selectedMaximum : List (List Bool) → List Bool → List Bool
  | [],m => m
  | x::xs,m => selectedMaximum xs (chooseMaximum x m)

def catalogueCost : List (List Bool) → List (List Bool) → List Bool → ℕ
  | [],_,m => 11+(5*m.length+8)
  | x::xs,seen,m => recordCost x seen m+catalogueCost xs (x::seen) (chooseMaximum x m)

/-- The catalogue header loop validates numeric distinctness, preserves raw
label bytes in reverse order, leaves the formula suffix untouched, and computes
freshness using the actual finite binary adder. -/
theorem catalogue_run (labels seen : List (List Bool)) (rest m : List Bool)
    (hn : (labels.map value++seen.map value).Nodup) :
    Run program (catalogueCost labels seen m)
      (cfg .readTag (store (dataFields (catalogFields labels)++rest) m [] [] [] (dataFields seen) [] [] []))
      (cfg .accept (store rest [] (addCarry (selectedMaximum labels m) [] true).1 [] []
        (dataFields (labels.reverse++seen)) [] [] [])) := by
  induction labels generalizing seen m with
  | nil =>
    have hh := (header_call false rest m (dataFields seen)).trans (fresh_call rest m (dataFields seen))
    simpa [catalogueCost,selectedMaximum,catalogFields,dataFields,List.append_assoc] using hh
  | cons x xs ih =>
    have hn' : (value x::(xs.map value++seen.map value)).Nodup := by simpa using hn
    have hx : value x∉seen.map value := by
      intro hm;exact (List.nodup_cons.mp hn').1 (List.mem_append_right _ hm)
    have htail : (xs.map value++(x::seen).map value).Nodup := by
      simp only [List.map_cons]
      exact List.perm_middle.nodup_iff.mpr hn'
    have hhead := record_run x (dataFields (catalogFields xs)++rest) m seen hx
    have hh := hhead.trans (ih (x::seen) (chooseMaximum x m) htail)
    simpa [catalogueCost,selectedMaximum,catalogFields,dataFields,List.reverse_cons,List.flatMap_append,List.append_assoc] using hh

lemma chooseMaximum_value (x m : List Bool) : value (chooseMaximum x m)=max (value x) (value m) := by
  by_cases h : leBits x m=true
  · have hv := (leBits_correct x m).mp h
    simp [chooseMaximum,h,max_eq_right hv]
  · have hb : leBits x m=false := Bool.eq_false_iff.mpr h
    have hv : value m ≤ value x := by
      have hn : ¬ value x ≤ value m := fun hh => h ((leBits_correct x m).mpr hh)
      omega
    simp [chooseMaximum,hb,max_eq_left hv]

lemma selectedMaximum_value (labels : List (List Bool)) (m : List Bool) :
    value (selectedMaximum labels m)=max (maxLabel (labels.map value)) (value m) := by
  induction labels generalizing m with
  | nil => simp [selectedMaximum,maxLabel]
  | cons x xs ih => simp [selectedMaximum,ih,chooseMaximum_value,maxLabel,max_assoc,max_comm,max_left_comm]

lemma fresh_value (labels : List (List Bool)) :
    value (addCarry (selectedMaximum labels []) [] true).1=maxLabel (labels.map value)+1 := by
  simp [addCarry_value,selectedMaximum_value,value]

lemma chooseMaximum_length {x m : List Bool} {B : ℕ} (hx : x.length ≤ B) (hm : m.length ≤ B) :
    (chooseMaximum x m).length ≤ B := by
  unfold chooseMaximum;split <;> assumption

lemma selectedMaximum_length (labels : List (List Bool)) (m : List Bool) {B : ℕ}
    (hlabels : ∀ x∈labels,x.length ≤ B) (hm : m.length ≤ B) :
    (selectedMaximum labels m).length ≤ B := by
  induction labels generalizing m with
  | nil => exact hm
  | cons x xs ih =>
    exact ih (chooseMaximum x m) (fun y hy => hlabels y (by simp [hy])) (chooseMaximum_length (hlabels x (by simp)) hm)

lemma fresh_length (labels : List (List Bool)) {B : ℕ} (hlabels : ∀ x∈labels,x.length ≤ B) :
    (addCarry (selectedMaximum labels []) [] true).1.length ≤ B+1 := by
  have hh := addCarry_length (selectedMaximum labels []) [] true
  have hm := selectedMaximum_length labels [] hlabels (by simp)
  simp only [List.length_nil,Nat.max_zero] at hh
  omega

lemma recordCost_bound (label : List Bool) (seen : List (List Bool)) (m : List Bool) {N B : ℕ}
    (hl : label.length ≤ B) (hm : m.length ≤ B) (hs : ∀ x∈seen,x.length ≤ B) (hn : seen.length ≤ N) :
    recordCost label seen m ≤ 100*(N+1)*(B+1) := by
  have hsum : (seen.map List.length).sum ≤ seen.length*B := by
    induction seen with
    | nil => simp
    | cons x xs ih =>
      have hx := hs x (by simp)
      have ht := ih (fun y hy => hs y (by simp [hy])) (by simp at hn;omega)
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      nlinarith
  have hmember := NPStackCatalogueMember.memberCost_bound label seen
  have hmax : max label.length m.length ≤ B := max_le hl hm
  have hchoose : chooseCost label m ≤ m.length+1+(5*label.length+4) := by
    unfold chooseCost;split <;> omega
  have hnB : seen.length*B ≤ N*B := Nat.mul_le_mul_right B hn
  unfold recordCost maximumCost
  nlinarith

/-- Cubic coarse bound in actual field count and maximal raw label bit width;
no bound depends on a decoded label magnitude. -/
theorem catalogueCost_bound (labels seen : List (List Bool)) (m : List Bool) {N B : ℕ}
    (hlabels : ∀ x∈labels,x.length ≤ B) (hseen : ∀ x∈seen,x.length ≤ B)
    (hm : m.length ≤ B) (hn : labels.length+seen.length ≤ N) :
    catalogueCost labels seen m ≤ labels.length*(100*(N+1)*(B+1))+5*B+19 := by
  induction labels generalizing seen m with
  | nil => simp [catalogueCost];omega
  | cons x xs ih =>
    have hx := hlabels x (by simp)
    have hrec := recordCost_bound x seen m (N:=N) hx hm hseen (by simp at hn;omega)
    have ht := ih (x::seen) (chooseMaximum x m) (fun y hy => hlabels y (by simp [hy]))
      (by intro y hy;rcases List.mem_cons.mp hy with rfl|hy;exact hx;exact hseen y hy)
      (chooseMaximum_length hx hm) (by simp at hn ⊢;omega)
    simp only [catalogueCost,List.length_cons]
    nlinarith

end BalancedAssortments.NPCNF.StackCatalogue
