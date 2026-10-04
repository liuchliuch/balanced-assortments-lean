import BalancedAssortments.FixedSupportCostSerializedInput

/-! Physical support-mask selection and bounded positional labeling. Every
loop traverses an actual list. Positional successors are charged by their unary
size upper bound; no decoded numeric value is used as an iteration bound. -/
namespace BalancedAssortments.FixedSupportAmbientPreprocess
open FixedSupportCostPoints FixedSupportCostProgram FixedSupportCostRational

def selectProducts : List Product → List Bool → Option (List Product) × ℕ
  | [],[] => (some [],1)
  | [],_::_ => (none,1)
  | _::_,[] => (none,1)
  | p::ps,b::bs =>
    let tail := selectProducts ps bs
    (tail.1.map (fun xs => if b then p::xs else xs),tail.2+4)

def selected (ps : List Product) (mask : List Bool) : List Product :=
  (ps.zip mask).filterMap (fun p => if p.2 then some p.1 else none)

lemma selectProducts_correct (ps : List Product) (mask : List Bool) :
    (selectProducts ps mask).1=if ps.length=mask.length then some (selected ps mask) else none := by
  induction ps generalizing mask with
  | nil => cases mask <;> simp [selectProducts,selected]
  | cons p ps ih =>
    cases mask with
    | nil => simp [selectProducts]
    | cons b bs =>
      simp only [selectProducts,ih,List.length_cons,Nat.add_right_cancel_iff]
      by_cases h : ps.length=bs.length
      · cases b <;> simp [h,selected]
      · simp [h]

lemma selectProducts_cost (ps : List Product) (mask : List Bool) :
    (selectProducts ps mask).2 ≤ 4*ps.length+1 := by
  induction ps generalizing mask with
  | nil => cases mask <;> simp [selectProducts]
  | cons p ps ih =>
    cases mask with
    | nil => simp [selectProducts]
    | cons b bs => have h:=ih bs;simp only [selectProducts,List.length_cons];omega

lemma selected_sublist (ps : List Product) (mask : List Bool) : (selected ps mask).Sublist ps := by
  induction ps generalizing mask with
  | nil => simp [selected]
  | cons p ps ih =>
    cases mask with
    | nil => simp [selected]
    | cons b bs =>
      cases b
      · simpa [selected] using (ih bs).cons p
      · simpa [selected] using (ih bs).cons₂ p

lemma selectProducts_some {ps xs : List Product} {mask : List Bool}
    (h : (selectProducts ps mask).1=some xs) :
    ps.length=mask.length ∧ xs=selected ps mask ∧ xs.Sublist ps := by
  rw [selectProducts_correct] at h
  split_ifs at h with he
  · cases h
    exact ⟨he,rfl,selected_sublist ps mask⟩

/-- A bounded position index is incremented only once per remaining record.
Its conservative successor charge i+4 dominates bitwise successor and record
construction for a position at most the physical list length. -/
def labelAux {N : ℕ} (i : ℕ) (ps : List Product) (h : i+ps.length≤N) :
    List (Fin N × Product) × ℕ :=
  match ps with
  | [] => ([],1)
  | p::ps =>
    let tail := labelAux (i+1) ps (by simp only [List.length_cons] at h;omega)
    ((⟨i,by simp only [List.length_cons] at h;omega⟩,p)::tail.1,tail.2+i+4)

def labelProducts (ps : List Product) : List (Fin ps.length × Product) × ℕ :=
  let out := labelAux 0 ps (by omega)
  (out.1,out.2+ps.length+1)

lemma labelAux_data {N : ℕ} (i : ℕ) (ps : List Product) (h : i+ps.length≤N) :
    (labelAux i ps h).1.map Prod.snd=ps := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih => simp [labelAux,ih]
lemma labelAux_values {N : ℕ} (i : ℕ) (ps : List Product) (h : i+ps.length≤N) :
    (labelAux i ps h).1.map (fun p => p.1.val)=List.range' i ps.length := by
  induction ps generalizing i with
  | nil => rfl
  | cons p ps ih => simp [labelAux,ih,List.range'_succ]
lemma labelAux_cost {N : ℕ} (i : ℕ) (ps : List Product) (h : i+ps.length≤N) :
    (labelAux i ps h).2 ≤ ps.length*(N+4)+1 := by
  induction ps generalizing i with
  | nil => simp [labelAux]
  | cons p ps ih =>
    have hh := ih (i+1) (by simp only [List.length_cons] at h;omega)
    simp only [labelAux,List.length_cons]
    simp only [List.length_cons] at h
    nlinarith

@[simp] theorem labelProducts_data (ps : List Product) : (labelProducts ps).1.map Prod.snd=ps := labelAux_data _ _ _
@[simp] theorem labelProducts_labels (ps : List Product) :
    (labelProducts ps).1.map Prod.fst=List.finRange ps.length := by
  apply List.map_injective_iff.mpr Fin.val_injective
  simpa [labelProducts,List.map_map,Function.comp_def,List.range_eq_range'] using labelAux_values (N := ps.length) 0 ps (by omega)
@[simp] theorem labelProducts_length (ps : List Product) : (labelProducts ps).1.length=ps.length := by
  have hh := congrArg List.length (labelProducts_data ps)
  simpa only [List.length_map] using hh
lemma labelProducts_cost (ps : List Product) : (labelProducts ps).2 ≤ (ps.length+1)*(ps.length+6) := by
  have hh := labelAux_cost 0 ps (N := ps.length) (by omega)
  simp only [labelProducts]
  nlinarith

structure Prepared where
  products : List Product
  indexed : List (Fin products.length × Product)

def prepare (ps : List Product) (mask : List Bool) : Option Prepared × ℕ :=
  let chosen := selectProducts ps mask
  match chosen.1 with
  | none => (none,chosen.2+1)
  | some xs =>
    let labeled := labelProducts xs
    (some ⟨xs,labeled.1⟩,chosen.2+labeled.2+3)

theorem prepare_correct {ps : List Product} {mask : List Bool} {out : Prepared}
    (h : (prepare ps mask).1=some out) :
    ps.length=mask.length ∧ out.products=selected ps mask ∧ out.products.Sublist ps ∧
      out.indexed=(labelProducts out.products).1 ∧
      out.indexed.map Prod.fst=List.finRange out.products.length ∧
      out.indexed.map Prod.snd=out.products := by
  unfold prepare at h
  cases hs : (selectProducts ps mask).1 with
  | none => simp [hs] at h
  | some xs =>
    simp only [hs,Option.some.injEq] at h
    subst out
    have hh := selectProducts_some hs
    exact ⟨hh.1,hh.2.1,hh.2.2,rfl,labelProducts_labels xs,labelProducts_data xs⟩

theorem prepare_cost (ps : List Product) (mask : List Bool) :
    (prepare ps mask).2 ≤ 4*ps.length+1+(ps.length+1)*(ps.length+6)+3 := by
  have hs := selectProducts_cost ps mask
  unfold prepare
  cases he : (selectProducts ps mask).1 with
  | none => simp only [he];omega
  | some xs =>
    have hlen := (selectProducts_some he).2.2.length_le
    have hl := labelProducts_cost xs
    have hm : (xs.length+1)*(xs.length+6)≤(ps.length+1)*(ps.length+6) := by gcongr
    simp only [he]
    omega

lemma prepare_success (ps : List Product) (mask : List Bool) (h : ps.length=mask.length) :
    ∃ out,(prepare ps mask).1=some out := by
  have hs : (selectProducts ps mask).1=some (selected ps mask) := by rw [selectProducts_correct,if_pos h]
  exact ⟨⟨selected ps mask,(labelProducts (selected ps mask)).1⟩,by simp [prepare,hs]⟩
lemma prepare_mismatch (ps : List Product) (mask : List Bool) (h : ps.length≠mask.length) :
    (prepare ps mask).1=none := by
  have hs : (selectProducts ps mask).1=none := by rw [selectProducts_correct,if_neg h]
  simp [prepare,hs]
@[simp] lemma prepare_empty : prepare [] []=(some ⟨[],[]⟩,6) := rfl
lemma selected_all_false (ps : List Product) : selected ps (List.replicate ps.length false)=[] := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [selected,List.replicate_succ] using ih
lemma prepare_all_false (ps : List Product) :
    ∃ out,(prepare ps (List.replicate ps.length false)).1=some out ∧ out.products=[] := by
  obtain ⟨out,hout⟩ := prepare_success ps (List.replicate ps.length false) (by simp)
  exact ⟨out,hout,(prepare_correct hout).2.1.trans (selected_all_false ps)⟩

end BalancedAssortments.FixedSupportAmbientPreprocess
