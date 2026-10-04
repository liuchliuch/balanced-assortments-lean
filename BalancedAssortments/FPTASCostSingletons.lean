import BalancedAssortments.FPTASCostLoops

namespace BalancedAssortments.FPTASCostSingletons
open KnapsackCostRational

def zeroes : List Fraction → List Fraction × ℕ
  | [] => ([],1)
  | _::xs => let rest := zeroes xs; (FPTASCostKernel.zero::rest.1,rest.2+4)

lemma zeroes_eq (xs : List Fraction) : (zeroes xs).1 = List.replicate xs.length FPTASCostKernel.zero := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [zeroes,ih,List.replicate_succ]
lemma zeroes_cost (xs : List Fraction) : (zeroes xs).2 = 4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [zeroes,ih,List.replicate_succ]; omega

def prependZero : List (List Fraction) → List (List Fraction) × ℕ
  | [] => ([],1)
  | x::xs => let rest := prependZero xs; ( (FPTASCostKernel.zero::x)::rest.1,rest.2+4)

lemma prependZero_eq (xs : List (List Fraction)) :
    (prependZero xs).1 = xs.map (FPTASCostKernel.zero::·) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [prependZero,ih]
lemma prependZero_cost (xs : List (List Fraction)) : (prependZero xs).2 = 4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [prependZero,ih]; omega

/-- Build each singleton sales vector using only list cells and existing input
fractions; every copied zero spine is charged. -/
def singletons : List Fraction → List (List Fraction) × ℕ
  | [] => ([],1)
  | v::vs =>
      let zs := zeroes vs
      let tail := singletons vs
      let padded := prependZero tail.1
      ((v::zs.1)::padded.1,zs.2+tail.2+padded.2+4)

lemma singletons_count (vs : List Fraction) : (singletons vs).1.length = vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [singletons,prependZero_eq,ih]

lemma singletons_cost (vs : List Fraction) : (singletons vs).2 ≤ 8*vs.length^2+8*vs.length+1 := by
  induction vs with
  | nil => simp [singletons]
  | cons v vs ih =>
    simp only [singletons,zeroes_cost,prependZero_cost,singletons_count,List.length_cons]
    nlinarith

lemma singletons_shape (vs : List Fraction) :
    ∀ xs ∈ (singletons vs).1, xs.length = vs.length ∧ ∀ x ∈ xs, x = FPTASCostKernel.zero ∨ x ∈ vs := by
  induction vs with
  | nil => simp [singletons]
  | cons v vs ih =>
    intro xs hxs
    simp only [singletons,List.mem_cons,prependZero_eq,List.mem_map] at hxs
    rcases hxs with rfl | ⟨ys,hys,rfl⟩
    · refine ⟨by simp [zeroes_eq], ?_⟩
      intro x hx
      simp only [List.mem_cons,zeroes_eq,List.mem_replicate] at hx
      rcases hx with rfl | ⟨_,rfl⟩
      · exact Or.inr (by simp)
      · exact Or.inl rfl
    · obtain ⟨hlen,hmem⟩ := ih ys hys
      refine ⟨by simp [hlen], ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · rcases hmem x hx with hz | hm
        · exact Or.inl hz
        · exact Or.inr (List.mem_cons_of_mem _ hm)

def rationalSingletons : List ℚ → List (List ℚ)
  | [] => []
  | v::vs => (v::List.replicate vs.length 0) :: ((rationalSingletons vs).map (0::·))

lemma singletons_decode (vs : List Fraction) :
    (singletons vs).1.map (List.map Fraction.decode) = rationalSingletons (vs.map Fraction.decode) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [singletons,List.map_cons,zeroes_eq,prependZero_eq,List.map_map,
      List.map_replicate,FPTASCostKernel.zero_decode,rationalSingletons,List.length_map]
    rw [← ih,List.map_map]
    simp only [Function.comp_def,List.map_cons,FPTASCostKernel.zero_decode]

/-- Recursive singleton enumeration agrees with the paper's finite-coordinate
singleton vectors, in the standard Fin order. -/
lemma rationalSingletons_ofFn {n : ℕ} (v : Fin n → ℚ) :
    rationalSingletons (List.ofFn v) =
      List.ofFn (fun j : Fin n => List.ofFn (fun i : Fin n => if i=j then v j else 0)) := by
  induction n with
  | zero => simp [rationalSingletons]
  | succ n ih =>
    simp only [List.ofFn_succ,rationalSingletons,ih]
    congr 1
    · congr 1
      have hh : (fun i : Fin n => if i.succ = (0 : Fin (n+1)) then v 0 else 0) = fun _ => (0 : ℚ) := by
        funext i; simp
      rw [hh]
      simp
    · rw [List.map_ofFn]
      apply congrArg List.ofFn
      funext j
      simp only [Function.comp_apply,List.ofFn_succ]
      congr 1
      · simp

end BalancedAssortments.FPTASCostSingletons
