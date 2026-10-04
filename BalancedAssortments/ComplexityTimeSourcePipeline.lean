import BalancedAssortments.ComplexityTimeSourceRows
import BalancedAssortments.ComplexityTimeClearing
import BalancedAssortments.ComplexityTimeSystem

/-! Complete raw source-row construction, bitwise denominator clearing, and
integer checking. Numeric source data are never passed to a rational-arithmetic
oracle. Input-field parsing is a separate representation layer. -/
namespace BalancedAssortments.ComplexityTimeSourcePipeline
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions
open ComplexityTimeSourceRows DecisionPolyhedron Decomposition.CostMachine

/-- Enumerating n bounded indices and traversing the result lists is explicitly
charged; each coordinate evaluator is the concrete raw-fraction algorithm. -/
def rowEntries {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (row : Row n) : List Fraction × ℕ :=
  let b := boundRaw v K H row
  let cs := List.ofFn (fun j : Fin n => coefficientRaw v r α H mask row j)
  (b.1 :: cs.map Prod.fst,b.2+(cs.map Prod.snd).sum+8*(n+1)^2)

theorem rowEntries_data {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (row : Row n) :
    (rowEntries v r α H K mask row).1 =
      (boundRaw v K H row).1 :: List.ofFn (fun j => (coefficientRaw v r α H mask row j).1) := by
  simp [rowEntries,List.map_ofFn,Function.comp_def]

@[simp] theorem rowEntries_length {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (row : Row n) : (rowEntries v r α H K mask row).1.length = n+1 := by simp [rowEntries]

def assemblyBudget (n B : ℕ) : ℕ := (n+1)*scalarBudget n B+8*(n+1)^2

theorem rowEntries_bounds {n B : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (hvn : v.length ≤ n) (hrn : r.length ≤ n) (hmn : mask.length ≤ n)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (hK : K.length ≤ B) (row : Row n) :
    (∀ x ∈ (rowEntries v r α H K mask row).1, ComplexityTimeFractions.width x ≤ 3*B+5) ∧
    (rowEntries v r α H K mask row).2 ≤ assemblyBudget n B := by
  have hb := boundRaw_bounds v K H hvn hv hK hH row
  have hc := coefficientRaw_bounds v r α H mask hvn hrn hmn hv hr hα hH row
  constructor
  · rw [rowEntries_data]
    simp only [List.mem_cons]
    intro x hx
    rcases hx with rfl | hx
    · exact hb.1
    · obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact (hc j).1
  · have hs : (∑ j : Fin n, (coefficientRaw v r α H mask row j).2) ≤ n*scalarBudget n B := by
      calc (∑ j : Fin n, (coefficientRaw v r α H mask row j).2) ≤ ∑ _j : Fin n, scalarBudget n B :=
          Finset.sum_le_sum (fun j _ => (hc j).2)
           _ = n*scalarBudget n B := by simp
    simp only [rowEntries,List.map_ofFn,List.sum_ofFn,Function.comp_def,assemblyBudget]
    nlinarith [hb.2]

lemma denominator_volume (xs : List Fraction) (W : ℕ)
    (h : ∀ x ∈ xs, ComplexityTimeFractions.width x ≤ W) :
    bitVolume (xs.map Fraction.den) ≤ xs.length*W := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hd : x.den.length ≤ W := (le_max_right _ _).trans hx
    have hi := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons,bitVolume_cons,List.length_cons]
    nlinarith

/-- Compile an augmented raw row and split its cleared RHS from coefficients. -/
def compiledRow {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (row : Row n) : (List ZBits × ZBits) × ℕ :=
  let raw := rowEntries v r α H K mask row
  let c := clearSigned (raw.1.map Fraction.den) 0 (raw.1.map Fraction.num)
  ((c.1.tail,c.1.headD zzero),raw.2+c.2+6*(n+1)+8)

def clearingVolume (n B : ℕ) : ℕ := (n+1)*(3*B+5)
def compiledRowBudget (n B : ℕ) : ℕ :=
  assemblyBudget n B+(n+1)*((n+2)*(4*inputProductBudget (clearingVolume n B)))+6*(n+1)+9

theorem compiledRow_length {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (row : Row n) : (compiledRow v r α H K mask row).1.1.length = n := by
  simp [compiledRow,clearSigned_length]

lemma headD_width (xs : List ZBits) (W : ℕ) (h : ∀ x ∈ xs, ComplexityTimeVerifier.width x ≤ W) :
    ComplexityTimeVerifier.width (xs.headD zzero) ≤ W := by
  cases xs with
  | nil => simp [zzero,ComplexityTimeVerifier.width]
  | cons x xs => exact h x (by simp)

theorem compiledRow_bounds {n B : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (hvn : v.length ≤ n) (hrn : r.length ≤ n) (hmn : mask.length ≤ n)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (hK : K.length ≤ B) (row : Row n) :
    (∀ x ∈ (compiledRow v r α H K mask row).1.1, ComplexityTimeVerifier.width x ≤ 4*clearingVolume n B+1) ∧
    ComplexityTimeVerifier.width (compiledRow v r α H K mask row).1.2 ≤ 4*clearingVolume n B+1 ∧
    (compiledRow v r α H K mask row).2 ≤ compiledRowBudget n B := by
  have hraw := rowEntries_bounds v r α H K mask hvn hrn hmn hv hr hα hH hK row
  let raw := (rowEntries v r α H K mask row).1
  have hd : bitVolume (raw.map Fraction.den) ≤ clearingVolume n B := by
    simpa [raw,clearingVolume] using denominator_volume raw (3*B+5) hraw.1
  have hn : ∀ x ∈ raw.map Fraction.num, ComplexityTimeVerifier.width x ≤ clearingVolume n B := by
    intro x hx
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hx
    have hw := hraw.1 f hf
    have hh : ComplexityTimeVerifier.width f.num ≤ 3*B+5 := (le_max_left _ _).trans hw
    unfold clearingVolume
    nlinarith
  have hc := clearSigned_cost (raw.map Fraction.den) hd 0 (raw.map Fraction.num) hn
  have hw := clearSigned_width (raw.map Fraction.den) hd 0 (raw.map Fraction.num) hn
  refine ⟨?_,?_,?_⟩
  · intro x hx
    exact hw x (List.mem_of_mem_tail hx)
  · exact headD_width _ _ hw
  · simp only [List.length_map] at hc
    have hl : raw.length = n+1 := rowEntries_length v r α H K mask row
    rw [hl] at hc
    change (rowEntries v r α H K mask row).2+_+6*(n+1)+8 ≤ _
    unfold compiledRowBudget
    nlinarith [hraw.2]

/-- Explicit constructor enumeration of all source rows, avoiding a noncomputable
choice of an equivalence between the row type and an initial segment. -/
def rowList (n : ℕ) : List (Row n) :=
  (List.finRange n).map Row.nonnegative ++ (List.finRange n).map Row.cap ++ [Row.rank] ++
  (List.finRange n).flatMap (fun i => (List.finRange n).map (Row.balance i)) ++
  (List.finRange n).map Row.offsupport ++ [Row.target]

theorem rowList_complete {n : ℕ} (row : Row n) : row ∈ rowList n := by
  cases row <;> simp [rowList]

theorem rowList_length (n : ℕ) : (rowList n).length = n*n+3*n+2 := by
  simp [rowList,List.length_flatMap,List.map_const',List.sum_replicate]
  ring

/-- Descriptor construction, bounded unary-index copying and list concatenation
are charged by a uniform per-emitted-row list-operation budget. -/
def enumerationCost (n : ℕ) : ℕ := 16*(n+1)*(n*n+3*n+2)+4

def compileRows {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool) :
    List (Row n) → List (List ZBits × ZBits) × ℕ
  | [] => ([],1)
  | row::rows =>
      let x := compiledRow v r α H K mask row
      let rest := compileRows v r α H K mask rows
      (x.1::rest.1,x.2+rest.2+4)

theorem compileRows_data {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (rows : List (Row n)) :
    (compileRows v r α H K mask rows).1 = rows.map (fun row => (compiledRow v r α H K mask row).1) := by
  induction rows <;> simp [compileRows, *]

@[simp] theorem compileRows_length {n : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (rows : List (Row n)) : (compileRows v r α H K mask rows).1.length = rows.length := by
  rw [compileRows_data,List.length_map]

theorem compileRows_cost {n B : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (hvn : v.length ≤ n) (hrn : r.length ≤ n) (hmn : mask.length ≤ n)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (hK : K.length ≤ B) (rows : List (Row n)) :
    (compileRows v r α H K mask rows).2 ≤ rows.length*(compiledRowBudget n B+4)+1 := by
  induction rows with
  | nil => simp [compileRows]
  | cons row rows ih =>
    have hc := (compiledRow_bounds v r α H K mask hvn hrn hmn hv hr hα hH hK row).2.2
    simp only [compileRows,List.length_cons]
    nlinarith

/-- Complete source verifier on raw bit-field inputs. It generates and clears
all rational rows itself before invoking the shared-certificate integer checker. -/
def verifySourceSized (n : ℕ) (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits) : Bool × ℕ :=
  let rows := compileRows v r α H K mask (rowList n)
  let checked := checkSystem p q rows.1
  (checked.1,rows.2+checked.2+enumerationCost n+4)

/-- The dimension is read from the supplied attraction list, not from an
unbounded binary promise about how many rows should be allocated. -/
def verifySource (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits) : Bool × ℕ :=
  let x := verifySourceSized v.length v r α H K mask p q
  (x.1,x.2+4*v.length+1)

def sourceBudget (n B C P : ℕ) : ℕ :=
  let W := 4*clearingVolume n B+1+C
  (n*n+3*n+2)*(compiledRowBudget n B+4)+1 +
  ((n*n+3*n+2)*(rowBudget (n+P) W+4)+48*W+27)+enumerationCost n+4

/-- End-to-end polynomial bit/list-operation cost from raw source fields to the
Boolean certificate decision, including coefficient generation and clearing. -/
theorem verifySourceSized_cost {n B C : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits)
    (hvn : v.length ≤ n) (hrn : r.length ≤ n) (hmn : mask.length ≤ n)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (hK : K.length ≤ B) (hp : ∀ x ∈ p, ComplexityTimeVerifier.width x ≤ C)
    (hq : ComplexityTimeVerifier.width q ≤ C) :
    (verifySourceSized n v r α H K mask p q).2 ≤ sourceBudget n B C p.length := by
  let W := 4*clearingVolume n B+1+C
  have hrows : ∀ row ∈ (compileRows v r α H K mask (rowList n)).1,
      row.1.length ≤ n+p.length ∧
      (∀ x ∈ row.1, ComplexityTimeVerifier.width x ≤ W) ∧ ComplexityTimeVerifier.width row.2 ≤ W := by
    rw [compileRows_data]
    intro row hrow
    obtain ⟨label,_,rfl⟩ := List.mem_map.mp hrow
    have hh := compiledRow_bounds v r α H K mask hvn hrn hmn hv hr hα hH hK label
    refine ⟨?_,?_,?_⟩
    · rw [compiledRow_length]; omega
    · intro x hx
      exact (hh.1 x hx).trans (by dsimp [W]; omega)
    · exact hh.2.1.trans (by dsimp [W]; omega)
  have hpp : ∀ x ∈ p, ComplexityTimeVerifier.width x ≤ W :=
    fun x hx => (hp x hx).trans (by dsimp [W]; omega)
  have hqq : ComplexityTimeVerifier.width q ≤ W := hq.trans (by dsimp [W]; omega)
  have hcheck := checkSystem_cost p q (compileRows v r α H K mask (rowList n)).1
    (n+p.length) W (by omega) hpp hqq hrows
  rw [compileRows_length,rowList_length] at hcheck
  have hcompile := compileRows_cost v r α H K mask hvn hrn hmn hv hr hα hH hK (rowList n)
  rw [rowList_length] at hcompile
  dsimp only [W] at hcheck
  unfold verifySourceSized sourceBudget
  dsimp only
  omega

theorem verifySource_cost {B C : ℕ} (v r : List Fraction) (α H : Fraction) (K mask : List Bool)
    (p : List ZBits) (q : ZBits)
    (hrn : r.length ≤ v.length) (hmn : mask.length ≤ v.length)
    (hv : ∀ x ∈ v, ComplexityTimeFractions.width x ≤ B)
    (hr : ∀ x ∈ r, ComplexityTimeFractions.width x ≤ B)
    (hα : ComplexityTimeFractions.width α ≤ B) (hH : ComplexityTimeFractions.width H ≤ B)
    (hK : K.length ≤ B) (hp : ∀ x ∈ p, ComplexityTimeVerifier.width x ≤ C)
    (hq : ComplexityTimeVerifier.width q ≤ C) :
    (verifySource v r α H K mask p q).2 ≤ sourceBudget v.length B C p.length+4*v.length+1 := by
  have h := verifySourceSized_cost v r α H K mask p q le_rfl hrn hmn hv hr hα hH hK hp hq
  simp only [verifySource]
  omega

end BalancedAssortments.ComplexityTimeSourcePipeline
