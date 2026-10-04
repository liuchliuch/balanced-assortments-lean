import BalancedAssortments.KnapsackCostEncoding

/-! Binary score tests and exact minimum-weight compression for the DP.
The scan charges every bit comparison and rational cross multiplication. -/
namespace BalancedAssortments.KnapsackCostState
open ComplexityTimeBinary KnapsackCostRational

theorem compare_fraction_lt {x y : Fraction} (hx : x.Valid) (hy : y.Valid) :
    (KnapsackCostRational.compare x y).1 = .lt ↔ x.decode < y.decode := by
  have h := KnapsackCostRational.compare_correct hx hy
  cases he : (KnapsackCostRational.compare x y).1 <;>
    simp only [he, rationalMeaning] at h <;> simp [he] <;> linarith

theorem compare_score_eq (x y : List Bool) :
    (compareBits x y).1 = .eq ↔ value x = value y := by
  have h := compareBits_correct x y
  cases he : (compareBits x y).1 <;>
    simp only [he, comparisonMeaning] at h <;> simp [he] <;> omega

def choose (old : Option State) (candidate : State) : Option State × ℕ :=
  match old with
  | none => (some candidate, 2)
  | some s =>
      let cmp := KnapsackCostRational.compare candidate.weight s.weight
      (if cmp.1 = .lt then some candidate else some s, cmp.2 + 4)

theorem choose_member {old : Option State} {candidate s : State}
    (hs : (choose old candidate).1 = some s) : s = candidate ∨ old = some s := by
  cases old with
  | none => simp [choose] at hs; exact Or.inl hs.symm
  | some o =>
    simp only [choose] at hs
    split_ifs at hs <;> simp_all

theorem choose_valid {old : Option State} {candidate : State}
    (ho : ∀ s, old = some s → s.Valid) (hc : candidate.Valid) :
    ∀ s, (choose old candidate).1 = some s → s.Valid := by
  intro s hs
  rcases choose_member hs with rfl | hs
  · exact hc
  · exact ho s hs

theorem choose_width {old : Option State} {candidate : State} {b : ℕ}
    (ho : ∀ s, old = some s → s.Width b) (hc : candidate.Width b) :
    ∀ s, (choose old candidate).1 = some s → s.Width b := by
  intro s hs
  rcases choose_member hs with rfl | hs
  · exact hc
  · exact ho s hs

theorem choose_cost {old : Option State} {candidate : State} {b : ℕ}
    (ho : ∀ s, old = some s → s.Width b) (hc : candidate.Width b) :
    (choose old candidate).2 ≤ 512*(b+1)^2 + 4 := by
  cases old with
  | none => simp [choose]
  | some s => exact Nat.add_le_add_right (compare_cost hc.1 (ho s rfl).1) 4

theorem choose_decode {old : Option State} {candidate : State}
    (ho : ∀ s, old = some s → s.Valid) (hc : candidate.Valid) :
    (choose old candidate).1.map State.decode =
      List.argAux (fun a b : Knapsack.State => a.weight < b.weight)
        (old.map State.decode) candidate.decode := by
  cases old with
  | none => rfl
  | some s =>
    have hh := compare_fraction_lt hc.1 (ho s rfl).1
    simp only [choose, List.argAux, Option.map_some]
    by_cases h : candidate.weight.decode < s.weight.decode
    · simp [hh.mpr h, State.decode, h]
    · have hn : (KnapsackCostRational.compare candidate.weight s.weight).1 ≠ .lt :=
        fun he => h (hh.mp he)
      simp [hn, State.decode, h]

/-- A complete min-weight scan at one encoded scaled-profit index. -/
def scan : List State → List Bool → Option State → Option State × ℕ
  | [], _, old => (old, 1)
  | s :: ss, p, old =>
      let cmp := compareBits s.scaled p
      let chosen := if cmp.1 = .eq then choose old s else (old, 1)
      let rest := scan ss p chosen.1
      (rest.1, cmp.2 + chosen.2 + rest.2 + 8)

theorem scan_valid {states : List State} {p : List Bool} {old : Option State}
    (ho : ∀ s, old = some s → s.Valid) (hs : ∀ s ∈ states, s.Valid) :
    ∀ s, (scan states p old).1 = some s → s.Valid := by
  induction states generalizing old with
  | nil => exact ho
  | cons s ss ih =>
    simp only [scan]
    apply ih
    · split_ifs
      · exact choose_valid ho (hs s (by simp))
      · exact ho
    · exact fun t ht => hs t (by simp [ht])

theorem scan_decode {states : List State} {p : List Bool} {old : Option State}
    (ho : ∀ s, old = some s → s.Valid) (hs : ∀ s ∈ states, s.Valid) :
    (scan states p old).1.map State.decode =
      ((states.map State.decode).filter (fun s => s.scaled = value p)).foldl
        (List.argAux (fun a b : Knapsack.State => a.weight < b.weight))
        (old.map State.decode) := by
  induction states generalizing old with
  | nil => rfl
  | cons s ss ih =>
    have hss : ∀ t ∈ ss, t.Valid := fun t ht => hs t (by simp [ht])
    have hv : s.Valid := hs s (by simp)
    by_cases he : value s.scaled = value p
    · have hh := (compare_score_eq s.scaled p).mpr he
      simp only [scan, hh, ↓reduceIte, List.map_cons, List.filter_cons,
        State.decode, he, decide_true, ↓reduceIte, List.foldl_cons]
      have hi := ih (choose_valid ho hv) hss
      rw [choose_decode ho hv] at hi
      simpa only [State.decode, he] using hi
    · have hh : (compareBits s.scaled p).1 ≠ .eq := fun h => he ((compare_score_eq _ _).mp h)
      simp only [scan, hh, ↓reduceIte, List.map_cons, List.filter_cons,
        State.decode, he, decide_false, ↓reduceIte]
      exact ih ho hss

/-- Exact refinement of the certified DP's `bestAt`, including tie-breaking. -/
theorem bestAt_decode {states : List State} {p : List Bool}
    (hs : ∀ s ∈ states, s.Valid) :
    (scan states p none).1.map State.decode =
      Knapsack.bestAt (states.map State.decode) (value p) := by
  exact scan_decode (by simp) hs

theorem scan_cost {states : List State} {p : List Bool} {old : Option State} {b : ℕ}
    (hp : p.length ≤ b)
    (ho : ∀ s, old = some s → s.Width b) (hs : ∀ s ∈ states, s.Width b) :
    (scan states p old).2 ≤ states.length * (1024*(b+1)^2) + 1 := by
  induction states generalizing old with
  | nil => simp [scan]
  | cons s ss ih =>
    have hss : ∀ t ∈ ss, t.Width b := fun t ht => hs t (by simp [ht])
    have hw : s.Width b := hs s (by simp)
    have hl : max s.scaled.length p.length ≤ b := max_le hw.2.2.1 hp
    have hchoose := choose_cost ho hw
    have hrest := ih (choose_width ho hw) hss
    have hold := ih ho hss
    simp only [scan, compareBits_cost, List.length_cons]
    split_ifs <;> nlinarith

theorem scan_member {states : List State} {p : List Bool} {old : Option State} {s : State}
    (hs : (scan states p old).1 = some s) : s ∈ states ∨ old = some s := by
  induction states generalizing old with
  | nil => exact Or.inr hs
  | cons t ts ih =>
    simp only [scan] at hs
    split_ifs at hs with he
    · rcases ih hs with hm | hm
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · rcases choose_member hm with rfl | hm
        · exact Or.inl (by simp)
        · exact Or.inr hm
    · rcases ih hs with hm | hm
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr hm

/-- Compress all provided score indices, retaining one exact minimum-weight state. -/
def compress : List State → List (List Bool) → List State × ℕ
  | _, [] => ([], 1)
  | states, p :: ps =>
      let head := scan states p none
      let tail := compress states ps
      (match head.1 with | none => tail.1 | some s => s :: tail.1,
        head.2 + tail.2 + 4)

theorem compress_decode {states : List State} (scores : List (List Bool))
    (hs : ∀ s ∈ states, s.Valid) :
    (compress states scores).1.map State.decode =
      scores.filterMap (fun p => Knapsack.bestAt (states.map State.decode) (value p)) := by
  induction scores with
  | nil => rfl
  | cons p ps ih =>
    have hh := bestAt_decode (p := p) hs
    simp only [compress, List.filterMap_cons]
    rw [← hh]
    cases he : (scan states p none).1 <;> simp [he, ih]

theorem compress_length (states : List State) (scores : List (List Bool)) :
    (compress states scores).1.length ≤ scores.length := by
  induction scores with
  | nil => simp [compress]
  | cons p ps ih =>
    simp only [compress, List.length_cons]
    cases (scan states p none).1 <;> simp_all <;> omega

theorem compress_member {states : List State} {scores : List (List Bool)} {s : State}
    (hs : s ∈ (compress states scores).1) : s ∈ states := by
  induction scores with
  | nil => simp [compress] at hs
  | cons p ps ih =>
    simp only [compress] at hs
    cases he : (scan states p none).1 with
    | none => rw [he] at hs; exact ih hs
    | some t =>
      rw [he] at hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact (scan_member he).resolve_right (by simp)
      · exact ih hs

theorem compress_cost {states : List State} {scores : List (List Bool)} {b : ℕ}
    (hp : ∀ p ∈ scores, p.length ≤ b) (hs : ∀ s ∈ states, s.Width b) :
    (compress states scores).2 ≤ scores.length * (states.length * (1024*(b+1)^2) + 5) + 1 := by
  induction scores with
  | nil => simp [compress]
  | cons p ps ih =>
    have hh := scan_cost (hp p (by simp)) (old := none) (by simp) hs
    have ht := ih (fun p hp' => hp p (by simp [hp']))
    simp only [compress, List.length_cons]
    nlinarith

end BalancedAssortments.KnapsackCostState
