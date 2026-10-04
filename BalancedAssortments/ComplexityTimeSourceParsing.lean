import BalancedAssortments.ComplexityTimeCertificateSize
import BalancedAssortments.EncodingTime

/-! Total source/certificate grammars over the existing self-delimiting Boolean
field parser. Numeric dimensions are checked after parsing actual records; they
are never trusted as allocation or loop bounds. -/
namespace BalancedAssortments.ComplexityTimeSourceParsing
open ComplexityTimeBinary ComplexityTimeVerifier ComplexityTimeFractions ComplexityTimeSourceRows
open ComplexityTimeSourcePipeline ComplexityEncoding

structure Source where
  declaredCount : List Bool
  capacity : List Bool
  alpha : Fraction
  target : Fraction
  products : List (Fraction × Fraction)
  deriving DecidableEq

structure Certificate where
  denominator : ZBits
  mask : List Bool
  numerators : List ZBits
  deriving DecidableEq

/-- The source body is six unsigned fields per signed price/attraction fraction. -/
def parseProducts : List (List Bool) → Option (List (Fraction × Fraction)) × ℕ
  | [] => (some [],1)
  | rp::rn::rd::vp::vn::vd::rest =>
      let r := parseProducts rest
      (r.1.map (fun xs => (⟨(rp,rn),rd⟩,⟨(vp,vn),vd⟩)::xs),r.2+24)
  | _ => (none,1)

def packSource : List (List Bool) → Option Source × ℕ
  | count::K::ap::an::ad::hp::hn::hd::rest =>
      let r := parseProducts rest
      (r.1.map (fun products => ⟨count,K,⟨(ap,an),ad⟩,⟨(hp,hn),hd⟩,products⟩),r.2+24)
  | _ => (none,1)

def parseSource (bits : List Bool) : Option Source × ℕ :=
  let p := EncodingTime.parse bits
  match p.1 with
  | none => (none,p.2+4)
  | some fields => let s := packSource fields; (s.1,p.2+s.2+4)

/-- A certificate mask field must encode exactly zero or one. -/
def parseMask (bits : List Bool) : Option Bool × ℕ :=
  let z := compareBits bits []
  let o := compareBits bits [true]
  (if z.1 = .eq then some false else if o.1 = .eq then some true else none,z.2+o.2+6)

def parseTriples : List (List Bool) → Option (List Bool × List ZBits) × ℕ
  | [] => (some ([],[]),1)
  | mb::pp::pn::rest =>
      let m := parseMask mb
      let r := parseTriples rest
      (match m.1,r.1 with
       | some b,some (ms,ps) => some (b::ms,(pp,pn)::ps)
       | _,_ => none,m.2+r.2+12)
  | _ => (none,1)

def packCertificate : List (List Bool) → Option Certificate × ℕ
  | qp::qn::rest =>
      let r := parseTriples rest
      (r.1.map (fun mp => ⟨(qp,qn),mp.1,mp.2⟩),r.2+8)
  | _ => (none,1)

def parseCertificate (bits : List Bool) : Option Certificate × ℕ :=
  let p := EncodingTime.parse bits
  match p.1 with
  | none => (none,p.2+4)
  | some fields => let c := packCertificate fields; (c.1,p.2+c.2+4)

def fieldVolume (fields : List (List Bool)) : ℕ := (fields.map (fun x => x.length+1)).sum

@[simp] theorem fieldVolume_nil : fieldVolume [] = 0 := rfl
@[simp] theorem fieldVolume_cons (x : List Bool) (xs : List (List Bool)) :
    fieldVolume (x::xs) = x.length+1+fieldVolume xs := rfl

/-- Successful raw parsing cannot manufacture more field bits/cells than were
present in the actual input string. -/
theorem raw_parser_volume (fuel bits : List Bool) (fields : List (List Bool))
    (h : (EncodingTime.parseAux fuel bits).1 = some fields) : fieldVolume fields ≤ bits.length := by
  induction fuel generalizing bits fields with
  | nil => cases bits <;> simp [EncodingTime.parseAux] at h <;> simp_all
  | cons f fuel ih =>
    cases bits with
    | nil => simp [EncodingTime.parseAux] at h; simp_all
    | cons b bits =>
      cases hp : (EncodingTime.parseField (b::bits)).1 with
      | none => simp [EncodingTime.parseAux,hp] at h
      | some pair =>
        obtain ⟨payload,rest⟩ := pair
        have hl : payload.length+rest.length < (b::bits).length :=
          decodeRawNat_lengths (by rw [← EncodingTime.parseField_correct]; exact hp)
        cases hr : (EncodingTime.parseAux fuel rest).1 with
        | none => simp [EncodingTime.parseAux,hp,hr] at h
        | some fs =>
          simp [EncodingTime.parseAux,hp,hr] at h
          subst fields
          have hi := ih rest fs hr
          simp only [fieldVolume_cons]
          omega

theorem parse_volume (bits : List Bool) (fields : List (List Bool))
    (h : (EncodingTime.parse bits).1 = some fields) : fieldVolume fields ≤ bits.length :=
  raw_parser_volume bits bits fields h

lemma field_count_le_volume (fields : List (List Bool)) : fields.length ≤ fieldVolume fields := by
  induction fields <;> simp_all [fieldVolume_cons] <;> omega

lemma field_member_length (fields : List (List Bool)) (x : List Bool) (hx : x ∈ fields) :
    x.length ≤ fieldVolume fields := by
  induction fields with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · simp only [fieldVolume_cons]; omega
    · have h := ih hx
      simp only [fieldVolume_cons]; omega

theorem parseProducts_cost (fields : List (List Bool)) : (parseProducts fields).2 ≤ 24*fields.length+1 := by
  fun_induction parseProducts fields
  · simp
  · rename_i rp rn rd vp vn vd rest r ih
    subst r
    simp only [List.length_cons] at *
    omega
  · omega

theorem packSource_cost (fields : List (List Bool)) : (packSource fields).2 ≤ 24*fields.length+25 := by
  fun_cases packSource fields
  · rename_i count K ap an ad hp hn hd rest r
    try subst r
    dsimp only at *
    have h := parseProducts_cost rest
    simp_all only [List.length_cons]
    omega
  · omega

theorem parseSource_cost (bits : List Bool) : (parseSource bits).2 ≤ 100*(bits.length+1)^2 := by
  have hp := EncodingTime.parse_cost bits
  have hsq : 0 < (bits.length+1)^2 := by positivity
  unfold parseSource
  cases he : (EncodingTime.parse bits).1 with
  | none => simp only [he]; nlinarith
  | some fs =>
    have hv := parse_volume bits fs he
    have hl := field_count_le_volume fs
    have hc := packSource_cost fs
    simp only [he]
    nlinarith

theorem parseMask_cost (bits : List Bool) : (parseMask bits).2 ≤ 32*bits.length+40 := by
  simp only [parseMask,compareBits_cost,List.length_nil,List.length_cons,Nat.max_zero]
  omega

theorem parseTriples_cost (fields : List (List Bool)) :
    (parseTriples fields).2 ≤ 64*fieldVolume fields+1 := by
  fun_induction parseTriples fields
  · simp
  · rename_i mb pp pn rest m r ih
    try subst m
    try subst r
    dsimp only at *
    have hm := parseMask_cost mb
    simp_all only [fieldVolume_cons]
    omega
  · simp only [fieldVolume_cons]
    omega

theorem packCertificate_cost (fields : List (List Bool)) :
    (packCertificate fields).2 ≤ 64*fieldVolume fields+9 := by
  fun_cases packCertificate fields
  · rename_i qp qn rest r
    try subst r
    dsimp only at *
    have h := parseTriples_cost rest
    simp_all only [fieldVolume_cons]
    omega
  · omega

theorem parseCertificate_cost (bits : List Bool) : (parseCertificate bits).2 ≤ 100*(bits.length+1)^2 := by
  have hp := EncodingTime.parse_cost bits
  have hsq : 0 < (bits.length+1)^2 := by positivity
  unfold parseCertificate
  cases he : (EncodingTime.parse bits).1 with
  | none => simp only [he]; nlinarith
  | some fs =>
    have hv := parse_volume bits fs he
    have hc := packCertificate_cost fs
    simp only [he]
    nlinarith

theorem parseTriples_dimensions (fields : List (List Bool)) (ms : List Bool) (ps : List ZBits)
    (h : (parseTriples fields).1 = some (ms,ps)) : ms.length = ps.length := by
  fun_induction parseTriples fields generalizing ms ps
  · simp at h
    rcases h with ⟨rfl,rfl⟩
    rfl
  · rename_i mb pp pn rest m r ih
    try subst m
    try subst r
    dsimp only at *
    cases hm : (parseMask mb).1 with
    | none => simp [hm] at h
    | some b =>
      cases hr : (parseTriples rest).1 with
      | none => simp [hm,hr] at h
      | some pair =>
        obtain ⟨ms',ps'⟩ := pair
        simp [hm,hr] at h
        rcases h with ⟨rfl,rfl⟩
        have hh := ih ms' ps' hr
        simp [hh]
  · simp at h

end BalancedAssortments.ComplexityTimeSourceParsing
