import frontier.SparseMonomial
import frontier.MCSPScope
import frontier.BooleanMobius

/-
The all-certificates sparse lower bound for a wide positive clause plus
negative units. Coefficients are rational, exponents arbitrary naturals.
The lower bound counts NONZERO coefficient records, including each slot
separately. The certificate-to-support implication is derived, not assumed.
-/

namespace SparseCertificateBound

open SparseMonomial

def nonzeroRecords {α : Type} (p : List (α × Rat)) : List (α × Rat) :=
  p.filter (fun t => decide (t.2 ≠ 0))

def nzCount {α : Type} (p : List (α × Rat)) : Nat := (nonzeroRecords p).length

theorem nonzeroRecords_map {α β : Type} (p : List (α × Rat)) (f : α → β) :
    nonzeroRecords (p.map (fun t => (f t.1,t.2))) =
      (nonzeroRecords p).map (fun t => (f t.1,t.2)) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      simp only [nonzeroRecords] at ih ⊢
      by_cases h : t.2 = 0 <;> simpa [h] using ih

theorem nzCount_map {α β : Type} (p : List (α × Rat)) (f : α → β) :
    nzCount (p.map (fun t => (f t.1,t.2))) = nzCount p := by
  simp only [nzCount, nonzeroRecords_map, List.length_map]

theorem nzCount_append {α : Type} (p q : List (α × Rat)) :
    nzCount (p++q) = nzCount p + nzCount q := by
  simp [nzCount, nonzeroRecords, List.filter_append]

def forceAt : List Bool → Nat → List Bool
  | [], _ => []
  | _ :: bs, 0 => true :: bs
  | b :: bs, i+1 => b :: forceAt bs i

theorem forceAt_length (s : List Bool) (i : Nat) :
    (forceAt s i).length = s.length := by
  induction s generalizing i with
  | nil => rfl
  | cons b bs ih => cases i <;> simp [forceAt, ih]

theorem forceAt_eval (s a : List Bool) (i : Nat)
    (hlen : s.length = a.length) (hi : i < s.length) :
    maskEval (forceAt s i) a = (maskEval s a && selBool a i) := by
  induction s generalizing a i with
  | nil => simp at hi
  | cons use ss ih =>
      cases a with
      | nil => simp at hlen
      | cons b bs =>
          cases i with
          | zero => cases use <;> cases b <;> simp [forceAt, maskEval, selBool]
          | succ i =>
              have htail : ss.length = bs.length := by simpa using hlen
              have hitail : i < ss.length := by simp at hi; omega
              simp only [forceAt, maskEval, selBool]
              rw [ih bs i htail hitail]
              cases use <;> cases b <;> simp

def PolyWidth (n : Nat) (p : List ExponentToken) : Prop :=
  ∀ t ∈ p, t.1.length = n

def unitTokens (i : Nat) (p : List ExponentToken) : List MaskToken :=
  p.map (fun t => (forceAt (support t.1) i,t.2))

def unitTokensFrom (i : Nat) : List (List ExponentToken) → List MaskToken
  | [] => []
  | p :: ps => unitTokens i p ++ unitTokensFrom (i+1) ps

def unitValueFrom (i : Nat) : List (List ExponentToken) → List Bool → Rat
  | [], _ => 0
  | p :: ps, a =>
      (if selBool a i then expPolyValue p a else 0) + unitValueFrom (i+1) ps a

theorem unitTokens_nzCount (i : Nat) (p : List ExponentToken) :
    nzCount (unitTokens i p) = nzCount p := by
  simpa only [unitTokens] using nzCount_map p (fun es => forceAt (support es) i)

theorem unitTokensFrom_nzCount (qs : List (List ExponentToken)) (i : Nat) :
    nzCount (unitTokensFrom i qs) = (qs.map nzCount).sum := by
  induction qs generalizing i with
  | nil => rfl
  | cons p ps ih => simp [unitTokensFrom, nzCount_append, unitTokens_nzCount, ih]

theorem unitTokens_width (n i : Nat) (p : List ExponentToken) (hp : PolyWidth n p) :
    ∀ t ∈ unitTokens i p, t.1.length = n := by
  intro t ht
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
  simp only [forceAt_length, support_length]
  exact hp u hu

theorem unitTokensFrom_width (n : Nat) (qs : List (List ExponentToken)) (i : Nat)
    (hq : ∀ p ∈ qs, PolyWidth n p) :
    ∀ t ∈ unitTokensFrom i qs, t.1.length = n := by
  induction qs generalizing i with
  | nil => simp [unitTokensFrom]
  | cons p ps ih =>
      intro t ht
      rcases List.mem_append.mp ht with ht | ht
      · exact unitTokens_width n i p (hq p List.mem_cons_self) t ht
      · exact ih (i+1) (fun p hp => hq p (List.mem_cons_of_mem _ hp)) t ht

theorem maskPolyValue_append (p q : List MaskToken) (a : List Bool) :
    maskPolyValue (p++q) a = maskPolyValue p a + maskPolyValue q a := by
  simp [maskPolyValue, List.map_append, List.sum_append]

theorem unitTokens_value (n i : Nat) (p : List ExponentToken)
    (hp : PolyWidth n p) (a : List Bool) (ha : a.length = n) (hi : i < n) :
    maskPolyValue (unitTokens i p) a =
      (if selBool a i then expPolyValue p a else 0) := by
  induction p with
  | nil => cases selBool a i <;> simp [unitTokens]
  | cons t p ih =>
      have ht : (support t.1).length = a.length := by simp [hp t List.mem_cons_self, ha]
      have hi' : i < (support t.1).length := by simp [hp t List.mem_cons_self, hi]
      have hitail := ih (fun u hu => hp u (List.mem_cons_of_mem t hu))
      change (if maskEval (forceAt (support t.1) i) a then t.2 else 0) +
        maskPolyValue (unitTokens i p) a =
        (if selBool a i then
          (if exponentEval t.1 a then t.2 else 0) + expPolyValue p a else 0)
      rw [forceAt_eval (support t.1) a i ht hi', collapse_eval]
      cases hs : selBool a i <;> simp [hs] at hitail ⊢
      · rw [hitail]
        exact Rat.zero_add 0
      · rw [hitail]

theorem unitTokensFrom_value (n i : Nat) (qs : List (List ExponentToken))
    (hbound : i+qs.length ≤ n) (hq : ∀ p ∈ qs, PolyWidth n p)
    (a : List Bool) (ha : a.length = n) :
    maskPolyValue (unitTokensFrom i qs) a = unitValueFrom i qs a := by
  induction qs generalizing i with
  | nil => rfl
  | cons p ps ih =>
      have hi : i < n := by simp only [List.length_cons] at hbound; omega
      rw [unitTokensFrom, maskPolyValue_append,
        unitTokens_value n i p (hq p List.mem_cons_self) a ha hi,
        ih (i+1) (by simp only [List.length_cons] at hbound; omega)
          (fun p hp => hq p (List.mem_cons_of_mem _ hp))]
      rfl

def zeroMask (n : Nat) : List Bool := List.replicate n false

theorem sel_zeroMask (n i : Nat) : selBool (zeroMask n) i = false := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => simpa [zeroMask, List.replicate_succ, selBool] using ih i

theorem zeroMask_any (n : Nat) : (zeroMask n).any id = false := by
  simp [zeroMask]

theorem eq_zeroMask_of_any_false (a : List Bool) (h : a.any id = false) :
    a = zeroMask a.length := by
  induction a with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          have ht : bs.any id = false := by simpa using h
          simpa [zeroMask, List.replicate_succ] using congrArg (false :: ·) (ih ht)
      | true => simp at h

theorem unitValueFrom_zeroMask (qs : List (List ExponentToken)) (i n : Nat) :
    unitValueFrom i qs (zeroMask n) = 0 := by
  induction qs generalizing i with
  | nil => rfl
  | cons p ps ih => simp [unitValueFrom, sel_zeroMask, ih, Rat.zero_add]

/-- Actual rational coefficient records evaluated on all Boolean points.
The wide-clause generator is the zero-row indicator; unit generators are
x_i. Boolean-axiom coefficients make zero contributions on these points. -/
def BooleanCertificate (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat) : Prop :=
  ∀ a : List Bool, a.length = n →
    (if a.any id then 0 else expPolyValue q0 a) + unitValueFrom 0 qs a = D

theorem certificate_unit_target (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat)
    (hc : BooleanCertificate n q0 qs D) :
    ∀ a : List Bool, a.length = n →
      unitValueFrom 0 qs a = (if a.any id then D else 0) := by
  intro a ha
  cases h : a.any id with
  | false =>
      have heq : a = zeroMask n := by simpa only [ha] using eq_zeroMask_of_any_false a h
      rw [heq, unitValueFrom_zeroMask]
      rfl
  | true => simpa only [h, ite_eq_left, Rat.zero_add] using hc a ha

theorem certificate_q0_at_zero (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat)
    (hc : BooleanCertificate n q0 qs D) : expPolyValue q0 (zeroMask n) = D := by
  have h := hc (zeroMask n) (by simp [zeroMask])
  simpa [zeroMask_any, unitValueFrom_zeroMask, Rat.add_zero] using h


theorem certificate_nonempty_mask_record (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat) (hD : D ≠ 0)
    (hlen : qs.length = n) (hq : ∀ p ∈ qs, PolyWidth n p)
    (hc : BooleanCertificate n q0 qs D)
    (S : List Bool) (hS : S.length = n) (hne : true ∈ S) :
    ∃ t ∈ unitTokensFrom 0 qs, t.1 = S ∧ t.2 ≠ 0 := by
  have hw : ∀ t ∈ unitTokensFrom 0 qs, t.1.length = S.length := by
    intro t ht
    exact (unitTokensFrom_width n qs 0 hq t ht).trans hS.symm
  have heval : ∀ a, a.length = S.length →
      maskPolyValue (unitTokensFrom 0 qs) a = BooleanMobius.nonzeroAt D a := by
    intro a ha
    have han : a.length = n := ha.trans hS
    rw [unitTokensFrom_value n 0 qs (by omega) hq a han]
    exact certificate_unit_target n q0 qs D hc a han
  have ht := BooleanMobius.transform_congr S
    (maskPolyValue (unitTokensFrom 0 qs)) (BooleanMobius.nonzeroAt D) heval
  have hnonzero : BooleanMobius.transform S (maskPolyValue (unitTokensFrom 0 qs)) ≠ 0 := by
    rw [ht]
    exact BooleanMobius.target_nonzero S D hne hD
  exact BooleanMobius.exists_nonzero_record_of_transform_ne_zero S _ hw hnonzero

theorem expPolyValue_zero_of_all_coeff_zero (p : List ExponentToken) (a : List Bool)
    (hz : ∀ t ∈ p, t.2 = 0) : expPolyValue p a = 0 := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      have ht := hz t List.mem_cons_self
      have hp := ih (fun u hu => hz u (List.mem_cons_of_mem t hu))
      simp [expPolyValue_cons, ht, hp, Rat.zero_add]

theorem eval_nonzero_has_nonzero_record (p : List ExponentToken) (a : List Bool)
    (hne : expPolyValue p a ≠ 0) : ∃ t, t ∈ nonzeroRecords p := by
  apply Classical.byContradiction
  intro hnot
  have hz : ∀ t ∈ p, t.2 = 0 := by
    intro t ht
    apply Classical.byContradiction
    intro hc
    apply hnot
    refine ⟨t, ?_⟩
    exact List.mem_filter.mpr ⟨ht, by simp [hc]⟩
  exact hne (expPolyValue_zero_of_all_coeff_zero p a hz)

def certificateMasks (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) : List (List Bool) :=
  (nonzeroRecords q0).map (fun _ => zeroMask n) ++
    (nonzeroRecords (unitTokensFrom 0 qs)).map Prod.fst

theorem certificateMasks_length (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) :
    (certificateMasks n q0 qs).length = nzCount q0 + (qs.map nzCount).sum := by
  simp only [certificateMasks, List.length_append, List.length_map]
  change nzCount q0 + nzCount (unitTokensFrom 0 qs) = _
  rw [unitTokensFrom_nzCount]

theorem certificate_all_masks_covered (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat) (hD : D ≠ 0)
    (hlen : qs.length = n) (hq : ∀ p ∈ qs, PolyWidth n p)
    (hc : BooleanCertificate n q0 qs D) :
    ∀ S ∈ MCSPScope.allAssignments n, S ∈ certificateMasks n q0 qs := by
  intro S hSmem
  have hS : S.length = n := (MCSPScope.mem_allAssignments n S).mp hSmem
  by_cases htrue : true ∈ S
  · obtain ⟨t,ht,heq,hnz⟩ := certificate_nonempty_mask_record n q0 qs D hD
      hlen hq hc S hS htrue
    apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨t, ?_, heq⟩
    exact List.mem_filter.mpr ⟨ht, by simp [hnz]⟩
  · have hany : S.any id = false := by
      cases h : S.any id with
      | false => rfl
      | true =>
          obtain ⟨b,hb,hbt⟩ := List.any_eq_true.mp h
          have heq : b = true := hbt
          subst b
          exact False.elim (htrue hb)
    have hzero : S = zeroMask n := by
      simpa only [hS] using eq_zeroMask_of_any_false S hany
    have heval : expPolyValue q0 (zeroMask n) ≠ 0 := by
      rw [certificate_q0_at_zero n q0 qs D hc]
      exact hD
    obtain ⟨t,ht⟩ := eval_nonzero_has_nonzero_record q0 (zeroMask n) heval
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨t,ht,hzero.symm⟩

/-- ALL rational Boolean-evaluated certificates for the wide clause and
negative units require at least 2^n NONZERO sparse coefficient records.
No support-cover premise, coefficient nonzero premise, or token-nodup
premise is assumed. Arbitrary natural exponents are included. -/
theorem sparse_certificate_bound (n : Nat) (q0 : List ExponentToken)
    (qs : List (List ExponentToken)) (D : Rat) (hD : D ≠ 0)
    (hlen : qs.length = n) (hq : ∀ p ∈ qs, PolyWidth n p)
    (hc : BooleanCertificate n q0 qs D) :
    2^n ≤ nzCount q0 + (qs.map nzCount).sum := by
  have hcount : (MCSPScope.allAssignments n).length ≤
      (certificateMasks n q0 qs).length := by
    apply Classical.byContradiction
    intro hnot
    obtain ⟨S,hS,hmissing⟩ := exists_missing_of_length_lt
      (MCSPScope.allAssignments n) (certificateMasks n q0 qs)
      (MCSPScope.allAssignments_nodup n) (by omega)
    exact hmissing (certificate_all_masks_covered n q0 qs D hD hlen hq hc S hS)
  simpa only [MCSPScope.allAssignments_length, certificateMasks_length] using hcount

/-! ## Thin actual-rational-evaluation Nullstellensatz wrapper -/

def ratSel : List Rat → Nat → Rat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i+1 => ratSel xs i

theorem ratSel_boolEmbed (a : List Bool) (i : Nat) :
    ratSel (boolEmbed a) i = ratValue (selBool a i) := by
  induction a generalizing i with
  | nil => rfl
  | cons b bs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

def wideValue : List Rat → Rat
  | [] => 1
  | x :: xs => (1-x)*wideValue xs

theorem wideValue_boolEmbed (a : List Bool) :
    wideValue (boolEmbed a) = (if a.any id then 0 else 1) := by
  induction a with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          change (1-0)*wideValue (boolEmbed bs) = (if bs.any id then 0 else 1)
          rw [BooleanMobius.rat_sub_zero, Rat.one_mul]
          exact ih
      | true =>
          change (1-1)*wideValue (boolEmbed bs) = 0
          rw [Rat.sub_self, Rat.zero_mul]

def ratUnitValueFrom (i : Nat) : List (List ExponentToken) → List Rat → Rat
  | [], _ => 0
  | p :: ps, xs => ratPolyValue p xs * ratSel xs i + ratUnitValueFrom (i+1) ps xs

theorem ratUnitValueFrom_boolEmbed (qs : List (List ExponentToken)) (i : Nat)
    (a : List Bool) : ratUnitValueFrom i qs (boolEmbed a) = unitValueFrom i qs a := by
  induction qs generalizing i with
  | nil => rfl
  | cons p ps ih =>
      rw [ratUnitValueFrom, ratPolyValue_boolEmbed, ratSel_boolEmbed, ih]
      cases h : selBool a i <;>
        simp [unitValueFrom, h, ratValue, Rat.mul_zero, Rat.mul_one]

def ratAxiomValueFrom (i : Nat) : List (List ExponentToken) → List Rat → Rat
  | [], _ => 0
  | p :: ps, xs => ratPolyValue p xs * ((ratSel xs i)^2-ratSel xs i) +
      ratAxiomValueFrom (i+1) ps xs

theorem ratAxiomValueFrom_boolEmbed (rs : List (List ExponentToken)) (i : Nat)
    (a : List Bool) : ratAxiomValueFrom i rs (boolEmbed a) = 0 := by
  induction rs generalizing i with
  | nil => rfl
  | cons p ps ih =>
      have hbeta : (ratSel (boolEmbed a) i)^2-ratSel (boolEmbed a) i = 0 := by
        rw [ratSel_boolEmbed]
        cases selBool a i <;>
          simp [ratValue, Rat.pow_succ, Rat.pow_zero, Rat.mul_one, Rat.sub_self]
      rw [ratAxiomValueFrom, hbeta, Rat.mul_zero, ih, Rat.zero_add]

/-- Exact evaluation identity on ALL rational points, with actual sparse
natural-exponent coefficients for q0, all n unit coefficients, and all n
Boolean-axiom coefficients. This predicate does not postulate a cover or a
multilinear quotient identity. A formal polynomial identity implies this
predicate; coefficientwise polynomial identity itself is not defined here. -/
def RationalCertificate (n : Nat) (q0 : List ExponentToken)
    (qs rs : List (List ExponentToken)) (D : Rat) : Prop :=
  qs.length = n ∧ rs.length = n ∧ PolyWidth n q0 ∧
  (∀ p ∈ qs, PolyWidth n p) ∧ (∀ p ∈ rs, PolyWidth n p) ∧
  ∀ xs : List Rat, xs.length = n →
    ratPolyValue q0 xs * wideValue xs + ratUnitValueFrom 0 qs xs +
      ratAxiomValueFrom 0 rs xs = D

theorem rational_certificate_to_boolean (n : Nat) (q0 : List ExponentToken)
    (qs rs : List (List ExponentToken)) (D : Rat)
    (hc : RationalCertificate n q0 qs rs D) : BooleanCertificate n q0 qs D := by
  obtain ⟨_,_,_,_,_,hid⟩ := hc
  intro a ha
  have h := hid (boolEmbed a) (by simp [ha])
  rw [ratPolyValue_boolEmbed, wideValue_boolEmbed, ratUnitValueFrom_boolEmbed,
    ratAxiomValueFrom_boolEmbed, Rat.add_zero] at h
  cases hany : a.any id <;> simpa [hany, Rat.mul_zero, Rat.mul_one] using h

/-- ALL actual rational-evaluation NS identities in the stated sparse format
obey the exponential nonzero-record lower bound. Arbitrary Boolean-axiom
coefficients cannot evade it. -/
theorem rational_certificate_bound (n : Nat) (q0 : List ExponentToken)
    (qs rs : List (List ExponentToken)) (D : Rat) (hD : D ≠ 0)
    (hc : RationalCertificate n q0 qs rs D) :
    2^n ≤ nzCount q0 + (qs.map nzCount).sum := by
  have hbool := rational_certificate_to_boolean n q0 qs rs D hc
  obtain ⟨hlen,_,_,hq,_,_⟩ := hc
  exact sparse_certificate_bound n q0 qs D hD hlen hq hbool

theorem nullstellensatz_total_records_bound (n : Nat) (q0 : List ExponentToken)
    (qs rs : List (List ExponentToken))
    (hc : RationalCertificate n q0 qs rs 1) :
    2^n ≤ nzCount q0 + (qs.map nzCount).sum + (rs.map nzCount).sum := by
  have h := rational_certificate_bound n q0 qs rs 1 (by decide) hc
  omega
#print axioms forceAt_eval
#print axioms unitTokensFrom_value
#print axioms certificate_unit_target
#print axioms certificate_all_masks_covered
#print axioms sparse_certificate_bound
#print axioms rational_certificate_to_boolean
#print axioms rational_certificate_bound
#print axioms nullstellensatz_total_records_bound

end SparseCertificateBound