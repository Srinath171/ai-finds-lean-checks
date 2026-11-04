import frontier.FirstGateExtension
import frontier.ParityTeaching
import frontier.CircuitRewiring
import frontier.GraphHoles

/-
A cheaper parity phase gives an optimal residual circuit that cannot omit
ANY of its n+1 coordinates. No exact parity NAND complexity is assumed.
The construction selects a phase and the first gate of an optimal circuit;
no efficient selector or total-MCSP hardness conclusion is claimed.
-/

namespace OptimalSupport

open FirstGateExtension

def flipAt : List Bool → Nat → List Bool
  | [], _ => []
  | b :: bs, 0 => (!b) :: bs
  | b :: bs, i+1 => b :: flipAt bs i

theorem flipAt_length (a : List Bool) (i : Nat) :
    (flipAt a i).length = a.length := by
  induction a generalizing i with
  | nil => rfl
  | cons b bs ih => cases i <;> simp [flipAt, ih]

theorem sel_flipAt_self (a : List Bool) (i : Nat) (hi : i < a.length) :
    selBool (flipAt a i) i = !(selBool a i) := by
  induction a generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simp at hi; omega)

theorem sel_flipAt_other (a : List Bool) (i j : Nat) (hne : j ≠ i) :
    selBool (flipAt a i) j = selBool a j := by
  induction a generalizing i j with
  | nil => rfl
  | cons b bs ih =>
      cases i with
      | zero => cases j with
        | zero => exact False.elim (hne rfl)
        | succ j => rfl
      | succ i => cases j with
        | zero => rfl
        | succ j => exact ih i j (by omega)

theorem parity_flipAt (a : List Bool) (i : Nat) (hi : i < a.length) :
    ParityTeaching.parity (flipAt a i) = !(ParityTeaching.parity a) := by
  induction a generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          cases b <;> cases h : ParityTeaching.parity bs <;>
            simp [flipAt, ParityTeaching.parity, h]
      | succ i =>
          have h := ih i (by simp at hi; omega)
          simp only [flipAt, ParityTeaching.parity, h]
          cases b <;> cases ParityTeaching.parity bs <;> rfl

def phase (b : Bool) (a : List Bool) : Bool := ParityTeaching.parity a ^^ b

theorem phase_flipAt (b : Bool) (a : List Bool) (i : Nat) (hi : i < a.length) :
    phase b (flipAt a i) = phase (!b) a := by
  simp only [phase, parity_flipAt a i hi]
  cases b <;> cases ParityTeaching.parity a <;> rfl

theorem phase_flipAt_ne (b : Bool) (a : List Bool) (i : Nat) (hi : i < a.length) :
    phase b a ≠ phase b (flipAt a i) := by
  rw [phase_flipAt b a i hi]
  cases b <;> cases h : ParityTeaching.parity a <;> simp [phase, h]

theorem phase_function_essential (n i : Nat) (b : Bool) (hi : i < n) :
    FunctionEssentialAt n (phase b) i := by
  let u := List.replicate n false
  refine ⟨u, flipAt u i, by simp [u], ?_, ?_, ?_⟩
  · simp [flipAt_length, u]
  · intro j _ hne
    exact (sel_flipAt_other u i j hne).symm
  · exact phase_flipAt_ne b u i (by simpa [u] using hi)

theorem phase_no_zero_circuit (n : Nat) (hn : 2 ≤ n) (b : Bool) :
    ¬ MCSPScope.HasCircuit n (phase b) 0 := by
  rintro ⟨gates,out,hwf,hcost,hcomp⟩
  have h := DependencyBound.essential_inputs_le_budget_add_one n 0 gates out
    hwf hcost (fun i hi =>
      computes_transfers_essential hcomp (phase_function_essential n i b hi))
  omega

/-- Elementary least-witness principle, proved by bounded induction. -/
theorem exists_least_nat (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ C, P C ∧ ∀ k, P k → C ≤ k := by
  classical
  have aux : ∀ K, (∃ k, k ≤ K ∧ P k) →
      ∃ C, C ≤ K ∧ P C ∧ ∀ k, k < C → ¬ P k := by
    intro K
    induction K with
    | zero =>
        rintro ⟨k,hk,hp⟩
        have he : k = 0 := by omega
        subst k
        exact ⟨0, by omega, hp, by intro k hk; omega⟩
    | succ K ih =>
        intro h
        by_cases hsmall : ∃ k, k ≤ K ∧ P k
        · obtain ⟨C,hC,hp,hmin⟩ := ih hsmall
          exact ⟨C, by omega, hp, hmin⟩
        · obtain ⟨k,hk,hp⟩ := h
          have he : k = K+1 := by
            apply Classical.byContradiction
            intro hne
            exact hsmall ⟨k, by omega, hp⟩
          subst k
          refine ⟨K+1, by omega, hp, ?_⟩
          intro k hk hp
          exact hsmall ⟨k, by omega, hp⟩
  obtain ⟨K,hK⟩ := hex
  obtain ⟨C,_,hp,hmin⟩ := aux K ⟨K, by omega, hK⟩
  refine ⟨C,hp,?_⟩
  intro k hk
  apply Classical.byContradiction
  intro h
  exact hmin k (by omega) hk

def CheapestPhase (n : Nat) (b : Bool) (C : Nat) : Prop :=
  MCSPScope.HasCircuit n (phase b) C ∧
  ∀ b' k, MCSPScope.HasCircuit n (phase b') k → C ≤ k

theorem exists_cheapest_phase (n : Nat) (hn : 0 < n) :
    ∃ b C, CheapestPhase n b C ∧ C ≤ MCSPScope.circuitBound n := by
  obtain ⟨C,⟨b,hb⟩,hmin⟩ := exists_least_nat
    (fun k => ∃ b : Bool, MCSPScope.HasCircuit n (phase b) k)
    ⟨MCSPScope.circuitBound n, false,
      MCSPScope.universal_circuit_bound n (phase false) hn⟩
  refine ⟨b,C,⟨hb,?_⟩,?_⟩
  · intro b' k hk
    exact hmin k ⟨b',hk⟩
  · exact hmin _ ⟨false, MCSPScope.universal_circuit_bound n (phase false) hn⟩

theorem hasCircuit_congr {n s : Nat} {f g : List Bool → Bool}
    (heq : ∀ a, a.length = n → f a = g a)
    (h : MCSPScope.HasCircuit n f s) : MCSPScope.HasCircuit n g s := by
  obtain ⟨gates,out,hwf,hcost,hcomp⟩ := h
  exact ⟨gates,out,hwf,hcost, fun a ha => (hcomp a ha).trans (heq a ha)⟩

theorem circuit_has_own_function (m s : Nat) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN m gates out) (hcost : gates.length ≤ s) :
    MCSPScope.HasCircuit m (circuitFunction gates out) s :=
  ⟨gates,out,hwf,hcost,fun _ _ => rfl⟩

theorem eval_eq_of_not_essential {m k : Nat} {gates : List (Nat × Nat)} {out : Nat}
    (hnot : ¬ DependencyBound.EssentialAt m gates out k)
    (u v : List Bool) (hu : u.length = m) (hv : v.length = m)
    (hother : ∀ j, j < m → j ≠ k → selBool u j = selBool v j) :
    circuitFunction gates out u = circuitFunction gates out v := by
  classical
  apply Classical.byContradiction
  intro hne
  exact hnot ⟨u,v,hu,hv,hother,hne⟩

theorem zero_sel (n i : Nat) (hi : i < n) :
    selBool (List.replicate n false) i = false := by
  rw [← ParityTeaching.bit_eq_selBool]
  exact ParityTeaching.bit_replicate false n i hi


theorem rewire_append_projection (n r e : Nat) (hr : r < n)
    (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN (n+1) gates out) (hcost : gates.length ≤ e) :
    MCSPScope.HasCircuit n
      (fun a => circuitFunction gates out (a ++ [selBool a r])) e := by
  have hrho : ∀ k, k < n+1 → (if k<n then k else r) < n := by
    intro k _
    by_cases h : k < n
    · simpa only [ite_eq_left h] using h
    · simpa only [ite_eq_right h] using hr
  have h := CircuitRewiring.hasCircuit_rewire (n+1) n
    (fun k => if k<n then k else r) hrho (circuitFunction gates out) e
    (circuit_has_own_function (n+1) e gates out hwf hcost)
  apply hasCircuit_congr _ h
  intro a ha
  rw [CircuitRewiring.sourceInput_append_projection n r a ha]

theorem unused_extra_implies_original_circuit (n e i j : Nat) (hn : 0 < n)
    (f : List Bool → Bool) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN (n+1) gates out) (hcost : gates.length ≤ e)
    (hgraph : GraphComputes n f i j gates out)
    (hnot : ¬ DependencyBound.EssentialAt (n+1) gates out n) :
    MCSPScope.HasCircuit n f e := by
  apply hasCircuit_congr _ (rewire_append_projection n 0 e hn gates out hwf hcost)
  intro a ha
  calc
    circuitFunction gates out (a ++ [selBool a 0]) =
        circuitFunction gates out (graphInput a i j) := by
      apply eval_eq_of_not_essential hnot
      · simp [ha]
      · simp [graphInput_length, ha]
      · intro k hk hne
        have hka : k < a.length := by omega
        change selBool (a ++ [selBool a 0]) k =
          selBool (a ++ [nandBool (selBool a i) (selBool a j)]) k
        rw [selBool_append_of_lt hka, selBool_append_of_lt hka]
    _ = f a := hgraph a ha

theorem graphInput_flip_diagonal (a : List Bool) (i : Nat) (hi : i < a.length) :
    graphInput (flipAt a i) i i = flipAt a i ++ [selBool a i] := by
  simp only [graphInput, sel_flipAt_self a i hi]
  cases selBool a i <;> rfl

theorem unused_diagonal_implies_flipped_circuit (n e i : Nat) (hi : i < n)
    (f : List Bool → Bool) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN (n+1) gates out) (hcost : gates.length ≤ e)
    (hgraph : GraphComputes n f i i gates out)
    (hnot : ¬ DependencyBound.EssentialAt (n+1) gates out i) :
    MCSPScope.HasCircuit n (fun a => f (flipAt a i)) e := by
  apply hasCircuit_congr _ (rewire_append_projection n i e hi gates out hwf hcost)
  intro a ha
  have hai : i < a.length := by omega
  have hfa : (flipAt a i).length = n := by rw [flipAt_length, ha]
  calc
    circuitFunction gates out (a ++ [selBool a i]) =
        circuitFunction gates out (graphInput (flipAt a i) i i) := by
      rw [graphInput_flip_diagonal a i hai]
      apply eval_eq_of_not_essential hnot
      · simp [ha]
      · simp [hfa]
      · intro k hk hne
        by_cases hkn : k < n
        · have hka : k < a.length := by omega
          have hkfa : k < (flipAt a i).length := by omega
          rw [selBool_append_of_lt hka, selBool_append_of_lt hkfa]
          exact (sel_flipAt_other a i k hne).symm
        · have heq : k = n := by omega
          subst k
          rw [selBool_append_singleton, selBool_append_singleton]
          simp [ha, hfa]
    _ = f (flipAt a i) := hgraph (flipAt a i) hfa

theorem original_coordinate_essential (n i j k : Nat) (b : Bool)
    (hi : i < n) (hj : j < n) (hk : k < n)
    (hdiag : ¬ (i = k ∧ j = k))
    (gates : List (Nat × Nat)) (out : Nat)
    (hgraph : GraphComputes n (phase b) i j gates out) :
    DependencyBound.EssentialAt (n+1) gates out k := by
  let u := List.replicate n false
  let v := flipAt u k
  have hu : u.length = n := by simp [u]
  have hv : v.length = n := by simp [v, flipAt_length, hu]
  have hgateu : nandBool (selBool u i) (selBool u j) = true := by
    simp [u, zero_sel n i hi, zero_sel n j hj, nandBool]
  have hgatev : nandBool (selBool v i) (selBool v j) = true := by
    have hne : i ≠ k ∨ j ≠ k := by
      by_cases h : i = k
      · exact Or.inr (by intro h'; exact hdiag ⟨h,h'⟩)
      · exact Or.inl h
    rcases hne with hne | hne
    · change nandBool (selBool (flipAt u k) i) (selBool (flipAt u k) j) = true
      rw [sel_flipAt_other u k i hne]
      have hzero : selBool u i = false := zero_sel n i hi
      rw [hzero]
      simp [nandBool]
    · change nandBool (selBool (flipAt u k) i) (selBool (flipAt u k) j) = true
      rw [sel_flipAt_other u k j hne]
      have hzero : selBool u j = false := zero_sel n j hj
      rw [hzero]
      simp [nandBool]
  refine ⟨graphInput u i j, graphInput v i j,
    by simp [graphInput_length, hu], by simp [graphInput_length, hv], ?_, ?_⟩
  · intro t ht hne
    by_cases htn : t < n
    · have htu : t < u.length := by omega
      have htv : t < v.length := by omega
      change selBool (u ++ [nandBool (selBool u i) (selBool u j)]) t =
        selBool (v ++ [nandBool (selBool v i) (selBool v j)]) t
      rw [selBool_append_of_lt htu, selBool_append_of_lt htv]
      exact (sel_flipAt_other u k t hne).symm
    · have heq : t = n := by omega
      subst t
      simp only [graphInput, selBool_append_singleton, hu, hv, hgateu, hgatev]
      simp
  · change circuitFunction gates out (graphInput u i j) ≠
      circuitFunction gates out (graphInput v i j)
    rw [hgraph u hu, hgraph v hv]
    exact phase_flipAt_ne b u k (by omega)

/-- Any residual circuit cheaper than BOTH parity phases must use every
extra coordinate, including a diagonal first gate's original input. -/
theorem every_residual_coordinate_essential (n C e i j : Nat) (hn : 0 < n)
    (b : Bool) (hi : i < n) (hj : j < n)
    (hmin : ∀ b' k, MCSPScope.HasCircuit n (phase b') k → C ≤ k)
    (he : e < C) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN (n+1) gates out) (hcost : gates.length ≤ e)
    (hgraph : GraphComputes n (phase b) i j gates out) :
    ∀ k, k < n+1 → DependencyBound.EssentialAt (n+1) gates out k := by
  intro k hk
  by_cases hkn : k < n
  · by_cases hdiag : i = k ∧ j = k
    · have hgraph' : GraphComputes n (phase b) k k gates out := by
        simpa only [hdiag.1, hdiag.2] using hgraph
      apply Classical.byContradiction
      intro hnot
      have h := unused_diagonal_implies_flipped_circuit n e k hkn
        (phase b) gates out hwf hcost hgraph' hnot
      have hop : MCSPScope.HasCircuit n (phase (!b)) e := by
        apply hasCircuit_congr _ h
        intro a ha
        exact phase_flipAt b a k (by omega)
      have hbad := hmin (!b) e hop
      omega
    · exact original_coordinate_essential n i j k b hi hj hkn hdiag
        gates out hgraph
  · have heq : k = n := by omega
    subst k
    apply Classical.byContradiction
    intro hnot
    have h := unused_extra_implies_original_circuit n e i j hn (phase b)
      gates out hwf hcost hgraph hnot
    have hbad := hmin b e h
    omega

/-- TOTAL-function coordinate support on all valid m-bit rows. This is not
merely constancy of labels on the observed NAND graph. -/
def CoordinateSupport (m : Nat) (g : List Bool → Bool) (S : List Nat) : Prop :=
  (∀ k ∈ S, k < m) ∧
  ∀ u v : List Bool, u.length = m → v.length = m →
    (∀ k ∈ S, selBool u k = selBool v k) → g u = g v

theorem essential_coordinate_in_support (m k : Nat)
    (gates : List (Nat × Nat)) (out : Nat)
    (he : DependencyBound.EssentialAt m gates out k)
    (S : List Nat) (hs : CoordinateSupport m (circuitFunction gates out) S) :
    k ∈ S := by
  apply Classical.byContradiction
  intro hnot
  obtain ⟨u,v,hu,hv,hother,hne⟩ := he
  apply hne
  apply hs.2 u v hu hv
  intro t ht
  have htk : t ≠ k := by intro heq; subst t; exact hnot ht
  exact hother t (hs.1 t ht) htk

def HasResidual (n : Nat) (f : List Bool → Bool) (i j e : Nat) : Prop :=
  ∃ (gates : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN (n+1) gates out ∧ gates.length ≤ e ∧
    GraphComputes n f i j gates out

def LeastResidual (n : Nat) (f : List Bool → Bool) (i j e : Nat) : Prop :=
  HasResidual n f i j e ∧ ∀ k, HasResidual n f i j k → e ≤ k

theorem residual_budget_lower_bound (n C i j : Nat) (b : Bool)
    (hi : i < n) (hj : j < n)
    (hmin : ∀ b' k, MCSPScope.HasCircuit n (phase b') k → C ≤ k)
    (e : Nat) (hr : HasResidual n (phase b) i j e) : C-1 ≤ e := by
  obtain ⟨gates,out,hwf,hcost,hgraph⟩ := hr
  have hc : MCSPScope.HasCircuit n (phase b) (e+1) := by
    refine ⟨(i,j)::gates, out, prefix_first_gate n i j gates out hi hj hwf, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro a ha
      exact hgraph a ha
  have h := hmin b (e+1) hc
  omega

/-- A selected cheaper parity phase and an optimal circuit's first gate.
The retained support is support of the TOTAL extension function. -/
structure OptimalSupportWitness (n : Nat) where
  phaseBit : Bool
  budget : Nat
  left : Nat
  right : Nat
  budget_positive : 0 < budget
  budget_cap : budget ≤ MCSPScope.circuitBound n
  cheapest : CheapestPhase n phaseBit budget
  left_lt : left < n
  right_lt : right < n
  residual_minimum : LeastResidual n (phase phaseBit) left right (budget-1)
  every_residual_essential :
    ∀ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN (n+1) gates out → gates.length ≤ budget-1 →
      GraphComputes n (phase phaseBit) left right gates out →
      ∀ k, k < n+1 → DependencyBound.EssentialAt (n+1) gates out k
  every_support_full :
    ∀ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN (n+1) gates out → gates.length ≤ budget-1 →
      GraphComputes n (phase phaseBit) left right gates out →
      ∀ S : List Nat, CoordinateSupport (n+1) (circuitFunction gates out) S →
      ∀ k, k < n+1 → k ∈ S
  missing_nodup : (GraphHoles.missingRows n left right).Nodup
  missing_count : (GraphHoles.missingRows n left right).length = 2^n
  missing_exact : ∀ a : List Bool,
    a ∈ GraphHoles.missingRows n left right ↔
      a ∈ MCSPScope.allAssignments (n+1) ∧ a ∉ GraphHoles.graphRows n left right

/-- For every n>=2, some cheaper parity phase and an optimal first NAND
have residual minimum C-1, and every extension at that budget has full
TOTAL semantic support. Its full-coordinate graph has exactly 2^n holes. -/
theorem exists_optimal_full_support (n : Nat) (hn : 2 ≤ n) :
    Nonempty (OptimalSupportWitness n) := by
  have hn0 : 0 < n := by omega
  obtain ⟨b,C,hcheap,hcap⟩ := exists_cheapest_phase n hn0
  have hpos : 0 < C := by
    apply Classical.byContradiction
    intro h
    have heq : C = 0 := by omega
    exact phase_no_zero_circuit n hn b (by simpa only [heq] using hcheap.1)
  obtain ⟨gates,out,hwf,hcost,hcomp⟩ := hcheap.1
  have hcost_exact : gates.length = C := by
    have hc : MCSPScope.HasCircuit n (phase b) gates.length :=
      ⟨gates,out,hwf,Nat.le_refl _,hcomp⟩
    have hmin := hcheap.2 b gates.length hc
    omega
  cases gates with
  | nil => simp at hcost_exact; omega
  | cons gate rest =>
      obtain ⟨i,j⟩ := gate
      obtain ⟨hi,hj,hrest⟩ := delete_first_gate n i j rest out hwf
      have hlen : rest.length ≤ C-1 := by
        simp only [List.length_cons] at hcost_exact
        omega
      have hgraph : GraphComputes n (phase b) i j rest out := by
        intro a ha
        exact hcomp a ha
      have hminimum : LeastResidual n (phase b) i j (C-1) :=
        ⟨⟨rest,out,hrest,hlen,hgraph⟩,
          fun e hr => residual_budget_lower_bound n C i j b hi hj hcheap.2 e hr⟩
      have hfull : ∀ (gs : List (Nat × Nat)) (o : Nat),
          WellFormedCircuitN (n+1) gs o → gs.length ≤ C-1 →
          GraphComputes n (phase b) i j gs o →
          ∀ k, k < n+1 → DependencyBound.EssentialAt (n+1) gs o k := by
        intro gs o hw hc hg
        exact every_residual_coordinate_essential n C (C-1) i j hn0 b hi hj
          hcheap.2 (by omega) gs o hw hc hg
      refine ⟨{
        phaseBit := b
        budget := C
        left := i
        right := j
        budget_positive := hpos
        budget_cap := hcap
        cheapest := hcheap
        left_lt := hi
        right_lt := hj
        residual_minimum := hminimum
        every_residual_essential := hfull
        every_support_full := ?_
        missing_nodup := GraphHoles.nodup_missingRows n i j
        missing_count := GraphHoles.length_missingRows n i j
        missing_exact := GraphHoles.missingRows_enumerates_holes n i j
      }⟩
      intro gs o hw hc hg S hs k hk
      exact essential_coordinate_in_support (n+1) k gs o (hfull gs o hw hc hg k hk) S hs

/-- Elementary growth bound used only to make the fixed-linear-cap
refutation itself fully quantified in Lean. -/
theorem square_le_two_pow (n : Nat) (hn : 4 ≤ n) : n*n ≤ 2^n := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases hsmall : n < 4
      · have heq : n = 3 := by omega
        subst n
        decide
      · have hn4 : 4 ≤ n := by omega
        have hp := ih hn4
        have hthree : 3*n ≤ n*n := Nat.mul_le_mul_right n (by omega : 3 ≤ n)
        have hlin : 2*n+1 ≤ n*n := by omega
        have hstep : (n+1)*(n+1) ≤ 2*(n*n) := by
          simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          omega
        calc
          (n+1)*(n+1) ≤ 2*(n*n) := hstep
          _ ≤ 2*(2^n) := Nat.mul_le_mul_left 2 hp
          _ = 2^(n+1) := by rw [Nat.pow_succ]; omega

/-- Every fixed linear hole cap is exceeded by some exact-optimal residual
instance whose TOTAL supporting coordinate sets must all be full. -/
theorem no_universal_linear_hole_cap (c : Nat) :
    ∃ n, 2 ≤ n ∧ ∃ w : OptimalSupportWitness n,
      c*n < (GraphHoles.missingRows n w.left w.right).length := by
  let n := c+4
  have hn : 4 ≤ n := by omega
  obtain ⟨w⟩ := exists_optimal_full_support n (by omega)
  refine ⟨n, by omega, w, ?_⟩
  rw [w.missing_count]
  have hstrict : c*n < n*n :=
    Nat.mul_lt_mul_of_pos_right (by omega : c < n) (by omega : 0 < n)
  exact Nat.lt_of_lt_of_le hstrict (square_le_two_pow n hn)

/-- The obstruction occurs beyond every requested arity threshold, so no
fixed linear cap holds eventually for this exact-optimal-support premise. -/
theorem no_eventual_linear_hole_cap (c n0 : Nat) :
    ∃ n, n0 ≤ n ∧ 2 ≤ n ∧ ∃ w : OptimalSupportWitness n,
      c*n < (GraphHoles.missingRows n w.left w.right).length := by
  let n := c+n0+4
  have hn : 4 ≤ n := by omega
  obtain ⟨w⟩ := exists_optimal_full_support n (by omega)
  refine ⟨n, by omega, by omega, w, ?_⟩
  rw [w.missing_count]
  have hstrict : c*n < n*n :=
    Nat.mul_lt_mul_of_pos_right (by omega : c < n) (by omega : 0 < n)
  exact Nat.lt_of_lt_of_le hstrict (square_le_two_pow n hn)
#print axioms exists_cheapest_phase
#print axioms phase_no_zero_circuit
#print axioms every_residual_coordinate_essential
#print axioms exists_optimal_full_support
#print axioms no_universal_linear_hole_cap
#print axioms no_eventual_linear_hole_cap

end OptimalSupport