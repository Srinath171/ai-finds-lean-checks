import frontier.FirstGateExtension

/-
Input-coordinate substitution for shared topological NAND circuits.
Every gate and the output are reindexed; no gates are added or removed.
-/
namespace CircuitRewiring

/-- Primary inputs follow rho; an old gate wire m+k becomes n+k. -/
def wireMap (m n : Nat) (rho : Nat → Nat) (w : Nat) : Nat :=
  if w < m then rho w else n + (w-m)

def rewireGates (m n : Nat) (rho : Nat → Nat)
    (gates : List (Nat × Nat)) : List (Nat × Nat) :=
  gates.map (fun p => (wireMap m n rho p.1, wireMap m n rho p.2))

def sourceInput (m : Nat) (rho : Nat → Nat) (a : List Bool) : List Bool :=
  (List.range m).map (fun i => selBool a (rho i))

@[simp] theorem rewireGates_length (m n : Nat) (rho : Nat → Nat)
    (gates : List (Nat × Nat)) :
    (rewireGates m n rho gates).length = gates.length := by
  simp [rewireGates]

@[simp] theorem sourceInput_length (m : Nat) (rho : Nat → Nat) (a : List Bool) :
    (sourceInput m rho a).length = m := by simp [sourceInput]

theorem selBool_eq_getElem (a : List Bool) (i : Nat) (hi : i < a.length) :
    selBool a i = a[i] := by
  induction a generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          exact ih i (by simpa using hi)

@[simp] theorem sourceInput_sel (m : Nat) (rho : Nat → Nat) (a : List Bool)
    (i : Nat) (hi : i < m) :
    selBool (sourceInput m rho a) i = selBool a (rho i) := by
  rw [selBool_eq_getElem _ _ (by simpa using hi)]
  simp [sourceInput]

theorem wireMap_lt (m n k : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n) (w : Nat) (hw : w < m+k) :
    wireMap m n rho w < n+k := by
  unfold wireMap
  split
  · have h := hrho w ‹w < m›
    omega
  · omega

@[simp] theorem wireMap_gate (m n k : Nat) (rho : Nat → Nat) :
    wireMap m n rho (m+k) = n+k := by
  simp [wireMap, show ¬ m+k < m by omega]

theorem rewireGates_wf_stage (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n) (gates : List (Nat × Nat)) :
    ∀ k, WellFormedGatesN (m+k) gates →
      WellFormedGatesN (n+k) (rewireGates m n rho gates) := by
  induction gates with
  | nil => intro k _; exact wellFormedGatesN_nil _
  | cons p rest ih =>
      obtain ⟨a,b⟩ := p
      intro k hwf
      obtain ⟨ha,hb,hr⟩ := (DependencyBound.wf_cons_iff (m+k) a b rest).mp hwf
      apply (DependencyBound.wf_cons_iff (n+k)
        (wireMap m n rho a) (wireMap m n rho b)
        (rewireGates m n rho rest)).mpr
      refine ⟨wireMap_lt m n k rho hrho a ha,
        wireMap_lt m n k rho hrho b hb, ?_⟩
      simpa [Nat.add_assoc] using ih (k+1) (by simpa [Nat.add_assoc] using hr)

theorem rewire_wellFormed (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n)
    (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN m gates out) :
    WellFormedCircuitN n (rewireGates m n rho gates) (wireMap m n rho out) := by
  refine ⟨?_, ?_⟩
  · simpa using rewireGates_wf_stage m n rho hrho gates 0 hwf.1
  · simpa using wireMap_lt m n gates.length rho hrho out hwf.2

/-- A selector relation survives appending the same computed signal. -/
theorem append_agrees (m n k : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n)
    (s t : List Bool) (hs : s.length = m+k) (ht : t.length = n+k)
    (hag : ∀ w, w < m+k → selBool t (wireMap m n rho w) = selBool s w)
    (q : Bool) :
    ∀ w, w < m+(k+1) →
      selBool (t++[q]) (wireMap m n rho w) = selBool (s++[q]) w := by
  intro w hw
  by_cases h : w < m+k
  · rw [selBool_append_of_lt (by rw [ht]; exact wireMap_lt m n k rho hrho w h),
        selBool_append_of_lt (by omega : w < s.length)]
    exact hag w h
  · have heq : w = m+k := by omega
    subst w
    rw [wireMap_gate, selBool_append_singleton, selBool_append_singleton]
    simp [hs,ht]

/-- Simulation invariant at any number k of already computed gates. -/
theorem run_rewire_agrees (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n) (gates : List (Nat × Nat)) :
    ∀ (k : Nat) (s t : List Bool),
      s.length = m+k → t.length = n+k →
      (∀ w, w < m+k → selBool t (wireMap m n rho w) = selBool s w) →
      WellFormedGatesN (m+k) gates →
      ∀ out, out < (m+k)+gates.length →
        selBool (runGatesBool t (rewireGates m n rho gates)) (wireMap m n rho out) =
        selBool (runGatesBool s gates) out := by
  induction gates with
  | nil =>
      intro k s t hs ht hag _ out hout
      exact hag out (by simpa using hout)
  | cons p rest ih =>
      obtain ⟨a,b⟩ := p
      intro k s t hs ht hag hwf out hout
      obtain ⟨ha,hb,hr⟩ := (DependencyBound.wf_cons_iff (m+k) a b rest).mp hwf
      have hq : nandBool (selBool t (wireMap m n rho a))
          (selBool t (wireMap m n rho b)) =
          nandBool (selBool s a) (selBool s b) := by
        rw [hag a ha, hag b hb]
      simp only [rewireGates, List.map_cons, runGatesBool]
      rw [hq]
      apply ih (k+1)
        (s++[nandBool (selBool s a) (selBool s b)])
        (t++[nandBool (selBool s a) (selBool s b)])
      · simp [hs,Nat.add_assoc]
      · simp [ht,Nat.add_assoc]
      · exact append_agrees m n k rho hrho s t hs ht hag _
      · simpa [Nat.add_assoc] using hr
      · simp only [List.length_cons] at hout
        omega

/-- Exact pointwise semantics, with zero-cost primary-input substitution. -/
theorem rewire_eval (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n)
    (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN m gates out)
    (a : List Bool) (ha : a.length = n) :
    selBool (runGatesBool a (rewireGates m n rho gates)) (wireMap m n rho out) =
      selBool (runGatesBool (sourceInput m rho a) gates) out := by
  apply run_rewire_agrees m n rho hrho gates 0 (sourceInput m rho a) a
  · simp
  · simpa using ha
  · intro w hw
    have hw' : w < m := by simpa using hw
    simp [wireMap, hw', sourceInput_sel m rho a w hw']
  · simpa using hwf.1
  · simpa using hwf.2

/-- Transport a circuit computing f under a coordinate substitution. -/
theorem computes_rewire (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n)
    (f : List Bool → Bool) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN m gates out)
    (hc : MCSPScope.Computes m f gates out) :
    MCSPScope.Computes n (fun a => f (sourceInput m rho a))
      (rewireGates m n rho gates) (wireMap m n rho out) := by
  intro a ha
  rw [rewire_eval m n rho hrho gates out hwf a ha]
  exact hc _ (sourceInput_length m rho a)

/-- Circuit-existence transport, with the identical paid-gate budget. -/
theorem hasCircuit_rewire (m n : Nat) (rho : Nat → Nat)
    (hrho : ∀ i, i < m → rho i < n)
    (f : List Bool → Bool) (budget : Nat)
    (h : MCSPScope.HasCircuit m f budget) :
    MCSPScope.HasCircuit n (fun a => f (sourceInput m rho a)) budget := by
  obtain ⟨gates,out,hwf,hcost,hc⟩ := h
  exact ⟨rewireGates m n rho gates, wireMap m n rho out,
    rewire_wellFormed m n rho hrho gates out hwf,
    by simpa using hcost,
    computes_rewire m n rho hrho f gates out hwf hc⟩


/-- Equal-length Boolean lists are determined by their valid selectors. -/
theorem list_eq_of_selBool_eq (a b : List Bool) (hlen : a.length = b.length)
    (hag : ∀ i, i < a.length → selBool a i = selBool b i) : a = b := by
  induction a generalizing b with
  | nil =>
      cases b with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons x xs ih =>
      cases b with
      | nil => simp at hlen
      | cons y ys =>
          have hxy : x = y := hag 0 (by simp)
          have htail : xs = ys := by
            apply ih ys (by simpa using hlen)
            intro i hi
            exact hag (i+1) (by simp only [List.length_cons]; omega)
          rw [hxy,htail]

/-- Keep all n original inputs and replace only the extra input by a_r. -/
theorem sourceInput_append_projection (n r : Nat) (a : List Bool)
    (ha : a.length = n) :
    sourceInput (n+1) (fun k => if k<n then k else r) a =
      a ++ [selBool a r] := by
  apply list_eq_of_selBool_eq
  · simp [ha]
  · intro i hi
    have hi' : i < n+1 := by simpa using hi
    rw [sourceInput_sel (n+1) _ a i hi']
    by_cases h : i<n
    · rw [ite_eq_left h]
      exact (selBool_append_of_lt (by omega : i < a.length)).symm
    · have heq : i=n := by omega
      subst i
      rw [ite_eq_right (by omega : ¬ n<n), selBool_append_singleton]
      simp [ha]

#print axioms rewire_wellFormed
#print axioms rewire_eval
#print axioms hasCircuit_rewire
#print axioms sourceInput_append_projection

end CircuitRewiring
