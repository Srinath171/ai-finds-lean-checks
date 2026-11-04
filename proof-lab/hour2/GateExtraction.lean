import frontier.CircuitRewiring

/- Arbitrary designated-gate extraction in shared topological NAND DAGs. -/
namespace GateExtraction
open CircuitRewiring FirstGateExtension

/-- Boundary permutation moves the designated gate output to free input n. -/
def boundaryMap (n t w : Nat) : Nat :=
  if w<n then w else if w<n+t then w+1 else n

def extractionMap (n t : Nat) : Nat → Nat :=
  wireMap (n+t+1) (n+t+1) (boundaryMap n t)

def prefixGates (n : Nat) (pre : List (Nat × Nat)) : List (Nat × Nat) :=
  rewireGates n (n+1) id pre

def extractedGates (n : Nat) (pre post : List (Nat × Nat)) : List (Nat × Nat) :=
  prefixGates n pre ++
    rewireGates (n+pre.length+1) (n+pre.length+1) (boundaryMap n pre.length) post

def gateValue (a : List Bool) (pre : List (Nat × Nat)) (u v : Nat) : Bool :=
  nandBool (selBool (runGatesBool a pre) u) (selBool (runGatesBool a pre) v)

theorem boundaryMap_lt (n t w : Nat) (hw : w<n+t+1) : boundaryMap n t w<n+t+1 := by
  unfold boundaryMap
  split <;> rename_i h
  · omega
  · split <;> omega

theorem boundaryMap_before (n t w : Nat) (hw : w<n+t) :
    boundaryMap n t w=wireMap n (n+1) id w := by
  unfold boundaryMap wireMap
  by_cases h : w<n
  · simp only [h,ite_true,id_eq]
  · simp only [h,ite_false,hw,ite_true]
    omega

theorem extractionMap_cases (n t w : Nat) : extractionMap n t w =
    if w<n then w else if w<n+t then w+1 else if w=n+t then n else w := by
  unfold extractionMap wireMap boundaryMap
  by_cases h : w<n+t+1
  · rw [ite_eq_left h]
    by_cases h0 : w<n
    · simp only [h0,ite_true]
    · simp only [h0,ite_false]
      by_cases h1 : w<n+t
      · simp only [h1,ite_true]
      · have heq : w=n+t := by omega
        simp only [heq,ite_true]
  · rw [ite_eq_right h]
    have h0 : ¬ w<n := by omega
    have h1 : ¬ w<n+t := by omega
    have h2 : w≠n+t := by omega
    simp only [h0,h1,h2,ite_false]
    omega

@[simp] theorem prefixGates_length (n : Nat) (pre : List (Nat × Nat)) :
    (prefixGates n pre).length=pre.length := by simp [prefixGates]

@[simp] theorem extractedGates_length (n : Nat) (pre post : List (Nat × Nat)) :
    (extractedGates n pre post).length=pre.length+post.length := by simp [extractedGates]

/-- Exactly one paid gate is removed, including empty prefix/suffix cases. -/
theorem extraction_length_eq_sub_one (n u v : Nat) (pre post : List (Nat × Nat)) :
    (extractedGates n pre post).length=(pre++((u,v)::post)).length-1 := by
  simp only [extractedGates_length,List.length_append,List.length_cons]
  omega

/-- Splitting a well-formed gate block shifts only the available-signal count. -/
theorem wf_append_iff (n : Nat) (pre post : List (Nat × Nat)) :
    WellFormedGatesN n (pre++post) ↔
      WellFormedGatesN n pre ∧ WellFormedGatesN (n+pre.length) post := by
  induction pre generalizing n with
  | nil =>
      constructor
      · intro h; exact ⟨wellFormedGatesN_nil _, by simpa using h⟩
      · intro h; simpa using h.2
  | cons p pre ih =>
      obtain ⟨u,v⟩ := p
      constructor
      · intro h
        obtain ⟨hu,hv,hr⟩ := (DependencyBound.wf_cons_iff n u v (pre++post)).mp h
        obtain ⟨hp,hq⟩ := (ih (n+1)).mp hr
        refine ⟨(DependencyBound.wf_cons_iff n u v pre).mpr ⟨hu,hv,hp⟩,?_⟩
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq
      · intro h
        obtain ⟨hu,hv,hp⟩ := (DependencyBound.wf_cons_iff n u v pre).mp h.1
        apply (DependencyBound.wf_cons_iff n u v (pre++post)).mpr
        refine ⟨hu,hv,(ih (n+1)).mpr ⟨hp,?_⟩⟩
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2

/-- Independent well-formedness survives deletion at an arbitrary position. -/
theorem extraction_wellFormed (n u v : Nat) (pre post : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n (pre++((u,v)::post)) out) :
    WellFormedCircuitN (n+1) (extractedGates n pre post) (extractionMap n pre.length out) := by
  obtain ⟨hp,hrest⟩ := (wf_append_iff n pre ((u,v)::post)).mp hwf.1
  obtain ⟨_,_,hq⟩ := (DependencyBound.wf_cons_iff (n+pre.length) u v post).mp hrest
  have hpre : WellFormedGatesN (n+1) (prefixGates n pre) := by
    simpa [prefixGates] using rewireGates_wf_stage n (n+1) id (by intro i hi; exact Nat.lt_succ_of_lt hi) pre 0 hp
  have hpost : WellFormedCircuitN (n+pre.length+1) post out := by
    refine ⟨hq,?_⟩
    have ho:=hwf.2
    simp only [List.length_append,List.length_cons] at ho
    omega
  have hpost' := rewire_wellFormed (n+pre.length+1) (n+pre.length+1)
    (boundaryMap n pre.length) (boundaryMap_lt n pre.length) post out hpost
  refine ⟨(wf_append_iff (n+1) (prefixGates n pre) _).mpr ⟨hpre,?_⟩,?_⟩
  · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hpost'.1
  · have ho:=hpost'.2
    change extractionMap n pre.length out < (n+1)+(extractedGates n pre post).length
    rw [extractedGates_length]
    change extractionMap n pre.length out < _ at ho
    simp only [rewireGates_length] at ho
    omega

/-- Every original prefix wire keeps its value after the free input is inserted. -/
theorem prefix_agrees (n : Nat) (pre : List (Nat × Nat)) (hp : WellFormedGatesN n pre)
    (a : List Bool) (ha : a.length=n) (z : Bool) (w : Nat) (hw : w<n+pre.length) :
    selBool (runGatesBool (a++[z]) (prefixGates n pre)) (wireMap n (n+1) id w) =
      selBool (runGatesBool a pre) w := by
  apply run_rewire_agrees n (n+1) id (by intro i hi; exact Nat.lt_succ_of_lt hi) pre
    0 a (a++[z])
  · simpa using ha
  · simp [ha]
  · intro i hi
    have hi' : i<n := by omega
    simp only [wireMap,hi',ite_true,id_eq]
    exact selBool_append_of_lt (by omega)
  · simpa using hp
  · simpa using hw

/-- Pointwise extraction semantics for ANY designated gate and ANY output.
The new free input receives that gate's actual original value. -/
theorem extraction_eval (n u v : Nat) (pre post : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n (pre++((u,v)::post)) out)
    (a : List Bool) (ha : a.length=n) :
    circuitFunction (extractedGates n pre post) (extractionMap n pre.length out)
      (a++[gateValue a pre u v]) =
      circuitFunction (pre++((u,v)::post)) out a := by
  obtain ⟨hp,hrest⟩ := (wf_append_iff n pre ((u,v)::post)).mp hwf.1
  obtain ⟨_,_,hq⟩ := (DependencyBound.wf_cons_iff (n+pre.length) u v post).mp hrest
  let s := runGatesBool a pre ++ [gateValue a pre u v]
  let t := runGatesBool (a++[gateValue a pre u v]) (prefixGates n pre)
  have hs : s.length=n+pre.length+1 := by simp [s,runBool_length,ha]
  have ht : t.length=n+pre.length+1 := by simp [t,runBool_length,ha]; omega
  have hag : ∀ w, w<n+pre.length+1 →
      selBool t (extractionMap n pre.length w)=selBool s w := by
    intro w hw
    have hmap : extractionMap n pre.length w=boundaryMap n pre.length w := by
      simp only [extractionMap,wireMap,hw,ite_true]
    rw [hmap]
    by_cases hbefore : w<n+pre.length
    · rw [boundaryMap_before n pre.length w hbefore]
      change selBool (runGatesBool (a++[gateValue a pre u v]) (prefixGates n pre))
        (wireMap n (n+1) id w) = selBool (runGatesBool a pre++[gateValue a pre u v]) w
      rw [selBool_append_of_lt (by rw [runBool_length,ha]; exact hbefore)]
      exact prefix_agrees n pre hp a ha _ w hbefore
    · have heq : w=n+pre.length := by omega
      subst w
      have hboundary : boundaryMap n pre.length (n+pre.length)=n := by
        simp [boundaryMap,show ¬ n+pre.length<n by omega]
      rw [hboundary]
      change selBool (runGatesBool (a++[gateValue a pre u v]) (prefixGates n pre)) n =
        selBool (runGatesBool a pre++[gateValue a pre u v]) (n+pre.length)
      rw [runBool_preserves _ _ (by simp [ha]),selBool_append_singleton,selBool_append_singleton]
      simp [ha,runBool_length]
  have hout : out<(n+pre.length+1)+post.length := by
    have ho:=hwf.2
    simp only [List.length_append,List.length_cons] at ho
    omega
  have hsim := run_rewire_agrees (n+pre.length+1) (n+pre.length+1)
    (boundaryMap n pre.length) (boundaryMap_lt n pre.length) post 0 s t
    (by simpa using hs) (by simpa using ht) (by simpa [extractionMap] using hag)
    (by simpa using hq) out (by simpa using hout)
  change selBool (runGatesBool (a++[gateValue a pre u v])
    (prefixGates n pre++rewireGates (n+pre.length+1) (n+pre.length+1) (boundaryMap n pre.length) post))
    (extractionMap n pre.length out) = _
  rw [runBool_append]
  change selBool (runGatesBool t _) (extractionMap n pre.length out) = _
  change selBool (runGatesBool t (rewireGates (n+pre.length+1) (n+pre.length+1)
    (boundaryMap n pre.length) post)) (extractionMap n pre.length out) =
    selBool (runGatesBool s post) out at hsim
  rw [hsim]
  change selBool (runGatesBool (runGatesBool a pre++[gateValue a pre u v]) post) out = _
  rw [circuitFunction,runBool_append]
  rfl

/-- A supplied semantic name for the designated gate gives the graph theorem. -/
theorem extraction_computes_graph (n u v : Nat) (pre post : List (Nat × Nat)) (out : Nat)
    (f g : List Bool → Bool)
    (hwf : WellFormedCircuitN n (pre++((u,v)::post)) out)
    (hf : MCSPScope.Computes n f (pre++((u,v)::post)) out)
    (hg : ∀ a, a.length=n → gateValue a pre u v=g a) :
    ∀ a, a.length=n →
      circuitFunction (extractedGates n pre post) (extractionMap n pre.length out) (a++[g a])=f a := by
  intro a ha
  rw [←hg a ha,extraction_eval n u v pre post out hwf a ha]
  exact hf a ha


/-! ## Exact finite joint-output versus residual budget shift -/

def inputNand (i j : Nat) (a : List Bool) : Bool :=
  nandBool (selBool a i) (selBool a j)

/-- One shared gate list computes both output functions. -/
def JointBudget (n : Nat) (f g : List Bool → Bool) (S : Nat) : Prop :=
  ∃ (gates : List (Nat × Nat)) (outf outg : Nat),
    WellFormedCircuitN n gates outf ∧ WellFormedCircuitN n gates outg ∧
    gates.length≤S ∧ MCSPScope.Computes n f gates outf ∧ MCSPScope.Computes n g gates outg

def ResidualBudget (n : Nat) (f : List Bool → Bool) (i j e : Nat) : Prop :=
  ∃ (gates : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN (n+1) gates out ∧ gates.length≤e ∧ GraphComputes n f i j gates out

theorem sel_replicate_true (n i : Nat) (hi : i<n) :
    selBool (List.replicate n true) i=true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)

/-- NAND of original inputs is never an input projection: at all ones its
value is false, whereas every original input is true. -/
theorem nand_output_is_gate (n i j : Nat) (hi : i<n) (hj : j<n)
    (gates : List (Nat × Nat)) (outg : Nat)
    (hg : MCSPScope.Computes n (inputNand i j) gates outg) : n≤outg := by
  apply Classical.byContradiction
  intro hnot
  have ho : outg<n := by omega
  have htrue : selBool (runGatesBool (List.replicate n true) gates) outg=true := by
    rw [runBool_preserves _ _ (by simpa using ho)]
    exact sel_replicate_true n outg ho
  have hfalse : inputNand i j (List.replicate n true)=false := by
    simp [inputNand,sel_replicate_true n i hi,sel_replicate_true n j hj,nandBool]
  have h := hg (List.replicate n true) (by simp)
  rw [htrue,hfalse] at h
  cases h

/-- Any valid gate-output signal identifies a designated gate decomposition. -/
theorem gate_signal_decomposition (gates : List (Nat × Nat)) (n out : Nat)
    (hlo : n≤out) (hhi : out<n+gates.length) :
    ∃ (pre : List (Nat × Nat)) (u v : Nat) (post : List (Nat × Nat)),
      gates=pre++((u,v)::post) ∧ out=n+pre.length := by
  induction gates generalizing n with
  | nil => simp at hhi; omega
  | cons p rest ih =>
      obtain ⟨u,v⟩ := p
      by_cases heq : out=n
      · exact ⟨[],u,v,rest,rfl,by simpa using heq⟩
      · obtain ⟨pre,x,y,post,he,ho⟩ := ih (n+1) (by omega)
          (by simp only [List.length_cons] at hhi; omega)
        refine ⟨(u,v)::pre,x,y,post,?_,?_⟩
        · simp only [List.cons_append,he]
        · simp only [List.length_cons]
          omega

/-- Later gates do not change the designated gate's already computed signal. -/
theorem gateValue_eq_signal (n u v : Nat) (pre post : List (Nat × Nat))
    (a : List Bool) (ha : a.length=n) :
    selBool (runGatesBool a (pre++((u,v)::post))) (n+pre.length)=gateValue a pre u v := by
  rw [runBool_append]
  change selBool (runGatesBool (runGatesBool a pre++[gateValue a pre u v]) post)
    (n+pre.length)=gateValue a pre u v
  rw [runBool_preserves _ _ (by simp [runBool_length,ha])]
  rw [selBool_append_singleton]
  simp [runBool_length,ha]

/-- Every joint circuit must pay at least one gate for the NAND output. -/
theorem joint_budget_positive (n i j S : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) (h : JointBudget n f (inputNand i j) S) : 0<S := by
  obtain ⟨gates,outf,outg,_,hwg,hcost,_,hg⟩ := h
  have hgate:=nand_output_is_gate n i j hi hj gates outg hg
  have hb:=hwg.2
  omega

/-- Exact graph-extension budget identity for a fixed original-input NAND.
This allows arbitrary sharing, outputs, gate positions and repeated fanins. -/
theorem joint_budget_iff_residual (n i j e : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) :
    JointBudget n f (inputNand i j) (e+1) ↔ ResidualBudget n f i j e := by
  constructor
  · rintro ⟨gates,outf,outg,hwf,hwg,hcost,hf,hg⟩
    have hlo:=nand_output_is_gate n i j hi hj gates outg hg
    obtain ⟨pre,u,v,post,he,ho⟩ := gate_signal_decomposition gates n outg hlo hwg.2
    subst gates
    have hvalue : ∀ a, a.length=n → gateValue a pre u v=inputNand i j a := by
      intro a ha
      calc
        _ = selBool (runGatesBool a (pre++((u,v)::post))) (n+pre.length) :=
          (gateValue_eq_signal n u v pre post a ha).symm
        _ = selBool (runGatesBool a (pre++((u,v)::post))) outg := by rw [ho]
        _ = inputNand i j a := hg a ha
    refine ⟨extractedGates n pre post,extractionMap n pre.length outf,
      extraction_wellFormed n u v pre post outf hwf,?_,?_⟩
    · rw [extractedGates_length]
      simp only [List.length_append,List.length_cons] at hcost
      omega
    · change ∀ a, a.length=n →
        circuitFunction (extractedGates n pre post) (extractionMap n pre.length outf)
          (a++[inputNand i j a])=f a
      exact extraction_computes_graph n u v pre post outf f (inputNand i j) hwf hf hvalue
  · rintro ⟨gates,out,hwf,hcost,hgraph⟩
    have hprefix:=prefix_first_gate n i j gates out hi hj hwf
    refine ⟨(i,j)::gates,out,n,hprefix,⟨hprefix.1,by simp⟩,
      by simp only [List.length_cons]; omega,?_,?_⟩
    · intro a ha
      exact hgraph a ha
    · intro a ha
      change selBool (runGatesBool (a++[inputNand i j a]) gates) n=inputNand i j a
      rw [runBool_preserves _ _ (by simp [ha]),selBool_append_singleton]
      simp [ha]

/-- Least-budget predicates avoid assumptions about a particular search
algorithm or an efficient selector for an optimal shared circuit. -/
def LeastJoint (n : Nat) (f g : List Bool → Bool) (J : Nat) : Prop :=
  JointBudget n f g J ∧ ∀ S, JointBudget n f g S → J≤S

def LeastResidual (n : Nat) (f : List Bool → Bool) (i j e : Nat) : Prop :=
  ResidualBudget n f i j e ∧ ∀ k, ResidualBudget n f i j k → e≤k

theorem least_residual_gives_least_joint (n i j e : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) (he : LeastResidual n f i j e) :
    LeastJoint n f (inputNand i j) (e+1) := by
  refine ⟨(joint_budget_iff_residual n i j e f hi hj).mpr he.1,?_⟩
  intro S hS
  have hp:=joint_budget_positive n i j S f hi hj hS
  have hS' : JointBudget n f (inputNand i j) ((S-1)+1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤S)] using hS
  have hr:=(joint_budget_iff_residual n i j (S-1) f hi hj).mp hS'
  have hle:=he.2 (S-1) hr
  omega

theorem joint_residual_minimum_identity (n i j J e : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) (hJ : LeastJoint n f (inputNand i j) J)
    (he : LeastResidual n f i j e) : J=e+1 := by
  have heJ:=least_residual_gives_least_joint n i j e f hi hj he
  have h1:=hJ.2 (e+1) heJ.1
  have h2:=heJ.2 J hJ.1
  omega


/-- Append the paid NAND output to any circuit for f. Earlier outputs and
original input values are preserved, including shared intermediate signals. -/
theorem append_nand_joint_budget (n i j S : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) (h : MCSPScope.HasCircuit n f S) :
    JointBudget n f (inputNand i j) (S+1) := by
  obtain ⟨gates,out,hwf,hcost,hf⟩ := h
  have hgs : WellFormedGatesN n (gates++[(i,j)]) :=
    wellFormedGatesN_append_singleton_iff.mpr
      ⟨hwf.1,by omega,by omega⟩
  refine ⟨gates++[(i,j)],out,n+gates.length,⟨hgs,?_⟩,⟨hgs,?_⟩,?_,?_,?_⟩
  · have ho:=hwf.2
    simp only [List.length_append,List.length_singleton]
    omega
  · simp only [List.length_append,List.length_singleton]
    omega
  · simp only [List.length_append,List.length_singleton]
    omega
  · intro a ha
    rw [runBool_append]
    rw [runBool_preserves _ _ (by rw [runBool_length,ha]; exact hwf.2)]
    exact hf a ha
  · intro a ha
    rw [runBool_append]
    have hlen : (runGatesBool a gates).length=n+gates.length := by rw [runBool_length,ha]
    rw [←hlen,selBool_runBool_singleton]
    rw [runBool_preserves a gates (by omega : i<a.length),
      runBool_preserves a gates (by omega : j<a.length)]
    rfl

theorem exists_joint_budget (n i j : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) : ∃ S, JointBudget n f (inputNand i j) S := by
  exact ⟨MCSPScope.circuitBound n+1,append_nand_joint_budget n i j _ f hi hj
    (MCSPScope.universal_circuit_bound n f (by omega))⟩

/-- Least natural witnesses exist whenever the predicate is inhabited. -/
theorem least_nat_exists (P : Nat → Prop) (hex : ∃ k, P k) :
    ∃ C, P C ∧ ∀ k, P k → C≤k := by
  classical
  have aux : ∀ K, (∃ k, k≤K ∧ P k) →
      ∃ C, C≤K ∧ P C ∧ ∀ k, k<C → ¬P k := by
    intro K
    induction K with
    | zero =>
        rintro ⟨k,hk,hp⟩
        have he : k=0 := by omega
        subst k
        exact ⟨0,by omega,hp,by intro k hk; omega⟩
    | succ K ih =>
        intro h
        by_cases hs : ∃ k, k≤K ∧ P k
        · obtain ⟨C,hC,hp,hmin⟩ := ih hs
          exact ⟨C,by omega,hp,hmin⟩
        · obtain ⟨k,hk,hp⟩ := h
          have he : k=K+1 := by
            apply Classical.byContradiction
            intro hne
            exact hs ⟨k,by omega,hp⟩
          subst k
          refine ⟨K+1,by omega,hp,?_⟩
          intro k hk hp
          exact hs ⟨k,by omega,hp⟩
  obtain ⟨K,hK⟩ := hex
  obtain ⟨C,_,hp,hmin⟩ := aux K ⟨K,by omega,hK⟩
  refine ⟨C,hp,?_⟩
  intro k hk
  apply Classical.byContradiction
  intro h
  exact hmin k (by omega) hk

/-- Both least costs are attained for every Boolean target f, and their
exact relationship is J=e+1. No efficient optimization procedure is asserted. -/
theorem exists_joint_residual_minima (n i j : Nat) (f : List Bool → Bool)
    (hi : i<n) (hj : j<n) :
    ∃ J e, LeastJoint n f (inputNand i j) J ∧ LeastResidual n f i j e ∧ J=e+1 := by
  obtain ⟨S,hS⟩ := exists_joint_budget n i j f hi hj
  have hp:=joint_budget_positive n i j S f hi hj hS
  have hS' : JointBudget n f (inputNand i j) ((S-1)+1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1≤S)] using hS
  have hr:=(joint_budget_iff_residual n i j (S-1) f hi hj).mp hS'
  obtain ⟨e,he,hmin⟩ := least_nat_exists (ResidualBudget n f i j) ⟨S-1,hr⟩
  have he' : LeastResidual n f i j e := ⟨he,hmin⟩
  exact ⟨e+1,e,least_residual_gives_least_joint n i j e f hi hj he',he',rfl⟩

#print axioms extraction_wellFormed
#print axioms extraction_eval
#print axioms extraction_computes_graph
#print axioms joint_budget_iff_residual
#print axioms joint_residual_minimum_identity
#print axioms exists_joint_residual_minima

end GateExtraction
