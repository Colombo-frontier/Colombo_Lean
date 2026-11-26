import MinimaxAudit.Frame
import MinimaxAudit.PairedCoordinates

/-!
# Paired deterministic resisting frames

This module adapts the finite orthonormal completion induction from the
reference audit's `Pilot/DeterministicLower.lean` (frozen commit recorded in
`reference/vendor_provenance.json`) to actual complete scalar jets and two
independent primal/dual frames. The scalar construction and policy execution
below are new to this audit; no theorem of the general monotone operator
lower bound is substituted for a scalar theorem.
-/

open Set
open scoped RealInnerProductSpace
namespace MinimaxAudit.Deterministic

noncomputable section

section Completion
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_unit_orthogonal_fin {k : ℕ} (u : Fin k → E)
    (hk : k < Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧ ∀ i, inner ℝ w (u i) = 0 := by
  obtain ⟨w, hw, ho⟩ := Frame.exists_unit_orthogonal_list (List.ofFn u) (by simpa using hk)
  exact ⟨w, hw, fun i => ho (u i) (by simp)⟩

theorem exists_unit_orthogonal_two_fin {r s : ℕ} (a : Fin r → E) (b : Fin s → E)
    (hrs : r + s < Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧
      (∀ i, inner ℝ w (a i) = 0) ∧ (∀ j, inner ℝ w (b j) = 0) := by
  obtain ⟨w, hw, horth⟩ := exists_unit_orthogonal_fin (Fin.append a b) hrs
  refine ⟨w, hw, ?_, ?_⟩
  · intro i
    simpa using horth (Fin.castAdd s i)
  · intro j
    simpa using horth (Fin.natAdd r j)

omit [FiniteDimensional ℝ E] in
theorem orthonormal_fin_snoc {k : ℕ} (u : Fin k → E) (w : E)
    (hu : Orthonormal ℝ u) (hw : ‖w‖ = 1)
    (hwu : ∀ i, inner ℝ w (u i) = 0) :
    Orthonormal ℝ (Fin.append u (fun _ : Fin 1 => w)) := by
  constructor
  · intro i
    refine Fin.addCases (fun i' => ?_) (fun _ => ?_) i
    · simpa using hu.1 i'
    · simpa using hw
  · intro i j
    revert j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      intro j <;> revert j <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_)
    · intro hij
      simpa using hu.2 (fun h => hij (congrArg (Fin.castAdd 1) h))
    · intro _hij
      simpa [real_inner_comm] using hwu i'
    · intro _hij
      simpa using hwu j'
    · have hij' : i' = j' := Subsingleton.elim _ _
      intro hij
      exact (hij (by subst j'; rfl)).elim

/-- Extend an orthonormal prefix to a prescribed finite length.  Every new
vector avoids the fixed query history, and the final vector also avoids the
terminal output.  The extra factor two in the ambient dimension is exactly
the resisting-oracle dimension count. -/
theorem exists_orthonormal_completion_avoiding
    (N k t : ℕ) (hkN : k ≤ N) (htk : t ≤ k)
    (u : Fin k → E) (z : Fin t → E) (y : E)
    (hu : Orthonormal ℝ u)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E) :
    ∃ v : Fin (N + 1) → E,
      Orthonormal ℝ v ∧
      (∀ i : Fin k, v (Fin.castLE (by omega) i) = u i) ∧
      (∀ i : Fin (N + 1), k ≤ i.1 → ∀ j : Fin t,
        inner ℝ (v i) (z j) = 0) ∧
      inner ℝ (v (Fin.last N)) y = 0 := by
  induction hgap : N - k using Nat.strong_induction_on generalizing k u with
  | h gap ih =>
      by_cases hk : k = N
      · subst k
        let zy : Fin (t + 1) → E := Fin.append z (fun _ : Fin 1 => y)
        have hcount : N + (t + 1) < Module.finrank ℝ E := by omega
        obtain ⟨w, hw, hwu, hwzy⟩ :=
          exists_unit_orthogonal_two_fin u zy hcount
        let v : Fin (N + 1) → E := Fin.append u (fun _ : Fin 1 => w)
        have hv : Orthonormal ℝ v := orthonormal_fin_snoc u w hu hw hwu
        refine ⟨v, hv, ?_, ?_, ?_⟩
        · intro i
          exact Fin.append_left _ _ i
        · intro i hi j
          have hval : i.1 = N := Nat.le_antisymm (Nat.le_of_lt_succ i.2) hi
          have hilast : i = Fin.last N := Fin.ext hval
          rw [hilast]
          have hwz : inner ℝ w (z j) = 0 := by
            have := hwzy (Fin.castAdd 1 j)
            simpa [zy] using this
          have vlast : v (Fin.last N) = w := by
            change Fin.append u (fun _ : Fin 1 => w) (Fin.last N) = w
            rw [show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext rfl,
              Fin.append_right]
          rw [vlast]
          exact hwz
        · have hwy : inner ℝ w y = 0 := by
            have := hwzy (Fin.natAdd t (0 : Fin 1))
            simpa [zy] using this
          have vlast : v (Fin.last N) = w := by
            change Fin.append u (fun _ : Fin 1 => w) (Fin.last N) = w
            rw [show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext rfl,
              Fin.append_right]
          rw [vlast]
          exact hwy
      · have hklt : k < N := lt_of_le_of_ne hkN hk
        have hcount : k + t < Module.finrank ℝ E := by omega
        obtain ⟨w, hw, hwu, hwz⟩ :=
          exists_unit_orthogonal_two_fin u z hcount
        let u' : Fin (k + 1) → E := Fin.append u (fun _ : Fin 1 => w)
        have hu' : Orthonormal ℝ u' := orthonormal_fin_snoc u w hu hw hwu
        have hgaplt : N - (k + 1) < gap := by omega
        obtain ⟨v, hv, hvu', hvz, hvy⟩ :=
          ih (N - (k + 1)) hgaplt (k + 1) (by omega) (by omega) u' hu' rfl
        refine ⟨v, hv, ?_, ?_, hvy⟩
        · intro i
          have hleft := Fin.append_left u (fun _ : Fin 1 => w) i
          rw [← hleft]
          exact hvu' (Fin.castAdd 1 i)
        · intro i hik j
          by_cases hieq : i.1 = k
          · have hi : i = Fin.castLE (by omega) (Fin.last k) :=
              Fin.ext (by simpa using hieq)
            have hwzj := hwz j
            let ilast : Fin (k + 1) := Fin.natAdd k (0 : Fin 1)
            have hlast : Fin.last k = ilast := Fin.ext rfl
            rw [hi, hlast, hvu' ilast]
            change inner ℝ (u' ilast) (z j) = 0
            rw [show u' ilast = w from
              Fin.append_right u (fun _ : Fin 1 => w) (0 : Fin 1)]
            exact hwzj
          · exact hvz i (by omega) j


/-- List form of completion, used for the actual query-answer history. -/
theorem completion_avoiding_list (N k : ℕ) (hkN : k ≤ N)
    (u : Fin k → E) (queries : List E) (y : E)
    (hu : Orthonormal ℝ u) (hq : queries.length ≤ k)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E) :
    ∃ v : Fin (N + 1) → E, Orthonormal ℝ v ∧
      (∀ i : Fin k, v (Fin.castLE (by omega) i) = u i) ∧
      (∀ i : Fin (N + 1), k ≤ i.1 → ∀ q ∈ queries, inner ℝ (v i) q = 0) ∧
      inner ℝ (v (Fin.last N)) y = 0 := by
  obtain ⟨v, hv, hprefix, hqueries, hout⟩ :=
    exists_orthonormal_completion_avoiding N k queries.length hkN hq u queries.get y hu hdim
  refine ⟨v, hv, hprefix, ?_, hout⟩
  intro i hi q hqmem
  obtain ⟨j, hj⟩ := List.get_of_mem hqmem
  rw [← hj]
  exact hqueries i hi j

end Completion

section ScalarPotential
variable {N dx dy : ℕ}

/-- The concrete a_i coordinate as a continuous linear functional. -/
def plusForm (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (i : Fin (N + 1)) : SaddleSpace dx dy →L[ℝ] ℝ :=
  innerSL ℝ (pairedPlus U V i)

/-- The concrete b_i coordinate as a continuous linear functional. -/
def minusForm (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (i : Fin (N + 1)) : SaddleSpace dx dy →L[ℝ] ℝ :=
  innerSL ℝ (pairedMinus U V i)

def publicQuadratic (z : SaddleSpace dx dy) : ℝ :=
  ‖primalBlock z‖ ^ 2 / 2 - ‖dualBlock z‖ ^ 2 / 2

/-- The manuscript's actual scalar hard potential. -/
def hardPotential (profile : GateProfile) (tau lam c q : ℝ)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy) :
    SaddleSpace dx dy → ℝ :=
  chainPotential profile tau lam c q publicQuadratic (plusForm U V) (minusForm U V)

def revealedLinks (N t : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.1 < t)

def truncatedPotential (profile : GateProfile) (tau lam c q : ℝ) (t : ℕ)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy) :
    SaddleSpace dx dy → ℝ :=
  truncatedChainPotential profile tau lam c q publicQuadratic
    (plusForm U V) (minusForm U V) (revealedLinks N t)

def prefixPad {E : Type*} [Zero E] (N t : ℕ) (_ht : t ≤ N)
    (u : Fin (t + 1) → E) : Fin (N + 1) → E :=
  fun i => if hi : i.1 < t + 1 then u ⟨i.1, hi⟩ else 0

@[simp] theorem prefixPad_prefix {E : Type*} [Zero E] (N t : ℕ) (ht : t ≤ N)
    (u : Fin (t + 1) → E) (i : Fin (t + 1)) :
    prefixPad N t ht u (Fin.castLE (by omega) i) = u i := by
  simp [prefixPad, i.2]

theorem plusForm_eq_zero
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (i : Fin (N + 1)) (z : SaddleSpace dx dy)
    (hx : inner ℝ (U i) (primalBlock z) = 0)
    (hy : inner ℝ (V i) (dualBlock z) = 0) : plusForm U V i z = 0 := by
  change inner ℝ (pairedPlus U V i) z = 0
  rw [← join_blocks z, paired_plus_coordinate, hx, hy]
  simp

theorem minusForm_eq_zero
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (i : Fin (N + 1)) (z : SaddleSpace dx dy)
    (hx : inner ℝ (U i) (primalBlock z) = 0)
    (hy : inner ℝ (V i) (dualBlock z) = 0) : minusForm U V i z = 0 := by
  change inner ℝ (pairedMinus U V i) z = 0
  rw [← join_blocks z, paired_minus_coordinate, hx, hy]
  simp

/-- Every returned order, including value, is hidden by exact orthogonality
of all as-yet-unrevealed primal and dual directions. -/
theorem exactJet_full_eq_truncated_of_future_orthogonal
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (p t : ℕ) (ht : t ≤ N)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (z : SaddleSpace dx dy)
    (hfuture : ∀ i : Fin (N + 1), t ≤ i.1 →
      inner ℝ (U i) (primalBlock z) = 0 ∧ inner ℝ (V i) (dualBlock z) = 0) :
    exactScalarJet p (hardPotential profile tau lam c q U V) z =
      exactScalarJet p (truncatedPotential profile tau lam c q t U V) z := by
  apply chainPotential_exact_jet_eq_truncated profile htau lam c q publicQuadratic
    (plusForm U V) (minusForm U V) (revealedLinks N t)
  · intro i hi
    have hit : t ≤ i.1 := by simpa [revealedLinks] using hi
    rw [plusForm_eq_zero U V i.castSucc z (hfuture i.castSucc hit).1 (hfuture i.castSucc hit).2,
      minusForm_eq_zero U V i.succ z (hfuture i.succ (by simpa only [Fin.val_succ] using Nat.le_succ_of_le hit)).1
        (hfuture i.succ (by simpa only [Fin.val_succ] using Nat.le_succ_of_le hit)).2]
    simp
    linarith
  · rw [plusForm_eq_zero U V (Fin.last N) z
      (hfuture (Fin.last N) ht).1 (hfuture (Fin.last N) ht).2]
    simp
    linarith

/-- The truncated scalar answer inspects only the first t+1 frame pairs. -/
theorem truncatedPotential_congr_prefix
    (profile : GateProfile) (tau lam c q : ℝ) (t : ℕ) (ht : t ≤ N)
    (U U' : Fin (N + 1) → Primal dx) (V V' : Fin (N + 1) → Dual dy)
    (hU : ∀ i : Fin (t + 1), U (Fin.castLE (by omega) i) = U' (Fin.castLE (by omega) i))
    (hV : ∀ i : Fin (t + 1), V (Fin.castLE (by omega) i) = V' (Fin.castLE (by omega) i)) :
    truncatedPotential profile tau lam c q t U V =
      truncatedPotential profile tau lam c q t U' V' := by
  have hUall : ∀ i : Fin (N + 1), i.1 < t + 1 → U i = U' i := by
    intro i hi
    exact hU ⟨i.1, hi⟩
  have hVall : ∀ i : Fin (N + 1), i.1 < t + 1 → V i = V' i := by
    intro i hi
    exact hV ⟨i.1, hi⟩
  have hA : ∀ i : Fin (N + 1), i.1 < t + 1 → plusForm U V i = plusForm U' V' i := by
    intro i hi
    simp only [plusForm, pairedPlus, hUall i hi, hVall i hi]
  have hB : ∀ i : Fin (N + 1), i.1 < t + 1 → minusForm U V i = minusForm U' V' i := by
    intro i hi
    simp only [minusForm, pairedMinus, hUall i hi, hVall i hi]
  funext z
  have hsum :
      (∑ i ∈ revealedLinks N t, scalarGate profile tau (plusForm U V i.castSucc z)
        (minusForm U V i.succ z)) =
      ∑ i ∈ revealedLinks N t, scalarGate profile tau (plusForm U' V' i.castSucc z)
        (minusForm U' V' i.succ z) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hit : i.1 < t := by simpa [revealedLinks] using hi
    rw [hA i.castSucc (by simpa using Nat.lt_succ_of_lt hit), hB i.succ (by simpa using hit)]
  simp only [truncatedPotential, truncatedChainPotential]
  rw [hsum, hB 0 (by simp)]

end ScalarPotential

section Execution
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

/-- Actual execution of the source total-history policy. Every oracle answer
is the complete scalar jet; early stopping saves the policy's arbitrary output. -/
def runScalarPolicy (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy)) :
    ℕ → ScalarHistory p dx dy → SaddleSpace dx dy
  | 0, h => A.output h
  | fuel + 1, h => match A.query h with
    | none => A.output h
    | some z => runScalarPolicy A oracle fuel (h ++ [(z, oracle z)])

/-- The policy's source feasibility guarantee survives its actual execution. -/
theorem runScalarPolicy_feasible (A : DeterministicScalarPolicy p dx dy N X Y)
    (oracle : SaddleSpace dx dy → ScalarJet p (SaddleSpace dx dy))
    (fuel : ℕ) (h : ScalarHistory p dx dy) :
    runScalarPolicy A oracle fuel h ∈ productDomain X Y := by
  induction fuel generalizing h with
  | zero => exact A.feasible_output h
  | succ fuel ih =>
    cases hq : A.query h with
    | none => simpa [runScalarPolicy, hq] using A.feasible_output h
    | some z => simpa [runScalarPolicy, hq] using ih (h ++ [(z, oracle z)])

/-- Online invariant: selected prefixes are preserved, and every still
unselected direction avoids all previously issued queries in its own block. -/
structure FrameExtension (N t : ℕ) (u : Fin t → Primal dx) (v : Fin t → Dual dy)
    (h : ScalarHistory p dx dy)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy) : Prop where
  primal_orthonormal : Orthonormal ℝ U
  dual_orthonormal : Orthonormal ℝ V
  primal_prefix : ∀ (i : Fin (N + 1)) (j : Fin t), i.1 = j.1 → U i = u j
  dual_prefix : ∀ (i : Fin (N + 1)) (j : Fin t), i.1 = j.1 → V i = v j
  future_queries : ∀ i : Fin (N + 1), t ≤ i.1 → ∀ entry ∈ h,
    inner ℝ (U i) (primalBlock entry.1) = 0 ∧
      inner ℝ (V i) (dualBlock entry.1) = 0

def OutputHidden
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (z : SaddleSpace dx dy) : Prop :=
  inner ℝ (U (Fin.last N)) (primalBlock z) = 0 ∧
    inner ℝ (V (Fin.last N)) (dualBlock z) = 0

/-- Complete both actual frames at a stopped history, avoiding its queries
and the arbitrary terminal output in each block. -/
theorem complete_pair_at_output
    (N t : ℕ) (htN : t ≤ N)
    (u : Fin t → Primal dx) (v : Fin t → Dual dy)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (h : ScalarHistory p dx dy) (hlen : h.length ≤ t)
    (z : SaddleSpace dx dy)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy) :
    ∃ U V, FrameExtension N t u v h U V ∧ OutputHidden U V z := by
  let qx := h.map (fun e => primalBlock e.1)
  let qy := h.map (fun e => dualBlock e.1)
  obtain ⟨U, hU, hUprefix, hUqueries, hUout⟩ := completion_avoiding_list
    N t htN u qx (primalBlock z) hu (by simpa [qx] using hlen) (by simpa [Primal] using hdx)
  obtain ⟨V, hV, hVprefix, hVqueries, hVout⟩ := completion_avoiding_list
    N t htN v qy (dualBlock z) hv (by simpa [qy] using hlen) (by simpa [Dual] using hdy)
  refine ⟨U, V, ⟨hU, hV, ?_, ?_, ?_⟩, hUout, hVout⟩
  · intro i j hij
    have heq : Fin.castLE (by omega) j = i := Fin.ext hij.symm
    rw [← heq, hUprefix j]
  · intro i j hij
    have heq : Fin.castLE (by omega) j = i := Fin.ext hij.symm
    rw [← heq, hVprefix j]
  · intro i hi entry he
    exact ⟨hUqueries i hi _ (List.mem_map_of_mem he),
      hVqueries i hi _ (List.mem_map_of_mem he)⟩

end Execution

section OnlineConstruction
variable {p dx dy N : ℕ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

/-- A true online resisting construction for the source total-history scalar
policy. The final frames are constructed here; no resisting-frame certificate
or transcript-equality hypothesis is supplied by the caller. -/
theorem exists_resisting_continuation
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy) :
    ∀ fuel t : ℕ, t + fuel ≤ N →
      ∀ (h : ScalarHistory p dx dy), h.length ≤ t →
      ∀ (u : Fin t → Primal dx) (v : Fin t → Dual dy),
      Orthonormal ℝ u → Orthonormal ℝ v →
      ∃ U V, FrameExtension N t u v h U V ∧
        OutputHidden U V (runScalarPolicy A
          (exactScalarJet p (hardPotential profile tau lam c q U V)) fuel h) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t ht h hlen u v hu hv
    obtain ⟨U, V, hext, hout⟩ := complete_pair_at_output N t (by omega)
      u v hu hv h hlen (A.output h) hdx hdy
    exact ⟨U, V, hext, by simpa [runScalarPolicy] using hout⟩
  | succ fuel ih =>
    intro t ht h hlen u v hu hv
    cases hquery : A.query h with
    | none =>
      obtain ⟨U, V, hext, hout⟩ := complete_pair_at_output N t (by omega)
        u v hu hv h hlen (A.output h) hdx hdy
      exact ⟨U, V, hext, by simpa [runScalarPolicy, hquery] using hout⟩
    | some z =>
      let qx : List (Primal dx) :=
        List.ofFn u ++ (h.map (fun e => primalBlock e.1) ++ [primalBlock z])
      let qy : List (Dual dy) :=
        List.ofFn v ++ (h.map (fun e => dualBlock e.1) ++ [dualBlock z])
      have hcx : qx.length < Module.finrank ℝ (Primal dx) := by
        have hd : 2 * N + 2 ≤ Module.finrank ℝ (Primal dx) := by simpa [Primal] using hdx
        simp only [qx, List.length_append, List.length_ofFn, List.length_map,
          List.length_singleton]
        omega
      have hcy : qy.length < Module.finrank ℝ (Dual dy) := by
        have hd : 2 * N + 2 ≤ Module.finrank ℝ (Dual dy) := by simpa [Dual] using hdy
        simp only [qy, List.length_append, List.length_ofFn, List.length_map,
          List.length_singleton]
        omega
      obtain ⟨wx, hwx, hox⟩ := Frame.exists_unit_orthogonal_list qx hcx
      obtain ⟨wy, hwy, hoy⟩ := Frame.exists_unit_orthogonal_list qy hcy
      have hwxu : ∀ i, inner ℝ wx (u i) = 0 := fun i => hox (u i) (by simp [qx])
      have hwyv : ∀ i, inner ℝ wy (v i) = 0 := fun i => hoy (v i) (by simp [qy])
      have hwxz : inner ℝ wx (primalBlock z) = 0 := hox _ (by simp [qx])
      have hwyz : inner ℝ wy (dualBlock z) = 0 := hoy _ (by simp [qy])
      let u' : Fin (t + 1) → Primal dx := Fin.append u (fun _ : Fin 1 => wx)
      let v' : Fin (t + 1) → Dual dy := Fin.append v (fun _ : Fin 1 => wy)
      have hu' : Orthonormal ℝ u' := orthonormal_fin_snoc u wx hu hwx hwxu
      have hv' : Orthonormal ℝ v' := orthonormal_fin_snoc v wy hv hwy hwyv
      let fakeU := prefixPad N t (by omega) u'
      let fakeV := prefixPad N t (by omega) v'
      let answer := exactScalarJet p (truncatedPotential profile tau lam c q t fakeU fakeV) z
      let h' : ScalarHistory p dx dy := h ++ [(z, answer)]
      have hlen' : h'.length ≤ t + 1 := by
        simp only [h', List.length_append, List.length_singleton]
        omega
      obtain ⟨U, V, hext, hout⟩ := ih (t + 1) (by omega) h' hlen' u' v' hu' hv'
      have hUt : ∀ i : Fin (N + 1), i.1 = t → U i = wx := by
        intro i hi
        rw [hext.primal_prefix i (Fin.last t) (by simpa using hi)]
        change Fin.append u (fun _ : Fin 1 => wx) (Fin.last t) = wx
        rw [show Fin.last t = Fin.natAdd t (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
      have hVt : ∀ i : Fin (N + 1), i.1 = t → V i = wy := by
        intro i hi
        rw [hext.dual_prefix i (Fin.last t) (by simpa using hi)]
        change Fin.append v (fun _ : Fin 1 => wy) (Fin.last t) = wy
        rw [show Fin.last t = Fin.natAdd t (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
      have hcurrent : ∀ i : Fin (N + 1), t ≤ i.1 →
          inner ℝ (U i) (primalBlock z) = 0 ∧ inner ℝ (V i) (dualBlock z) = 0 := by
        intro i hi
        by_cases hieq : i.1 = t
        · rw [hUt i hieq, hVt i hieq]
          exact ⟨hwxz, hwyz⟩
        · exact hext.future_queries i (by omega) (z, answer) (by simp [h'])
      have hfakeU : ∀ i : Fin (t + 1),
          fakeU (Fin.castLE (by omega) i) = U (Fin.castLE (by omega) i) := by
        intro i
        rw [show fakeU (Fin.castLE (by omega) i) = u' i from
          prefixPad_prefix N t (by omega) u' i]
        exact (hext.primal_prefix _ i rfl).symm
      have hfakeV : ∀ i : Fin (t + 1),
          fakeV (Fin.castLE (by omega) i) = V (Fin.castLE (by omega) i) := by
        intro i
        rw [show fakeV (Fin.castLE (by omega) i) = v' i from
          prefixPad_prefix N t (by omega) v' i]
        exact (hext.dual_prefix _ i rfl).symm
      have htrunc := truncatedPotential_congr_prefix profile tau lam c q t (by omega)
        fakeU U fakeV V hfakeU hfakeV
      have hfull := exactJet_full_eq_truncated_of_future_orthogonal
        profile htau lam c q p t (by omega) U V z hcurrent
      have hans : answer = exactScalarJet p (hardPotential profile tau lam c q U V) z := by
        dsimp only [answer]
        rw [htrunc]
        exact hfull.symm
      refine ⟨U, V, ⟨hext.primal_orthonormal, hext.dual_orthonormal, ?_, ?_, ?_⟩, ?_⟩
      · intro i j hij
        have hp := hext.primal_prefix i (Fin.castAdd 1 j) (by simpa using hij)
        simpa [u'] using hp
      · intro i j hij
        have hp := hext.dual_prefix i (Fin.castAdd 1 j) (by simpa using hij)
        simpa [v'] using hp
      · intro i hi entry he
        by_cases hieq : i.1 = t
        · rw [hUt i hieq, hVt i hieq]
          constructor
          · apply hox
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem he))
          · apply hoy
            exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map_of_mem he))
        · exact hext.future_queries i (by omega) entry (List.mem_append_left _ he)
      · simp only [runScalarPolicy, hquery]
        rw [← hans]
        exact hout

/-- Every source deterministic policy with cap N has a single completed pair
of orthonormal frames whose actual complete-scalar-jet execution returns an
arbitrary output orthogonal to the last hidden direction in each block. -/
theorem exists_paired_resisting_frame
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy) :
    ∃ (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy),
      Orthonormal ℝ U ∧ Orthonormal ℝ V ∧
      OutputHidden U V (runScalarPolicy A
        (exactScalarJet p (hardPotential profile tau lam c q U V)) N []) := by
  let u : Fin 0 → Primal dx := fun i => Fin.elim0 i
  let v : Fin 0 → Dual dy := fun i => Fin.elim0 i
  obtain ⟨U, V, hext, hout⟩ := exists_resisting_continuation profile htau lam c q A hdx hdy
    N 0 (by omega) [] (by simp) u v (Orthonormal.of_isEmpty _) (Orthonormal.of_isEmpty _)
  exact ⟨U, V, hext.primal_orthonormal, hext.dual_orthonormal, hout⟩

/-- The paper's displayed final conditions a_n=b_n=0 for the actual policy
output, including outputs that were never queried. -/
theorem exists_paired_resisting_zero_coordinates
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy) :
    ∃ (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy),
      Orthonormal ℝ U ∧ Orthonormal ℝ V ∧
      let output := runScalarPolicy A
        (exactScalarJet p (hardPotential profile tau lam c q U V)) N []
      plusForm U V (Fin.last N) output = 0 ∧ minusForm U V (Fin.last N) output = 0 := by
  obtain ⟨U, V, hU, hV, hout⟩ := exists_paired_resisting_frame profile htau lam c q A hdx hdy
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · exact plusForm_eq_zero U V (Fin.last N) _ hout.1 hout.2
  · exact minusForm_eq_zero U V (Fin.last N) _ hout.1 hout.2

end OnlineConstruction

end
end MinimaxAudit.Deterministic
