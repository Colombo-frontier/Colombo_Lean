import NCConcave16991.ConditionalHaarConeLocality
import NCConcave16991.ConeProblem

/-!
# Exact locality of the actual cone value-plus-gradient oracle

The reference component retains all completed clocks and all source rows up
through the frontier. Later clocks are radial and later source terms vanish.
Strict correlation margins imply neighborhood equality of the literal
component and this reference function. Thus their full joint gradients agree
by locality of differentiation; no expanded gradient formula is assumed.
-/

open Set Filter
open scoped InnerProductSpace BigOperators Topology

namespace NCConcave16991.Haar

noncomputable section

open ConePrimitives ConeRadial ConeClockGap ConeRecovery ConeValue

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n M : ℕ}

def radialClock (q : ℝ) (u : E) : ℝ :=
  Real.sqrt (1 + ‖u‖ ^ 2) - 1 + ‖u‖ ^ 2 / (2 * q)

def referenceClockGuard (q : ℝ) (frontier : ℕ) (v : Fin (M + 1) → E) (z u : Blocks E M) : ℝ :=
  ∑ j, ((if j.val < frontier then clock q (v j) (z j) (u j) else radialClock q (u j)) +
    ConeRadial.guard 3000 (z j))

def referenceComponent (n : ℕ) (R q : ℝ) (frontier : ℕ)
    (v row : Fin (M + 1) → E) (z u y : Blocks E M) : ℝ :=
  referenceClockGuard q frontier v z u + R⁻¹ * ∑ j,
    if j.val ≤ frontier then previousGate q v (fun j ↦ u j) j *
      ⟪zeta (z j) - Real.sqrt (n : ℝ) • row j, y j⟫_ℝ else 0

def referenceJointComponent (n : ℕ) (R q : ℝ) (frontier : ℕ)
    (v row : Fin (M + 1) → E) (x : JointBlocks E M) : ℝ :=
  referenceComponent n R q frontier v row x.fst.fst x.fst.snd x.snd

def referenceFlatComponent (n : ℕ) (R q : ℝ) (frontier : ℕ)
    (v row : Fin (M + 1) → E)
    (x : JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M)) : ℝ :=
  referenceJointComponent n R q frontier v row ((ConeProblem.jointCoordinates E M).symm x)

/-- Only completed means and source rows through the frontier affect the
reference component. Unknown future parameters can be replaced arbitrarily. -/
theorem referenceComponent_eq_of_known_data (R q : ℝ) (frontier : ℕ)
    (v v' row row' : Fin (M + 1) → E)
    (hv : ∀ j, j.val < frontier → v j = v' j)
    (hr : ∀ j, j.val ≤ frontier → row j = row' j) (z u y : Blocks E M) :
    referenceComponent n R q frontier v row z u y = referenceComponent n R q frontier v' row' z u y := by
  have hc : referenceClockGuard q frontier v z u = referenceClockGuard q frontier v' z u := by
    unfold referenceClockGuard
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hf : j.val < frontier
    · rw [if_pos hf, if_pos hf, hv j hf]
    · rw [if_neg hf, if_neg hf]
  have hs : (∑ j : Fin (M + 1), if j.val ≤ frontier then previousGate q v (fun j ↦ u j) j *
      ⟪zeta (z j) - Real.sqrt (n : ℝ) • row j, y j⟫_ℝ else 0) =
      ∑ j : Fin (M + 1), if j.val ≤ frontier then previousGate q v' (fun j ↦ u j) j *
        ⟪zeta (z j) - Real.sqrt (n : ℝ) • row' j, y j⟫_ℝ else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hf : j.val ≤ frontier
    · rw [if_pos hf, if_pos hf, hr j hf]
      congr 1
      unfold previousGate
      split_ifs with hz
      · rfl
      · rw [hv _ (by dsimp; omega)]
    · rw [if_neg hf, if_neg hf]
  simp only [referenceComponent, hc, hs]

theorem referenceFlatComponent_eq_of_known_data (R q : ℝ) (frontier : ℕ)
    (v v' row row' : Fin (M + 1) → E)
    (hv : ∀ j, j.val < frontier → v j = v' j)
    (hr : ∀ j, j.val ≤ frontier → row j = row' j) :
    referenceFlatComponent n R q frontier v row = referenceFlatComponent n R q frontier v' row' := by
  funext x
  exact referenceComponent_eq_of_known_data R q frontier v v' row row' hv hr _ _ _

theorem component_eq_reference_of_flat_correlations {q : ℝ} (hq : 1 ≤ q) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) (frontier : ℕ)
    (hv : ∀ j, ‖sourceMean w j‖ = 1) (z u y : Blocks E M)
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (z j), sourceMean w j⟫_ℝ ≤ 1 / 4 ∧
      |⟪normalizedClockProbe (u j), sourceMean w j⟫_ℝ| ≤ 1 / 2) :
    ConeValue.component R q w i z u y =
      referenceComponent n R q frontier (sourceMean w) (fun j ↦ w i j) z u y := by
  have hc : clockGuard q (sourceMean w) z u = referenceClockGuard q frontier (sourceMean w) z u := by
    unfold clockGuard referenceClockGuard
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hf : j.val < frontier
    · rw [if_pos hf]
    · rw [if_neg hf]
      rw [unfinished_clock_value (sourceMean w j) (z j) (u j) (hv j)
        (hgood j (by omega)).1 (hgood j (by omega)).2]
      rfl
  have hs : (∑ j : Fin (M + 1), previousGate q (sourceMean w) (fun j ↦ u j) j *
      ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ) =
      ∑ j : Fin (M + 1), if j.val ≤ frontier then previousGate q (sourceMean w) (fun j ↦ u j) j *
        ⟪zeta (z j) - Real.sqrt (n : ℝ) • w i j, y j⟫_ℝ else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hf : j.val ≤ frontier
    · rw [if_pos hf]
    · rw [if_neg hf]
      have hj0 : j.val ≠ 0 := by omega
      have hp : previousGate q (sourceMean w) (fun j ↦ u j) j = 0 := by
        unfold previousGate
        rw [dif_neg hj0]
        exact unfinished_gate_value hq _ _ (hv _) (hgood _ (by dsimp; omega)).2
      rw [hp, zero_mul]
  simp only [ConeValue.component, referenceComponent, hc, hs]

theorem normalizedClockProbe_continuous : Continuous (normalizedClockProbe : E → E) := by
  have hc : Continuous (fun u : E ↦ Real.sqrt (1 + ‖u‖ ^ 2)) :=
    (continuous_const.add (continuous_norm.pow 2)).sqrt
  exact (hc.inv₀ (fun u ↦ (Real.sqrt_pos.mpr (by positivity : 0 < 1 + ‖u‖ ^ 2)).ne')).smul continuous_id

/-- Strict margins make the entire literal component agree with the reference
on a neighborhood, so this statement includes all joint derivative directions. -/
theorem jointComponent_eventuallyEq_reference {q : ℝ} (hq : 1 ≤ q) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) (frontier : ℕ)
    (hv : ∀ j, ‖sourceMean w j‖ = 1) (x : JointBlocks E M)
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (x.fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (x.fst.snd j), sourceMean w j⟫_ℝ| < 1 / 2) :
    jointComponent R q w i =ᶠ[𝓝 x]
      referenceJointComponent n R q frontier (sourceMean w) (fun j ↦ w i j) := by
  have hz (j : Fin (M + 1)) : Continuous (fun X : JointBlocks E M ↦ X.fst.fst j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.fstL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).continuous
  have hu (j : Fin (M + 1)) : Continuous (fun X : JointBlocks E M ↦ X.fst.snd j) :=
    ((PiLp.proj 2 (fun _ : Fin (M + 1) ↦ E) j).comp
      ((WithLp.sndL 2 ℝ (Blocks E M) (Blocks E M)).comp
        (WithLp.fstL 2 ℝ (PrimalBlocks E M) (Blocks E M)))).continuous
  have heach (j : Fin (M + 1)) : ∀ᶠ X : JointBlocks E M in 𝓝 x, frontier ≤ j.val →
      ⟪zeta (X.fst.fst j), sourceMean w j⟫_ℝ ≤ 1 / 4 ∧
      |⟪normalizedClockProbe (X.fst.snd j), sourceMean w j⟫_ℝ| ≤ 1 / 2 := by
    by_cases hj : frontier ≤ j.val
    · have hzc : Continuous (fun X : JointBlocks E M ↦ ⟪zeta (X.fst.fst j), sourceMean w j⟫_ℝ) :=
        (ConeSmooth.zeta_contDiff.continuous.comp (hz j)).inner continuous_const
      have huc : Continuous (fun X : JointBlocks E M ↦
          |⟪normalizedClockProbe (X.fst.snd j), sourceMean w j⟫_ℝ|) :=
        ((normalizedClockProbe_continuous.comp (hu j)).inner continuous_const).abs
      have hzn := (isOpen_lt hzc continuous_const).mem_nhds (hgood j hj).1
      have hun := (isOpen_lt huc continuous_const).mem_nhds (hgood j hj).2
      filter_upwards [hzn, hun] with X hZ hU
      intro _
      exact ⟨hZ.le, hU.le⟩
    · exact Filter.Eventually.of_forall (fun _ h ↦ (hj h).elim)
  filter_upwards [Filter.eventually_all.mpr heach] with X hX
  exact component_eq_reference_of_flat_correlations hq R w i frontier hv X.fst.fst X.fst.snd X.snd hX

theorem flatComponent_eventuallyEq_reference {q : ℝ} (hq : 1 ≤ q) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) (frontier : ℕ)
    (hv : ∀ j, ‖sourceMean w j‖ = 1)
    (x : JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (((ConeProblem.jointCoordinates E M).symm x).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm x).fst.snd j), sourceMean w j⟫_ℝ| < 1 / 2) :
    ConeProblem.component R q w i =ᶠ[𝓝 x]
      referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w i j) := by
  have hh := jointComponent_eventuallyEq_reference hq R w i frontier hv
    ((ConeProblem.jointCoordinates E M).symm x) hgood
  exact hh.comp_tendsto (ConeProblem.jointCoordinates E M).symm.continuous.continuousAt

/-- Exact value and full joint gradient agreement for the actual Euclidean
component used in `ConeProblem.problem`. -/
theorem component_firstJet_eq_reference {q : ℝ} (hq : 1 ≤ q) (R : ℝ)
    (w : Fin n → Fin (M + 1) → E) (i : Fin n) (frontier : ℕ)
    (hv : ∀ j, ‖sourceMean w j‖ = 1)
    (x : JointSpace (ConeProblem.primalDimension E M) (ConeProblem.dualDimension E M))
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (((ConeProblem.jointCoordinates E M).symm x).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm x).fst.snd j), sourceMean w j⟫_ℝ| < 1 / 2) :
    ConeProblem.component R q w i x = referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w i j) x ∧
    gradient (ConeProblem.component R q w i) x =
      gradient (referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w i j)) x := by
  have hh := flatComponent_eventuallyEq_reference hq R w i frontier hv x hgood
  exact ⟨hh.eq_of_nhds, hh.gradient_eq⟩

/-- The literal full value-plus-gradient response of the actual `Problem`
equals the reference response on every good query. -/
theorem oracleResponse_eq_reference (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (frontier : ℕ)
    (o : OracleQuery n (ConeProblem.primalDimension E M) (ConeProblem.dualDomain E M R hR))
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.snd j),
        sourceMean w j⟫_ℝ| < 1 / 2) :
    oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw) o =
      (referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w o.1 j) (queryPoint o),
        (gradient (referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w o.1 j)) (queryPoint o)).fst,
        (gradient (referenceFlatComponent n R q frontier (sourceMean w) (fun j ↦ w o.1 j)) (queryPoint o)).snd) := by
  have hh := component_firstJet_eq_reference hq R w o.1 frontier (sourceMean_unit hn w hw)
    (queryPoint o) hgood
  change (ConeProblem.component R q w o.1 (queryPoint o),
      (gradient (ConeProblem.component R q w o.1) (queryPoint o)).fst,
      (gradient (ConeProblem.component R q w o.1) (queryPoint o)).snd) = _
  rw [hh.1, hh.2]

/-- A reference reply can be computed from arbitrary stored arrays that agree
with the actually revealed means and frontier row. Future entries are free. -/
theorem oracleResponse_eq_reference_known_data (hn : 0 < n) (L : ℝ) (hL : 0 < L)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q)
    (w : Fin n → Fin (M + 1) → E) (hw : ∀ j, Orthonormal ℝ (fun i ↦ w i j)) (frontier : ℕ)
    (o : OracleQuery n (ConeProblem.primalDimension E M) (ConeProblem.dualDomain E M R hR))
    (v row : Fin (M + 1) → E)
    (hv : ∀ j, j.val < frontier → sourceMean w j = v j)
    (hr : ∀ j, j.val ≤ frontier → w o.1 j = row j)
    (hgood : ∀ j, frontier ≤ j.val →
      ⟪zeta (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.fst j), sourceMean w j⟫_ℝ < 1 / 4 ∧
      |⟪normalizedClockProbe (((ConeProblem.jointCoordinates E M).symm (queryPoint o)).fst.snd j),
        sourceMean w j⟫_ℝ| < 1 / 2) :
    oracleResponse (ConeProblem.problem hn L hL R hR q hq w hw) o =
      (referenceFlatComponent n R q frontier v row (queryPoint o),
        (gradient (referenceFlatComponent n R q frontier v row) (queryPoint o)).fst,
        (gradient (referenceFlatComponent n R q frontier v row) (queryPoint o)).snd) := by
  have he := referenceFlatComponent_eq_of_known_data (n := n) R q frontier (sourceMean w) v
    (fun j ↦ w o.1 j) row hv hr
  have ho := oracleResponse_eq_reference hn L hL R hR q hq w hw frontier o hgood
  rw [he] at ho
  exact ho

end

end NCConcave16991.Haar
