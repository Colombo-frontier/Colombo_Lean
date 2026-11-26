import VIReference.Pilot.StiefelBlock
import MinimaxAudit.Transcript

/-!
# Haar concentration for the scalar minimax audit

The normalized Haar law, concrete orthogonal columns, spherical moments,
and block-Haar averaging are proved in the vendored `VIReference.Pilot`
closure. Provenance and exact frozen source hashes are recorded in
`reference/vendor_provenance.json`. Only its namespace/import prefix was
changed; this module supplies new applications to the scalar minimax model.

In particular, the arbitrary threshold below is the present paper's `s`,
not the reference operator construction's `hiddenTau`.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace MinimaxAudit.Haar

open VIReference.Pilot

noncomputable section

/-- The scalar paper uses n=N+1 hidden directions in each block. -/
abbrev FrameSample (d : ℕ) := RealOrthogonalGroup d

/-- A real-valued bound at an arbitrary slab threshold. -/
def slabTailReal (N d : ℕ) (R s : ℝ) : ℝ :=
  2 * Real.exp (-((d - (N + 1) : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2))

/-- Actual adapted Haar projection MGF. The source-dependent hypotheses are
only measurability, prefix dependence, and the feasible norm bound. The Haar
and spherical laws themselves are constructed in the imported proof. -/
theorem adapted_projection_mgf
    {N d : ℕ} {R : ℝ} (hR : 0 < R)
    (hnd : N + 1 < d) (t : ℕ) (ht : t ≤ N + 1)
    (i : Fin (N + 1)) (hti : t ≤ i.1)
    (x : FrameSample d → EuclideanSpace ℝ (Fin d))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q i) (x Q)))
    (hprefix : DependsOnlyOnFramePrefix
      (haarStiefelFrame (Nat.le_of_lt hnd)) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R) :
    HasSubgaussianMGF
      (fun Q => inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q i) (x Q))
      ⟨R ^ 2 / (d - (N + 1) : ℕ),
        div_nonneg (sq_nonneg R) (Nat.cast_nonneg _)⟩
      (orthogonalHaarProbability d) := by
  exact haarStiefelAdaptedProjectionMGF_proof
    (Nat.le_of_lt hnd) hR hnd t ht i hti x hmeas hprefix hx

/-- Arbitrary-threshold concentration for a concrete Haar frame and an
adapted feasible probe. The tail is obtained from the proved MGF, with no
conditional-distribution or concentration premise. -/
theorem adapted_projection_tail
    {N d : ℕ} {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hnd : N + 1 < d) (t : ℕ) (ht : t ≤ N + 1)
    (i : Fin (N + 1)) (hti : t ≤ i.1)
    (x : FrameSample d → EuclideanSpace ℝ (Fin d))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q i) (x Q)))
    (hprefix : DependsOnlyOnFramePrefix
      (haarStiefelFrame (Nat.le_of_lt hnd)) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R) :
    orthogonalHaarProbability d
      {Q | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q i) (x Q)| > s} ≤
      ENNReal.ofReal (slabTailReal N d R s) := by
  have hmgf := adapted_projection_mgf hR hnd t ht i hti x hmeas hprefix hx
  have hc : 0 ≤ R ^ 2 / (d - (N + 1) : ℕ) :=
    div_nonneg (sq_nonneg R) (Nat.cast_nonneg _)
  have htail := abs_tail_le_of_subgaussian_mgf hc hs hmgf
  have hk : (0 : ℝ) < (d - (N + 1) : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hnd
  have hexponent :
      -s ^ 2 / (2 * (R ^ 2 / (d - (N + 1) : ℕ))) =
      -((d - (N + 1) : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2) := by
    field_simp [hR.ne', hk.ne']
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  simpa only [slabTailReal, hexponent] using htail

/-- Prefix dependence on both primal and dual frames. It is a deterministic
invariance statement; no conditioning on previous success events occurs. -/
def PairPrefixDependent
    {N dx dy : ℕ} {E : Type*}
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy)
    (t : ℕ) (x : FrameSample dx × FrameSample dy → E) : Prop :=
  ∀ Q Q',
    (∀ i : Fin (N + 1), i.1 < t →
      haarStiefelFrame hxd Q.1 i = haarStiefelFrame hxd Q'.1 i) →
    (∀ i : Fin (N + 1), i.1 < t →
      haarStiefelFrame hyd Q.2 i = haarStiefelFrame hyd Q'.2 i) →
    x Q = x Q'

/-- Fixing the whole dual frame leaves a primal-prefix-adapted section. -/
theorem pair_prefix_primal_section
    {N dx dy : ℕ}
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy)
    {t : ℕ} {x : FrameSample dx × FrameSample dy → EuclideanSpace ℝ (Fin dx)}
    (hx : PairPrefixDependent hxd hyd t x) (V : FrameSample dy) :
    DependsOnlyOnFramePrefix (haarStiefelFrame hxd) t (fun U => x (U, V)) := by
  intro U U' hU
  exact hx (U, V) (U', V) hU (fun _ _ => rfl)

/-- Fixing the whole primal frame leaves a dual-prefix-adapted section. -/
theorem pair_prefix_dual_section
    {N dx dy : ℕ}
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy)
    {t : ℕ} {y : FrameSample dx × FrameSample dy → EuclideanSpace ℝ (Fin dy)}
    (hy : PairPrefixDependent hxd hyd t y) (U : FrameSample dx) :
    DependsOnlyOnFramePrefix (haarStiefelFrame hyd) t (fun V => y (U, V)) := by
  intro V V' hV
  exact hy (U, V) (U, V') (fun _ _ => rfl) hV

/-- Primal concentration under two independent concrete Haar frames.
The probe may adapt to the revealed prefixes of both frames. -/
theorem paired_primal_projection_tail
    {N dx dy : ℕ} {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (x : FrameSample dx × FrameSample dy → EuclideanSpace ℝ (Fin dx))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1 i) (x Q)))
    (hprefix : PairPrefixDependent (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t x)
    (hx : ∀ Q, ‖x Q‖ ≤ R) :
    ((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy))
      {Q | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1 i) (x Q)| > s} ≤
      ENNReal.ofReal (slabTailReal N dx R s) := by
  have hbad : MeasurableSet {Q | s <
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1 i) (x Q)|} :=
    measurableSet_lt measurable_const hmeas.abs
  rw [Measure.prod_apply_symm hbad]
  calc
    _ ≤ ∫⁻ _V : FrameSample dy, ENNReal.ofReal (slabTailReal N dx R s)
        ∂orthogonalHaarProbability dy := by
      apply lintegral_mono
      intro V
      exact adapted_projection_tail hR hs hxd t ht i hti (fun U => x (U, V))
        (hmeas.comp (measurable_id.prodMk measurable_const))
        (pair_prefix_primal_section _ _ hprefix V) (fun U => hx (U, V))
    _ = _ := by simp

/-- Dual concentration under the same independent pair of Haar laws. -/
theorem paired_dual_projection_tail
    {N dx dy : ℕ} {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (y : FrameSample dx × FrameSample dy → EuclideanSpace ℝ (Fin dy))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.2 i) (y Q)))
    (hprefix : PairPrefixDependent (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t y)
    (hy : ∀ Q, ‖y Q‖ ≤ R) :
    ((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy))
      {Q | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.2 i) (y Q)| > s} ≤
      ENNReal.ofReal (slabTailReal N dy R s) := by
  have hbad : MeasurableSet {Q | s <
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.2 i) (y Q)|} :=
    measurableSet_lt measurable_const hmeas.abs
  rw [Measure.prod_apply hbad]
  calc
    _ ≤ ∫⁻ _U : FrameSample dx, ENNReal.ofReal (slabTailReal N dy R s)
        ∂orthogonalHaarProbability dx := by
      apply lintegral_mono
      intro U
      exact adapted_projection_tail hR hs hyd t ht i hti (fun V => y (U, V))
        (hmeas.comp (measurable_const.prodMk measurable_id))
        (pair_prefix_dual_section _ _ hprefix U) (fun V => hy (U, V))
    _ = _ := by simp

/-- Independent algorithmic seeds can be included without weakening the
primal tail. Prefix adaptation is checked separately for each fixed seed. -/
theorem seeded_paired_primal_projection_tail
    {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (x : (FrameSample dx × FrameSample dy) × Seed → EuclideanSpace ℝ (Fin dx))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1.1 i) (x Q)))
    (hprefix : ∀ seed, PairPrefixDependent
      (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t (fun Q => x (Q, seed)))
    (hx : ∀ Q, ‖x Q‖ ≤ R) :
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod ν)
      {Q | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1.1 i) (x Q)| > s} ≤
      ENNReal.ofReal (slabTailReal N dx R s) := by
  have hbad : MeasurableSet {Q | s <
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) Q.1.1 i) (x Q)|} :=
    measurableSet_lt measurable_const hmeas.abs
  rw [Measure.prod_apply_symm hbad]
  calc
    _ ≤ ∫⁻ _seed : Seed, ENNReal.ofReal (slabTailReal N dx R s) ∂ν := by
      apply lintegral_mono
      intro seed
      exact paired_primal_projection_tail hR hs hxd hyd t ht i hti
        (fun Q => x (Q, seed))
        (hmeas.comp (measurable_id.prodMk measurable_const))
        (hprefix seed) (fun Q => hx (Q, seed))
    _ = _ := by simp

/-- The analogous dual tail for the same independent seed law. -/
theorem seeded_paired_dual_projection_tail
    {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (y : (FrameSample dx × FrameSample dy) × Seed → EuclideanSpace ℝ (Fin dy))
    (hmeas : Measurable (fun Q =>
      inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.1.2 i) (y Q)))
    (hprefix : ∀ seed, PairPrefixDependent
      (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t (fun Q => y (Q, seed)))
    (hy : ∀ Q, ‖y Q‖ ≤ R) :
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod ν)
      {Q | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.1.2 i) (y Q)| > s} ≤
      ENNReal.ofReal (slabTailReal N dy R s) := by
  have hbad : MeasurableSet {Q | s <
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) Q.1.2 i) (y Q)|} :=
    measurableSet_lt measurable_const hmeas.abs
  rw [Measure.prod_apply_symm hbad]
  calc
    _ ≤ ∫⁻ _seed : Seed, ENNReal.ofReal (slabTailReal N dy R s) ∂ν := by
      apply lintegral_mono
      intro seed
      exact paired_dual_projection_tail hR hs hxd hyd t ht i hti
        (fun Q => y (Q, seed))
        (hmeas.comp (measurable_id.prodMk measurable_const))
        (hprefix seed) (fun Q => hy (Q, seed))
    _ = _ := by simp

/-- The actual triangular query/hidden-column pairs, in zero-based indexing.
The second coordinate is the offset from the current query index. -/
abbrev QuerySlabIndex (N : ℕ) := (t : Fin N) × Fin (N + 1 - t.1)

/-- Two blocks, all future-column query events, and one arbitrary output
projection event in each block. -/
abbrev PairedSlabIndex (N : ℕ) := Bool × (QuerySlabIndex N ⊕ Unit)

/-- Exact event count n(n+1), with n=N+1. -/
theorem triangular_event_count (N : ℕ) :
    2 * (∑ t ∈ Finset.range N, (N + 1 - t)) + 2 = (N + 1) * (N + 2) := by
  have hreflect : (∑ t ∈ Finset.range N, (N + 1 - t)) =
      ∑ t ∈ Finset.range N, (t + 2) := by
    rw [← Finset.sum_range_reflect (fun t => N + 1 - t) N]
    apply Finset.sum_congr rfl
    intro t ht
    have htl : t < N := Finset.mem_range.mp ht
    omega
  rw [hreflect, Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hgauss := Finset.sum_range_id_mul_two N
  cases N with
  | zero => simp
  | succ N =>
    simp only [Nat.add_sub_cancel] at hgauss
    nlinarith

theorem card_pairedSlabIndex (N : ℕ) :
    Fintype.card (PairedSlabIndex N) = (N + 1) * (N + 2) := by
  simp only [PairedSlabIndex, QuerySlabIndex, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin, Fintype.card_unique]
  rw [Fin.sum_univ_eq_sum_range]
  have hc := triangular_event_count N
  omega

/-- An explicit logarithmic dimension sufficient for the finite union bound. -/

theorem log_dimension_controls_union
    {M R s delta k : ℝ} (hM : 0 < M) (hR : 0 < R) (hs : 0 < s)
    (hdelta : 0 < delta)
    (hdim : 2 * R ^ 2 / s ^ 2 * Real.log (2 * M / delta) ≤ k) :
    M * (2 * Real.exp (-k * s ^ 2 / (2 * R ^ 2))) ≤ delta := by
  let A : ℝ := 2 * M / delta
  have hA : 0 < A := by dsimp [A]; positivity
  have hc : 0 < s ^ 2 / (2 * R ^ 2) := by positivity
  have hscale := mul_le_mul_of_nonneg_right hdim hc.le
  have hcancel :
      (2 * R ^ 2 / s ^ 2 * Real.log A) * (s ^ 2 / (2 * R ^ 2)) =
      Real.log A := by field_simp [hs.ne', hR.ne']
  change (2 * R ^ 2 / s ^ 2 * Real.log A) *
    (s ^ 2 / (2 * R ^ 2)) ≤ k * (s ^ 2 / (2 * R ^ 2)) at hscale
  rw [hcancel] at hscale
  have hexparg : -k * s ^ 2 / (2 * R ^ 2) ≤ -Real.log A := by
    calc
      _ = -(k * (s ^ 2 / (2 * R ^ 2))) := by ring
      _ ≤ -Real.log A := neg_le_neg hscale
  have hexp : Real.exp (-k * s ^ 2 / (2 * R ^ 2)) ≤ 1 / A := by
    calc
      _ ≤ Real.exp (-Real.log A) := Real.exp_le_exp.mpr hexparg
      _ = 1 / A := by rw [Real.exp_neg, Real.exp_log hA]; simp [one_div]
  calc
    _ = (2 * M) * Real.exp (-k * s ^ 2 / (2 * R ^ 2)) := by ring
    _ ≤ (2 * M) * (1 / A) := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = delta := by dsimp [A]; field_simp
/-- Future-column index obtained from a query and a nonnegative offset. -/
def querySlabColumn {N : ℕ} (a : QuerySlabIndex N) : Fin (N + 1) :=
  ⟨a.1.1 + a.2.1, by have := a.1.2; have := a.2.2; omega⟩

/-- The exact data assumed in the paper's adapted concentration lemma,
for equal primal and dual ambient dimensions. This contains probes and their
adaptation properties, not a concentration or probability certificate. -/
structure PairedProbeFamily (N d : ℕ) (R : ℝ) (hnd : N + 1 < d) where
  primalQuery : Fin N → FrameSample d × FrameSample d → EuclideanSpace ℝ (Fin d)
  dualQuery : Fin N → FrameSample d × FrameSample d → EuclideanSpace ℝ (Fin d)
  primalOutput : FrameSample d × FrameSample d → EuclideanSpace ℝ (Fin d)
  dualOutput : FrameSample d × FrameSample d → EuclideanSpace ℝ (Fin d)
  primalQuery_meas : ∀ t i, Measurable (fun Q =>
    inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 i) (primalQuery t Q))
  dualQuery_meas : ∀ t i, Measurable (fun Q =>
    inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 i) (dualQuery t Q))
  primalOutput_meas : Measurable (fun Q =>
    inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (Fin.last N)) (primalOutput Q))
  dualOutput_meas : Measurable (fun Q =>
    inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (Fin.last N)) (dualOutput Q))
  primalQuery_prefix : ∀ t, PairPrefixDependent
    (Nat.le_of_lt hnd) (Nat.le_of_lt hnd) t.1 (primalQuery t)
  dualQuery_prefix : ∀ t, PairPrefixDependent
    (Nat.le_of_lt hnd) (Nat.le_of_lt hnd) t.1 (dualQuery t)
  primalOutput_prefix : PairPrefixDependent
    (Nat.le_of_lt hnd) (Nat.le_of_lt hnd) N primalOutput
  dualOutput_prefix : PairPrefixDependent
    (Nat.le_of_lt hnd) (Nat.le_of_lt hnd) N dualOutput
  primalQuery_norm : ∀ t Q, ‖primalQuery t Q‖ ≤ R
  dualQuery_norm : ∀ t Q, ‖dualQuery t Q‖ ≤ R
  primalOutput_norm : ∀ Q, ‖primalOutput Q‖ ≤ R
  dualOutput_norm : ∀ Q, ‖dualOutput Q‖ ≤ R

/-- Every source slab event, including the two arbitrary-output events. -/
def pairedBadEvent {N d : ℕ} {R : ℝ} {hnd : N + 1 < d}
    (probes : PairedProbeFamily N d R hnd) (s : ℝ) :
    PairedSlabIndex N → Set (FrameSample d × FrameSample d)
  | (false, Sum.inl a) => {Q |
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (querySlabColumn a))
        (probes.primalQuery a.1 Q)| > s}
  | (true, Sum.inl a) => {Q |
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (querySlabColumn a))
        (probes.dualQuery a.1 Q)| > s}
  | (false, Sum.inr _) => {Q |
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (Fin.last N))
        (probes.primalOutput Q)| > s}
  | (true, Sum.inr _) => {Q |
      |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (Fin.last N))
        (probes.dualOutput Q)| > s}

/-- Simultaneous good slabs, including the output that need not be queried. -/
def pairedSlabEvent {N d : ℕ} {R : ℝ} {hnd : N + 1 < d}
    (probes : PairedProbeFamily N d R hnd) (s : ℝ) :
    Set (FrameSample d × FrameSample d) :=
  (⋃ i : PairedSlabIndex N, pairedBadEvent probes s i)ᶜ

theorem pairedBadEvent_measurable {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (probes : PairedProbeFamily N d R hnd) (i : PairedSlabIndex N) :
    MeasurableSet (pairedBadEvent probes s i) := by
  rcases i with ⟨block, a | a⟩ <;> cases block
  · exact measurableSet_lt measurable_const (probes.primalQuery_meas _ _).abs
  · exact measurableSet_lt measurable_const (probes.dualQuery_meas _ _).abs
  · exact measurableSet_lt measurable_const probes.primalOutput_meas.abs
  · exact measurableSet_lt measurable_const probes.dualOutput_meas.abs

theorem pairedBadEvent_tail {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s) (probes : PairedProbeFamily N d R hnd)
    (i : PairedSlabIndex N) :
    ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
      (pairedBadEvent probes s i) ≤ ENNReal.ofReal (slabTailReal N d R s) := by
  rcases i with ⟨block, a | a⟩ <;> cases block
  · exact paired_primal_projection_tail hR hs hnd hnd a.1.1
      (by have := a.1.2; omega) (querySlabColumn a)
      (by simp only [querySlabColumn]; omega) (probes.primalQuery a.1)
      (probes.primalQuery_meas _ _) (probes.primalQuery_prefix _) (probes.primalQuery_norm _)
  · exact paired_dual_projection_tail hR hs hnd hnd a.1.1
      (by have := a.1.2; omega) (querySlabColumn a)
      (by simp only [querySlabColumn]; omega) (probes.dualQuery a.1)
      (probes.dualQuery_meas _ _) (probes.dualQuery_prefix _) (probes.dualQuery_norm _)
  · exact paired_primal_projection_tail hR hs hnd hnd N (by omega)
      (Fin.last N) (by simp) probes.primalOutput probes.primalOutput_meas
      probes.primalOutput_prefix probes.primalOutput_norm
  · exact paired_dual_projection_tail hR hs hnd hnd N (by omega)
      (Fin.last N) (by simp) probes.dualOutput probes.dualOutput_meas
      probes.dualOutput_prefix probes.dualOutput_norm

/-- Actual simultaneous paired-Haar slab bound with the exact n(n+1)
event count. No tail bound is present among this theorem's hypotheses. -/
theorem pairedSlabEvent_probability {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s) (probes : PairedProbeFamily N d R hnd) :
    1 - (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (slabTailReal N d R s) ≤
    ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
      (pairedSlabEvent probes s) := by
  have h := Transcript.finite_good_event_probability
    ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
    (Finset.univ : Finset (PairedSlabIndex N)) (pairedBadEvent probes s)
    (fun i _ => pairedBadEvent_measurable probes i)
    (fun _ => ENNReal.ofReal (slabTailReal N d R s))
    (fun i _ => pairedBadEvent_tail hR hs probes i)
  have h' : 1 - (Fintype.card (PairedSlabIndex N) : ℝ≥0∞) *
      ENNReal.ofReal (slabTailReal N d R s) ≤
      ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
        (pairedSlabEvent probes s) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mem_univ, Set.iUnion_true, pairedSlabEvent] using h
  rw [card_pairedSlabIndex] at h'
  exact h'

/-- The last hidden primal and dual directions are small on the simultaneous
slab event, independently of whether the output was queried. -/
theorem output_slabs_of_pairedSlabEvent
    {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (probes : PairedProbeFamily N d R hnd)
    {Q : FrameSample d × FrameSample d} (hQ : Q ∈ pairedSlabEvent probes s) :
    |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (Fin.last N))
      (probes.primalOutput Q)| ≤ s ∧
    |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (Fin.last N))
      (probes.dualOutput Q)| ≤ s := by
  have hnone : ∀ i : PairedSlabIndex N, Q ∉ pairedBadEvent probes s i := by
    simpa only [pairedSlabEvent, Set.mem_compl_iff, Set.mem_iUnion, not_exists] using hQ
  exact ⟨not_lt.mp (hnone (false, Sum.inr ())), not_lt.mp (hnone (true, Sum.inr ()))⟩

/-- Explicit log dimension for the simultaneous paired-Haar slabs.
The full tail and union estimate are proved here, rather than supplied as a
field of the probe family. -/
theorem pairedSlabEvent_probability_of_dimension
    {N d : ℕ} {R s delta : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s) (hdelta : 0 < delta)
    (probes : PairedProbeFamily N d R hnd)
    (hdim : 2 * R ^ 2 / s ^ 2 *
      Real.log (2 * (((N + 1) * (N + 2) : ℕ) : ℝ) / delta) ≤
      ((d - (N + 1) : ℕ) : ℝ)) :
    ENNReal.ofReal (1 - delta) ≤
      ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
        (pairedSlabEvent probes s) := by
  have hreal : (((N + 1) * (N + 2) : ℕ) : ℝ) * slabTailReal N d R s ≤ delta :=
    log_dimension_controls_union (by positivity) hR hs hdelta hdim
  have hsmall : (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (slabTailReal N d R s) ≤ ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg ((N + 1) * (N + 2)))]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    ENNReal.ofReal (1 - delta) = 1 - ENNReal.ofReal delta := by
      rw [ENNReal.ofReal_sub 1 hdelta.le]
      simp
    _ ≤ 1 - (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (slabTailReal N d R s) := tsub_le_tsub_left hsmall 1
    _ ≤ _ := pairedSlabEvent_probability hR hs probes

/-- The paper's required 3/4 probability, at an explicit sufficient dimension. -/
theorem pairedSlabEvent_three_quarters
    {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s) (probes : PairedProbeFamily N d R hnd)
    (hdim : 2 * R ^ 2 / s ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      ((d - (N + 1) : ℕ) : ℝ)) :
    (3 / 4 : ℝ≥0∞) ≤
      ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
        (pairedSlabEvent probes s) := by
  have h := pairedSlabEvent_probability_of_dimension hR hs
    (by norm_num : (0 : ℝ) < 1 / 4) probes (by
      convert hdim using 2; ring_nf)
  norm_num at h ⊢
  simpa [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)] using h

/-- A stricter slab with room inside the scalar gates. -/

def strictSlabThreshold (n eta kappa R : ℝ) : ℝ :=
  eta * kappa * R / (8 * Real.sqrt 2 * n * Real.sqrt n)

theorem strictSlabThreshold_pos {n eta kappa R : ℝ}
    (hn : 0 < n) (heta : 0 < eta) (hkappa : 0 < kappa) (hR : 0 < R) :
    0 < strictSlabThreshold n eta kappa R := by
  unfold strictSlabThreshold
  positivity

theorem strict_slab_dimension_factor {n eta kappa R : ℝ}
    (hn : 0 < n) (heta : 0 < eta) (hkappa : 0 < kappa) (hR : 0 < R) :
    2 * R ^ 2 / (strictSlabThreshold n eta kappa R) ^ 2 =
      256 * n ^ 3 / (eta * kappa) ^ 2 := by
  unfold strictSlabThreshold
  rw [div_pow]
  simp only [mul_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hn.le]
  field_simp
  ring

theorem paired_event_log_bound {n : ℝ} (hn : 1 ≤ n) :
    Real.log (8 * (n * (n + 1))) ≤ 5 * Real.log (n + 1) := by
  have hn0 : 0 ≤ n := by linarith
  have hn1 : 0 ≤ n + 1 := by linarith
  have hcube : (8 : ℝ) ≤ (n + 1) ^ 3 := by
    calc
      (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (n + 1) ^ 3 := by gcongr; linarith
  have hprod : 8 * (n * (n + 1)) ≤ (n + 1) ^ 5 := by
    calc
      _ ≤ (n + 1) ^ 3 * ((n + 1) * (n + 1)) := by gcongr; linarith
      _ = _ := by ring
  calc
    _ ≤ Real.log ((n + 1) ^ 5) := Real.log_le_log (by positivity) hprod
    _ = 5 * Real.log (n + 1) := by rw [Real.log_pow]; norm_num
/-- The cubic-logarithmic dimension in the paper is sufficient with an
explicit universal coefficient and a strict interior gate margin. -/
theorem pairedSlabEvent_strict_scale_three_quarters
    {N d : ℕ} {eta kappa R : ℝ} {hnd : N + 1 < d}
    (heta : 0 < eta) (hkappa : 0 < kappa) (hR : 0 < R)
    (probes : PairedProbeFamily N d R hnd)
    (hdim : 1280 * (N + 1 : ℝ) ^ 3 / (eta * kappa) ^ 2 *
      Real.log (N + 2 : ℝ) ≤ ((d - (N + 1) : ℕ) : ℝ)) :
    (3 / 4 : ℝ≥0∞) ≤
      ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d))
        (pairedSlabEvent probes (strictSlabThreshold (N + 1) eta kappa R)) := by
  have hn : (0 : ℝ) < N + 1 := by positivity
  have hs := strictSlabThreshold_pos hn heta hkappa hR
  apply pairedSlabEvent_three_quarters hR hs probes
  rw [strict_slab_dimension_factor hn heta hkappa hR]
  have hlog := paired_event_log_bound (n := (N + 1 : ℝ)) (by
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith)
  have hlog' : Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      5 * Real.log (N + 2 : ℝ) := by
    convert hlog using 1 <;> push_cast <;> ring_nf
  calc
    _ ≤ (256 * (N + 1 : ℝ) ^ 3 / (eta * kappa) ^ 2) *
        (5 * Real.log (N + 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ = 1280 * (N + 1 : ℝ) ^ 3 / (eta * kappa) ^ 2 *
        Real.log (N + 2 : ℝ) := by ring
    _ ≤ _ := hdim

/-- Plain source form of all future query slabs, recovered from the exact
finite event index without an irrelevant rectangular overcount. -/
theorem query_slabs_of_pairedSlabEvent
    {N d : ℕ} {R s : ℝ} {hnd : N + 1 < d}
    (probes : PairedProbeFamily N d R hnd)
    {Q : FrameSample d × FrameSample d} (hQ : Q ∈ pairedSlabEvent probes s)
    (t : Fin N) (i : Fin (N + 1)) (hti : t.1 ≤ i.1) :
    |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 i)
      (probes.primalQuery t Q)| ≤ s ∧
    |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 i)
      (probes.dualQuery t Q)| ≤ s := by
  have hnone : ∀ j : PairedSlabIndex N, Q ∉ pairedBadEvent probes s j := by
    simpa only [pairedSlabEvent, Set.mem_compl_iff, Set.mem_iUnion, not_exists] using hQ
  let a : QuerySlabIndex N := ⟨t, ⟨i.1 - t.1, by have := t.2; have := i.2; omega⟩⟩
  have hcol : querySlabColumn a = i := by
    apply Fin.ext
    simp only [querySlabColumn, a]
    omega
  have hp := hnone (false, Sum.inl a)
  have hd := hnone (true, Sum.inl a)
  change ¬s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.1 (querySlabColumn a))
    (probes.primalQuery t Q)| at hp
  change ¬s < |inner ℝ (haarStiefelFrame (Nat.le_of_lt hnd) Q.2 (querySlabColumn a))
    (probes.dualQuery t Q)| at hd
  rw [hcol] at hp hd
  exact ⟨not_lt.mp hp, not_lt.mp hd⟩

/-- Integrate the proved paired-Haar concentration over an arbitrary
independent algorithmic seed. Joint measurability is an explicit source
policy obligation; there is no joint-probability premise. -/
theorem seeded_pairedSlabEvent_three_quarters
    {N d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {R s : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s)
    (probes : Seed → PairedProbeFamily N d R hnd)
    (hmeas : MeasurableSet {w : (FrameSample d × FrameSample d) × Seed |
      w.1 ∈ pairedSlabEvent (probes w.2) s})
    (hdim : 2 * R ^ 2 / s ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      ((d - (N + 1) : ℕ) : ℝ)) :
    (3 / 4 : ℝ≥0∞) ≤
      (((orthogonalHaarProbability d).prod (orthogonalHaarProbability d)).prod ν)
        {w : (FrameSample d × FrameSample d) × Seed |
          w.1 ∈ pairedSlabEvent (probes w.2) s} := by
  apply joint_probability_ge_of_seedwise
    ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d)) ν hmeas (3 / 4)
  intro seed
  exact pairedSlabEvent_three_quarters hR hs (probes seed) hdim

/-- A single primal/dual frame pair works for at least 3/4 of independent
seeds. The frame pair does not depend on the realized seed. -/
theorem exists_fixed_pair_seed_slabs
    {N d : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    {R s : ℝ} {hnd : N + 1 < d}
    (hR : 0 < R) (hs : 0 < s)
    (probes : Seed → PairedProbeFamily N d R hnd)
    (hmeas : MeasurableSet {w : (FrameSample d × FrameSample d) × Seed |
      w.1 ∈ pairedSlabEvent (probes w.2) s})
    (hdim : 2 * R ^ 2 / s ^ 2 *
      Real.log (8 * (((N + 1) * (N + 2) : ℕ) : ℝ)) ≤
      ((d - (N + 1) : ℕ) : ℝ)) :
    ∃ Q : FrameSample d × FrameSample d,
      (3 / 4 : ℝ≥0∞) ≤ ν {seed | Q ∈ pairedSlabEvent (probes seed) s} := by
  apply Transcript.exists_fixed_frame_of_joint_failure
    ((orthogonalHaarProbability d).prod (orthogonalHaarProbability d)) ν
    _ hmeas (3 / 4)
  exact seeded_pairedSlabEvent_three_quarters ν hR hs probes hmeas hdim

end

end MinimaxAudit.Haar
