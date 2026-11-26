import MinimaxAudit.Haar
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Source-faithful adaptive Haar lemma

Unlike the equal-dimension specialization used by the main lower bound, this
module permits different primal/dual dimensions, every 0<delta<1, an arbitrary
independent seed, exact sigma(seed,revealed columns) measurability, and only
almost-sure feasible-radius bounds. No pointwise-prefix or pointwise-bound
certificate is assumed of the original probes.
-/
open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace MinimaxAudit.HaarSource
open VIReference.Pilot
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev Sample (dx dy : ℕ) (Seed : Type*) := (Haar.FrameSample dx × Haar.FrameSample dy) × Seed

/-- The generating random variable for sigma(seed,first t primal/dual columns). -/
def prefixData {N dx dy : ℕ} {Seed : Type*}
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy) (t : ℕ) (ht : t ≤ N + 1)
    (w : Sample dx dy Seed) :
    Seed × (Fin t → EuclideanSpace ℝ (Fin dx)) × (Fin t → EuclideanSpace ℝ (Fin dy)) :=
  (w.2, (fun i => haarStiefelFrame hxd w.1.1 (Fin.castLE ht i)),
    (fun i => haarStiefelFrame hyd w.1.2 (Fin.castLE ht i)))

abbrev prefixSigma {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy) (t : ℕ) (ht : t ≤ N + 1) :
    MeasurableSpace (Sample dx dy Seed) :=
  MeasurableSpace.comap (prefixData (Seed := Seed) hxd hyd t ht) inferInstance

theorem prefixData_measurable {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy) (t : ℕ) (ht : t ≤ N + 1) :
    Measurable (prefixData (Seed := Seed) hxd hyd t ht) := by
  apply measurable_snd.prodMk
  apply Measurable.prodMk
  · apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (Fin.castLE ht i)).comp
      ((measurable_haarStiefelFrame hxd).comp (measurable_fst.comp measurable_fst))
  · apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (Fin.castLE ht i)).comp
      ((measurable_haarStiefelFrame hyd).comp (measurable_snd.comp measurable_fst))

/-- Measurability in the source filtration implies ambient joint measurability. -/
theorem adapted_jointlyMeasurable
    {N dx dy : ℕ} {Seed E : Type*} [MeasurableSpace Seed] [MeasurableSpace E]
    {hxd : N + 1 ≤ dx} {hyd : N + 1 ≤ dy} {t : ℕ} {ht : t ≤ N + 1}
    {x : Sample dx dy Seed → E} (hx : Measurable[prefixSigma hxd hyd t ht] x) :
    Measurable x :=
  hx.mono (prefixData_measurable hxd hyd t ht).comap_le le_rfl

/-- Exact fiber constancy follows from the source filtration measurability,
using measurable singletons; no Doob-Dynkin representative is postulated. -/
theorem adapted_prefix
    {N dx dy : ℕ} {Seed E : Type*} [MeasurableSpace Seed]
    [MeasurableSpace E] [MeasurableSingletonClass E]
    {hxd : N + 1 ≤ dx} {hyd : N + 1 ≤ dy} {t : ℕ} {ht : t ≤ N + 1}
    {x : Sample dx dy Seed → E} (hx : Measurable[prefixSigma hxd hyd t ht] x)
    (seed : Seed) :
    Haar.PairPrefixDependent hxd hyd t (fun Q => x (Q, seed)) := by
  intro Q Q' hU hV
  apply hx.factorsThrough
  have hf : (fun i : Fin t => haarStiefelFrame hxd Q.1 (Fin.castLE ht i)) =
      (fun i : Fin t => haarStiefelFrame hxd Q'.1 (Fin.castLE ht i)) := by
    funext i
    exact hU (Fin.castLE ht i) i.2
  have hg : (fun i : Fin t => haarStiefelFrame hyd Q.2 (Fin.castLE ht i)) =
      (fun i : Fin t => haarStiefelFrame hyd Q'.2 (Fin.castLE ht i)) := by
    funext i
    exact hV (Fin.castLE ht i) i.2
  exact congrArg₂ (fun f g => (seed, f, g)) hf hg

/-- A measurable, prefix-preserving feasible representative. It equals the
original probe almost surely whenever that probe satisfies its source bound. -/
def boundedProbe {Omega E : Type*} [NormedAddCommGroup E] (R : ℝ) (x : Omega → E) (w : Omega) : E :=
  if ‖x w‖ ≤ R then x w else 0

theorem boundedProbe_measurable {Omega E : Type*} [MeasurableSpace Omega]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (R : ℝ) {x : Omega → E} (hx : Measurable x) : Measurable (boundedProbe R x) := by
  exact hx.piecewise (measurableSet_le hx.norm measurable_const) measurable_const

theorem boundedProbe_norm {Omega E : Type*} [NormedAddCommGroup E]
    {R : ℝ} (hR : 0 ≤ R) (x : Omega → E) (w : Omega) : ‖boundedProbe R x w‖ ≤ R := by
  by_cases h : ‖x w‖ ≤ R <;> simp [boundedProbe, h, hR]

theorem boundedProbe_ae_eq {Omega E : Type*} [MeasurableSpace Omega] [NormedAddCommGroup E]
    {mu : Measure Omega} {R : ℝ} {x : Omega → E} (hx : ∀ᵐ w ∂mu, ‖x w‖ ≤ R) :
    boundedProbe R x =ᵐ[mu] x := by
  filter_upwards [hx] with w hw
  simp [boundedProbe, hw]

/-- A primal projection tail for a source-filtration-adapted probe with only
an almost-sure norm bound. Unequal dimensions and independent seeds are real. -/
theorem source_primal_tail
    {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (x : Sample dx dy Seed → EuclideanSpace ℝ (Fin dx))
    (hx : Measurable[prefixSigma (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t ht] x)
    (hbound : ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
      ‖x w‖ ≤ R) :
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
      {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) w.1.1 i) (x w)| > s} ≤
      ENNReal.ofReal (Haar.slabTailReal N dx R s) := by
  let mu := ((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu
  have hxm : Measurable x := adapted_jointlyMeasurable hx
  have hclip := boundedProbe_measurable R hxm
  have hu : Measurable (fun w : Sample dx dy Seed =>
      haarStiefelFrame (Nat.le_of_lt hxd) w.1.1 i) :=
    (measurable_pi_apply i).comp ((measurable_haarStiefelFrame (Nat.le_of_lt hxd)).comp
      (measurable_fst.comp measurable_fst))
  have hprefix : ∀ seed, Haar.PairPrefixDependent (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t
      (fun Q => boundedProbe R x (Q, seed)) := by
    intro seed Q Q' hU hV
    have heq := adapted_prefix hx seed Q Q' hU hV
    change x (Q, seed) = x (Q', seed) at heq
    exact congrArg (fun v => if ‖v‖ ≤ R then v else 0) heq
  have htail := Haar.seeded_paired_primal_projection_tail nu hR hs hxd hyd t ht i hti
    (boundedProbe R x) (hu.inner hclip) hprefix (boundedProbe_norm hR.le x)
  have heq : mu {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) w.1.1 i) (x w)| > s} =
      mu {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hxd) w.1.1 i) (boundedProbe R x w)| > s} := by
    apply measure_congr
    filter_upwards [boundedProbe_ae_eq hbound] with w hw
    exact (congrArg (fun v => s < |inner ℝ
      (haarStiefelFrame (Nat.le_of_lt hxd) w.1.1 i) v|) hw.symm)
  rw [heq]
  exact htail

/-- The corresponding dual projection tail, under the same source filtration. -/
theorem source_dual_tail
    {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (nu : Measure Seed) [IsProbabilityMeasure nu]
    {R s : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hxd : N + 1 < dx) (hyd : N + 1 < dy)
    (t : ℕ) (ht : t ≤ N + 1) (i : Fin (N + 1)) (hti : t ≤ i.1)
    (y : Sample dx dy Seed → EuclideanSpace ℝ (Fin dy))
    (hy : Measurable[prefixSigma (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t ht] y)
    (hbound : ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
      ‖y w‖ ≤ R) :
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
      {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) w.1.2 i) (y w)| > s} ≤
      ENNReal.ofReal (Haar.slabTailReal N dy R s) := by
  let mu := ((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu
  have hym : Measurable y := adapted_jointlyMeasurable hy
  have hclip := boundedProbe_measurable R hym
  have hv : Measurable (fun w : Sample dx dy Seed =>
      haarStiefelFrame (Nat.le_of_lt hyd) w.1.2 i) :=
    (measurable_pi_apply i).comp ((measurable_haarStiefelFrame (Nat.le_of_lt hyd)).comp
      (measurable_snd.comp measurable_fst))
  have hprefix : ∀ seed, Haar.PairPrefixDependent (Nat.le_of_lt hxd) (Nat.le_of_lt hyd) t
      (fun Q => boundedProbe R y (Q, seed)) := by
    intro seed Q Q' hU hV
    have heq := adapted_prefix hy seed Q Q' hU hV
    change y (Q, seed) = y (Q', seed) at heq
    exact congrArg (fun v => if ‖v‖ ≤ R then v else 0) heq
  have htail := Haar.seeded_paired_dual_projection_tail nu hR hs hxd hyd t ht i hti
    (boundedProbe R y) (hv.inner hclip) hprefix (boundedProbe_norm hR.le y)
  have heq : mu {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) w.1.2 i) (y w)| > s} =
      mu {w | |inner ℝ (haarStiefelFrame (Nat.le_of_lt hyd) w.1.2 i) (boundedProbe R y w)| > s} := by
    apply measure_congr
    filter_upwards [boundedProbe_ae_eq hbound] with w hw
    exact (congrArg (fun v => s < |inner ℝ
      (haarStiefelFrame (Nat.le_of_lt hyd) w.1.2 i) v|) hw.symm)
  rw [heq]
  exact htail

/-- Exactly the source-adapted probes, allowing a.s. feasibility. These
fields contain no projection-tail or simultaneous-probability assumption. -/
structure AdaptedProbes (N dx dy : ℕ) (Seed : Type*) [MeasurableSpace Seed]
    (R : ℝ) (nu : Measure Seed) (hxd : N + 1 ≤ dx) (hyd : N + 1 ≤ dy) where
  primalQuery : Fin N → Sample dx dy Seed → EuclideanSpace ℝ (Fin dx)
  dualQuery : Fin N → Sample dx dy Seed → EuclideanSpace ℝ (Fin dy)
  primalOutput : Sample dx dy Seed → EuclideanSpace ℝ (Fin dx)
  dualOutput : Sample dx dy Seed → EuclideanSpace ℝ (Fin dy)
  primalQuery_adapted : ∀ t, Measurable[prefixSigma hxd hyd t.1 (by have := t.2; omega)] (primalQuery t)
  dualQuery_adapted : ∀ t, Measurable[prefixSigma hxd hyd t.1 (by have := t.2; omega)] (dualQuery t)
  primalOutput_adapted : Measurable[prefixSigma hxd hyd N (by omega)] primalOutput
  dualOutput_adapted : Measurable[prefixSigma hxd hyd N (by omega)] dualOutput
  primalQuery_bound : ∀ t, ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
    ‖primalQuery t w‖ ≤ R
  dualQuery_bound : ∀ t, ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
    ‖dualQuery t w‖ ≤ R
  primalOutput_bound : ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
    ‖primalOutput w‖ ≤ R
  dualOutput_bound : ∀ᵐ w ∂(((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu),
    ‖dualOutput w‖ ≤ R

/-- Increasing the ambient dimension improves the proved spherical tail. -/
theorem slabTailReal_antitone {N d e : ℕ} {R s : ℝ} (hde : d ≤ e) :
    Haar.slabTailReal N e R s ≤ Haar.slabTailReal N d R s := by
  have hk : ((d - (N + 1) : ℕ) : ℝ) ≤ ((e - (N + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.sub_le_sub_right hde (N + 1))
  unfold Haar.slabTailReal
  gcongr

variable {N dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed]
variable {R s : ℝ} {nu : Measure Seed} {hxd : N + 1 ≤ dx} {hyd : N + 1 ≤ dy}

/-- The exact triangular collection of all raw bad projections. -/
def sourceBadEvent (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) (s : ℝ) :
    Haar.PairedSlabIndex N → Set (Sample dx dy Seed)
  | (false, Sum.inl a) => {w |
      |inner ℝ (haarStiefelFrame hxd w.1.1 (Haar.querySlabColumn a)) (probes.primalQuery a.1 w)| > s}
  | (true, Sum.inl a) => {w |
      |inner ℝ (haarStiefelFrame hyd w.1.2 (Haar.querySlabColumn a)) (probes.dualQuery a.1 w)| > s}
  | (false, Sum.inr _) => {w |
      |inner ℝ (haarStiefelFrame hxd w.1.1 (Fin.last N)) (probes.primalOutput w)| > s}
  | (true, Sum.inr _) => {w |
      |inner ℝ (haarStiefelFrame hyd w.1.2 (Fin.last N)) (probes.dualOutput w)| > s}

def sourceSlabEvent (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) (s : ℝ) :
    Set (Sample dx dy Seed) :=
  (⋃ i : Haar.PairedSlabIndex N, sourceBadEvent probes s i)ᶜ

theorem sourceBadEvent_measurable
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) (i : Haar.PairedSlabIndex N) :
    MeasurableSet (sourceBadEvent probes s i) := by
  have hu (j : Fin (N + 1)) : Measurable (fun w : Sample dx dy Seed =>
      haarStiefelFrame hxd w.1.1 j) :=
    (measurable_pi_apply j).comp ((measurable_haarStiefelFrame hxd).comp
      (measurable_fst.comp measurable_fst))
  have hv (j : Fin (N + 1)) : Measurable (fun w : Sample dx dy Seed =>
      haarStiefelFrame hyd w.1.2 j) :=
    (measurable_pi_apply j).comp ((measurable_haarStiefelFrame hyd).comp
      (measurable_snd.comp measurable_fst))
  rcases i with ⟨block, a | a⟩ <;> cases block
  · exact measurableSet_lt measurable_const
      ((hu _).inner (adapted_jointlyMeasurable (probes.primalQuery_adapted _))).abs
  · exact measurableSet_lt measurable_const
      ((hv _).inner (adapted_jointlyMeasurable (probes.dualQuery_adapted _))).abs
  · exact measurableSet_lt measurable_const
      ((hu _).inner (adapted_jointlyMeasurable probes.primalOutput_adapted)).abs
  · exact measurableSet_lt measurable_const
      ((hv _).inner (adapted_jointlyMeasurable probes.dualOutput_adapted)).abs

/-- Each of the n(n+1) source events satisfies the actual seeded Haar tail. -/
theorem sourceBadEvent_tail [IsProbabilityMeasure nu]
    (hR : 0 < R) (hs : 0 < s) (hxs : N + 1 < dx) (hys : N + 1 < dy)
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) (i : Haar.PairedSlabIndex N) :
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
      (sourceBadEvent probes s i) ≤
      ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s) := by
  rcases i with ⟨block, a | a⟩ <;> cases block
  · exact (source_primal_tail nu hR hs hxs hys a.1.1 (by have := a.1.2; omega)
      (Haar.querySlabColumn a) (by simp only [Haar.querySlabColumn]; omega)
      (probes.primalQuery a.1) (probes.primalQuery_adapted a.1) (probes.primalQuery_bound a.1)).trans
      (ENNReal.ofReal_le_ofReal (slabTailReal_antitone (Nat.min_le_left dx dy)))
  · exact (source_dual_tail nu hR hs hxs hys a.1.1 (by have := a.1.2; omega)
      (Haar.querySlabColumn a) (by simp only [Haar.querySlabColumn]; omega)
      (probes.dualQuery a.1) (probes.dualQuery_adapted a.1) (probes.dualQuery_bound a.1)).trans
      (ENNReal.ofReal_le_ofReal (slabTailReal_antitone (Nat.min_le_right dx dy)))
  · exact (source_primal_tail nu hR hs hxs hys N (by omega) (Fin.last N) (by simp)
      probes.primalOutput probes.primalOutput_adapted probes.primalOutput_bound).trans
      (ENNReal.ofReal_le_ofReal (slabTailReal_antitone (Nat.min_le_left dx dy)))
  · exact (source_dual_tail nu hR hs hxs hys N (by omega) (Fin.last N) (by simp)
      probes.dualOutput probes.dualOutput_adapted probes.dualOutput_bound).trans
      (ENNReal.ofReal_le_ofReal (slabTailReal_antitone (Nat.min_le_right dx dy)))

/-- Genuine union estimate on the joint law of both frames and the
independent seed; no conditional-probability certificate is assumed. -/
theorem sourceSlabEvent_probability [IsProbabilityMeasure nu]
    (hR : 0 < R) (hs : 0 < s) (hxs : N + 1 < dx) (hys : N + 1 < dy)
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) :
    1 - (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s) ≤
      (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
        (sourceSlabEvent probes s) := by
  have h := Transcript.finite_good_event_probability
    (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
    (Finset.univ : Finset (Haar.PairedSlabIndex N)) (sourceBadEvent probes s)
    (fun i _ => sourceBadEvent_measurable probes i)
    (fun _ => ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s))
    (fun i _ => sourceBadEvent_tail hR hs hxs hys probes i)
  have h' : 1 - (Fintype.card (Haar.PairedSlabIndex N) : ℝ≥0∞) *
      ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s) ≤
      (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
        (sourceSlabEvent probes s) := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.mem_univ, Set.iUnion_true, sourceSlabEvent] using h
  rw [Haar.card_pairedSlabIndex] at h'
  exact h'

/-- The convenient universal C=6 absorbs the exact event-count logarithm. -/
theorem source_event_log_bound {n delta : ℝ} (hn : 1 ≤ n)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    Real.log (2 * (n * (n + 1)) / delta) ≤
      3 * Real.log ((n + 1) / delta) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n + 1 := by linarith
  have hnne := ne_of_gt hn0
  have hn1ne := ne_of_gt hn1
  have hdne := ne_of_gt hd0
  have hlog2 : Real.log 2 ≤ Real.log (n + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogn : Real.log n ≤ Real.log (n + 1) := Real.log_le_log hn0 (by linarith)
  have hlogd : Real.log delta ≤ 0 := Real.log_nonpos hd0.le hd1.le
  rw [Real.log_div (by positivity) hdne, Real.log_mul (by norm_num) (by positivity),
    Real.log_mul hnne hn1ne, Real.log_div hn1ne hdne]
  linarith

/-- Plain source event: all future columns at all queries and both last
output columns, without an indexing abstraction in its proposition. -/
def sourceAllSlabs (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) (s : ℝ) :
    Set (Sample dx dy Seed) := {w |
      (∀ t : Fin N, ∀ i : Fin (N + 1), t.1 ≤ i.1 →
        |inner ℝ (haarStiefelFrame hxd w.1.1 i) (probes.primalQuery t w)| ≤ s ∧
        |inner ℝ (haarStiefelFrame hyd w.1.2 i) (probes.dualQuery t w)| ≤ s) ∧
      |inner ℝ (haarStiefelFrame hxd w.1.1 (Fin.last N)) (probes.primalOutput w)| ≤ s ∧
      |inner ℝ (haarStiefelFrame hyd w.1.2 (Fin.last N)) (probes.dualOutput w)| ≤ s}

theorem sourceSlabEvent_eq_sourceAllSlabs
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) :
    sourceSlabEvent probes s = sourceAllSlabs probes s := by
  ext w
  constructor
  · intro hw
    have hnone : ∀ j : Haar.PairedSlabIndex N, w ∉ sourceBadEvent probes s j := by
      simpa only [sourceSlabEvent, Set.mem_compl_iff, Set.mem_iUnion, not_exists] using hw
    refine ⟨?_, not_lt.mp (hnone (false, Sum.inr ())), not_lt.mp (hnone (true, Sum.inr ()))⟩
    intro t i hti
    let a : Haar.QuerySlabIndex N := ⟨t, ⟨i.1 - t.1, by have := t.2; have := i.2; omega⟩⟩
    have hcol : Haar.querySlabColumn a = i := by
      apply Fin.ext
      simp only [Haar.querySlabColumn, a]
      omega
    have hp := hnone (false, Sum.inl a)
    have hd := hnone (true, Sum.inl a)
    change ¬s < |inner ℝ (haarStiefelFrame hxd w.1.1 (Haar.querySlabColumn a))
      (probes.primalQuery t w)| at hp
    change ¬s < |inner ℝ (haarStiefelFrame hyd w.1.2 (Haar.querySlabColumn a))
      (probes.dualQuery t w)| at hd
    rw [hcol] at hp hd
    exact ⟨not_lt.mp hp, not_lt.mp hd⟩
  · rintro ⟨hq, hx, hy⟩
    change w ∉ ⋃ j : Haar.PairedSlabIndex N, sourceBadEvent probes s j
    simp only [Set.mem_iUnion, not_exists]
    rintro ⟨block, a | a⟩ <;> cases block
    · exact not_lt.mpr (hq a.1 (Haar.querySlabColumn a) (by simp only [Haar.querySlabColumn]; omega)).1
    · exact not_lt.mpr (hq a.1 (Haar.querySlabColumn a) (by simp only [Haar.querySlabColumn]; omega)).2
    · exact not_lt.mpr hx
    · exact not_lt.mpr hy

/-- The literal simultaneous event is measurable under the source hypotheses. -/
theorem sourceAllSlabs_measurable
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd) :
    MeasurableSet (sourceAllSlabs probes s) := by
  rw [← sourceSlabEvent_eq_sourceAllSlabs]
  exact (MeasurableSet.iUnion (fun i => sourceBadEvent_measurable probes i)).compl

/-- Full source adaptive Haar lemma, with an explicit absolute C=6. Frames
may have different ambient dimensions; the seed is genuinely independent;
source-filtration measurability and a.s. norm bounds suffice. -/
theorem adaptive_haar_source [IsProbabilityMeasure nu]
    (hR : 0 < R) (hs : 0 < s) {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta < 1)
    (probes : AdaptedProbes N dx dy Seed R nu hxd hyd)
    (hdim : 6 * R ^ 2 / s ^ 2 * Real.log ((N + 2 : ℝ) / delta) ≤
      ((min dx dy - (N + 1) : ℕ) : ℝ)) :
    ENNReal.ofReal (1 - delta) ≤
      (((orthogonalHaarProbability dx).prod (orthogonalHaarProbability dy)).prod nu)
        (sourceAllSlabs probes s) := by
  have hlogpos : 0 < Real.log ((N + 2 : ℝ) / delta) := by
    apply Real.log_pos
    apply (lt_div_iff₀ hd0).mpr
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have hdimpos : (0 : ℝ) < ((min dx dy - (N + 1) : ℕ) : ℝ) :=
    (by positivity : 0 < 6 * R ^ 2 / s ^ 2 * Real.log ((N + 2 : ℝ) / delta)).trans_le hdim
  have hm : N + 1 < min dx dy := by
    have hh : 0 < min dx dy - (N + 1) := Nat.cast_pos.mp hdimpos
    omega
  have hxs : N + 1 < dx := hm.trans_le (Nat.min_le_left dx dy)
  have hys : N + 1 < dy := hm.trans_le (Nat.min_le_right dx dy)
  have hlog : Real.log (2 * (((N + 1) * (N + 2) : ℕ) : ℝ) / delta) ≤
      3 * Real.log ((N + 2 : ℝ) / delta) := by
    have h := source_event_log_bound (n := (N + 1 : ℝ)) (by
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      linarith) hd0 hd1
    convert h using 1 <;> push_cast <;> ring_nf
  have hdim' : 2 * R ^ 2 / s ^ 2 *
      Real.log (2 * (((N + 1) * (N + 2) : ℕ) : ℝ) / delta) ≤
      ((min dx dy - (N + 1) : ℕ) : ℝ) := by
    calc
      _ ≤ 2 * R ^ 2 / s ^ 2 * (3 * Real.log ((N + 2 : ℝ) / delta)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = 6 * R ^ 2 / s ^ 2 * Real.log ((N + 2 : ℝ) / delta) := by ring
      _ ≤ _ := hdim
  have hreal : (((N + 1) * (N + 2) : ℕ) : ℝ) *
      Haar.slabTailReal N (min dx dy) R s ≤ delta :=
    Haar.log_dimension_controls_union (by positivity) hR hs hd0 hdim'
  have hsmall : (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s) ≤ ENNReal.ofReal delta := by
    rw [← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg ((N + 1) * (N + 2)))]
    exact ENNReal.ofReal_le_ofReal hreal
  rw [← sourceSlabEvent_eq_sourceAllSlabs]
  calc
    ENNReal.ofReal (1 - delta) = 1 - ENNReal.ofReal delta := by
      rw [ENNReal.ofReal_sub 1 hd0.le]
      simp
    _ ≤ 1 - (((N + 1) * (N + 2) : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (Haar.slabTailReal N (min dx dy) R s) := tsub_le_tsub_left hsmall 1
    _ ≤ _ := sourceSlabEvent_probability hR hs hxs hys probes

end
end MinimaxAudit.HaarSource
