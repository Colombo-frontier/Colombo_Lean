import MatchingBounds1005.ScheduledContainment
import MatchingBounds1005.GaussianVector
import RandomizedFO2003.SphereUniqueness

/-!
# Independent Gaussian starts for the exact scheduled Haar representation

The Gaussian direction law is proved from the independent-coordinate Gaussian
law and its orthogonal invariance. Product-map preservation then replaces all
ambient sphere starts by normalized genuine Gaussian starts. Their cyclic
spans agree pointwise, so normalization introduces no containment assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open RandomizedFO2003 RandomizedFO2003.Rotations RandomizedFO2003.Spherical
open MatchingBounds1005.GaussianVector MatchingBounds1005.ScheduledHaar

namespace MatchingBounds1005.GaussianHaar

universe u v

theorem gaussian_ae_ne_zero {dim : ℕ} (hdim : 0 < dim) :
    ∀ᵐ x ∂standardGaussian dim, x ≠ 0 := by
  simpa only [ae_iff, not_not, Set.setOf_eq_eq_singleton] using
    standardGaussian_singleton hdim (0 : Vec dim)

/-- Normalizing a genuine standard Gaussian gives exactly the concrete sphere law. -/
theorem gaussian_radial_law {dim : ℕ} (hdim : 0 < dim) :
    (standardGaussian dim).map (radial (Vec dim)) = sphereLaw (Vec dim) := by
  letI : Nonempty (Fin dim) := ⟨⟨0, hdim⟩⟩
  letI : IsProbabilityMeasure ((standardGaussian dim).map (radial (Vec dim))) :=
    isProbabilityMeasure_map (measurable_radial (Vec dim)).aemeasurable
  apply sphereLaw_unique (Vec dim)
  · apply (ae_map_iff (measurable_radial (Vec dim)).aemeasurable
      (isClosed_eq continuous_norm continuous_const).measurableSet).2
    filter_upwards [gaussian_ae_ne_zero hdim] with x hx
    exact radial_norm (Vec dim) hx
  · intro U
    refine ⟨U.continuous.measurable, ?_⟩
    rw [Measure.map_map U.continuous.measurable (measurable_radial (Vec dim))]
    have hc : (U : Vec dim → Vec dim) ∘ radial (Vec dim) =
        radial (Vec dim) ∘ U := by
      funext x
      exact (radial_commutes (Vec dim) U x).symm
    rw [hc, ← Measure.map_map (measurable_radial (Vec dim)) U.continuous.measurable,
      standardGaussian_map_isometry]

theorem gaussian_radial_preserving {dim : ℕ} (hdim : 0 < dim) :
    MeasurePreserving (radial (Vec dim)) (standardGaussian dim) (sphereLaw (Vec dim)) :=
  ⟨measurable_radial _, gaussian_radial_law hdim⟩

/-- Independent Gaussian pairs, in the same chronological storage as the
actual ambient exposure construction. -/
def gaussianPairLaw (dim : ℕ) : (n : ℕ) → {H : Type u} → [MeasurableSpace H] →
    Measure H → Measure (AmbientPairHistory (Vec dim) n H)
  | 0, _, _, μ => μ
  | n + 1, _, _, μ => gaussianPairLaw dim n ((μ.prod (standardGaussian dim)).prod (standardGaussian dim))

instance gaussianPairLaw_sFinite (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] : SFinite (gaussianPairLaw dim n μ) := by
  induction n generalizing H with
  | zero => exact inferInstanceAs (SFinite μ)
  | succ n ih => exact ih _

instance gaussianPairLaw_probability (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [IsProbabilityMeasure μ] : IsProbabilityMeasure (gaussianPairLaw dim n μ) := by
  induction n generalizing H with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih => exact ih _

def normalizePairs (dim : ℕ) : (n : ℕ) → {H : Type u} →
    AmbientPairHistory (Vec dim) n H → AmbientPairHistory (Vec dim) n H
  | 0, _, p => p
  | n + 1, _, p => AmbientPairHistory.map (Vec dim) n
      (Prod.map (Prod.map id (radial (Vec dim))) (radial (Vec dim)))
      (normalizePairs dim n p)

theorem normalizePairs_preserving {dim : ℕ} (hdim : 0 < dim) (n : ℕ)
    {H : Type u} [MeasurableSpace H] (μ : Measure H) [SFinite μ] :
    MeasurePreserving (normalizePairs dim n)
      (gaussianPairLaw dim n μ) (ambientPairHistoryLaw (Vec dim) n μ) := by
  induction n generalizing H with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    exact (AmbientPairHistory.map_preserving n _ _ _
      (((MeasurePreserving.id μ).prod (gaussian_radial_preserving hdim)).prod
        (gaussian_radial_preserving hdim))).comp (ih _)

@[simp] theorem seed_normalizePairs (dim n : ℕ) {H : Type u}
    (p : AmbientPairHistory (Vec dim) n H) :
    AmbientPairHistory.seed (Vec dim) n (normalizePairs dim n p) =
      AmbientPairHistory.seed (Vec dim) n p := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih =>
    simp only [normalizePairs, AmbientPairHistory.seed, AmbientPairHistory.seed_map,
      Prod.map_apply, id_eq, ih]
    rfl

theorem pairs_normalizePairs (dim n : ℕ) {H : Type u}
    (p : AmbientPairHistory (Vec dim) n H) (i : Fin n) :
    AmbientPairHistory.pairs (Vec dim) n (normalizePairs dim n p) i =
      Prod.map (radial (Vec dim)) (radial (Vec dim)) (AmbientPairHistory.pairs (Vec dim) n p i) := by
  induction n generalizing H with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [normalizePairs, AmbientPairHistory.pairs, Fin.cons_zero,
        AmbientPairHistory.seed_map, seed_normalizePairs, Prod.map_apply, id_eq]
      rfl
    · simp only [normalizePairs, AmbientPairHistory.pairs, Fin.cons_succ,
        AmbientPairHistory.pairs_map, ih]

theorem starts_normalizePairs (dim n : ℕ) {H : Type u}
    (p : AmbientPairHistory (Vec dim) n H) (i : Fin (n + n)) :
    AmbientPairHistory.starts (Vec dim) n (normalizePairs dim n p) i =
      radial (Vec dim) (AmbientPairHistory.starts (Vec dim) n p i) := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [AmbientPairHistory.starts, Fin.append_left, pairs_normalizePairs, Prod.map_apply]
    rfl
  · simp only [AmbientPairHistory.starts, Fin.append_right, pairs_normalizePairs, Prod.map_apply]
    rfl

/-- Normalization changes no polynomially generated subspace, even at zero. -/
theorem cyclicSpan_radial {dim m : ℕ} (Q : Vec dim →L[ℝ] Vec dim) (g : Fin m → Vec dim) :
    cyclicSpan Q (fun i => radial (Vec dim) (g i)) = cyclicSpan Q g := by
  have hscale (a : Fin m → Vec dim) (c : Fin m → ℝ) :
      cyclicSpan Q (fun i => c i • a i) ≤ cyclicSpan Q a := by
    apply Submodule.span_le.mpr
    rintro v ⟨⟨j, i⟩, rfl⟩
    change (Q.toLinearMap ^ j) (c i • a i) ∈ cyclicSpan Q a
    rw [map_smul]
    exact (cyclicSpan Q a).smul_mem _ (Submodule.subset_span ⟨(j, i), rfl⟩)
  apply le_antisymm (hscale g (fun i => ‖g i‖⁻¹))
  have hr (x : Vec dim) : ‖x‖ • radial (Vec dim) x = x := by
    by_cases hx : x = 0
    · simp [hx, radial]
    · simp [radial, smul_smul, norm_ne_zero_iff.mpr hx]
  simpa only [hr] using hscale (fun i => radial (Vec dim) (g i)) (fun i => ‖g i‖)

theorem cyclicSpan_normalizePairs {dim : ℕ} (n : ℕ) {H : Type u}
    (Q : Vec dim →L[ℝ] Vec dim) (p : AmbientPairHistory (Vec dim) n H) :
    cyclicSpan Q (AmbientPairHistory.starts (Vec dim) n (normalizePairs dim n p)) =
      cyclicSpan Q (AmbientPairHistory.starts (Vec dim) n p) := by
  have hfun := funext (starts_normalizePairs dim n p)
  rw [hfun]
  exact cyclicSpan_radial Q _

theorem gaussian_seed_preserving (dim n : ℕ) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ] :
    MeasurePreserving (AmbientPairHistory.seed (Vec dim) n) (gaussianPairLaw dim n μ) μ := by
  induction n generalizing H with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hfst : MeasurePreserving (Prod.fst : H × Vec dim → H) (μ.prod (standardGaussian dim)) μ :=
      ⟨measurable_fst, by simp⟩
    have hfst' : MeasurePreserving (Prod.fst : (H × Vec dim) × Vec dim → H × Vec dim)
        ((μ.prod (standardGaussian dim)).prod (standardGaussian dim)) (μ.prod (standardGaussian dim)) :=
      ⟨measurable_fst, by simp⟩
    exact (hfst.comp hfst').comp (ih _)

theorem gaussian_pairs_ae_ne_zero {dim : ℕ} (hdim : 0 < dim) (n : ℕ)
    {H : Type u} [MeasurableSpace H] (μ : Measure H) [SFinite μ] :
    ∀ᵐ p ∂gaussianPairLaw dim n μ, ∀ i : Fin n,
      (AmbientPairHistory.pairs (Vec dim) n p i).1 ≠ 0 ∧
        (AmbientPairHistory.pairs (Vec dim) n p i).2 ≠ 0 := by
  induction n generalizing H with
  | zero => exact ae_of_all _ (fun _ i => i.elim0)
  | succ n ih =>
    have hfirst : ∀ᵐ p ∂(μ.prod (standardGaussian dim)).prod (standardGaussian dim),
        p.1.2 ≠ 0 ∧ p.2 ≠ 0 := by
      have ha := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := standardGaussian dim)).ae
        (gaussian_ae_ne_zero hdim)
      have hb := (Measure.quasiMeasurePreserving_fst (μ := μ.prod (standardGaussian dim))
        (ν := standardGaussian dim)).ae ha
      have hc := (Measure.quasiMeasurePreserving_snd (μ := μ.prod (standardGaussian dim))
        (ν := standardGaussian dim)).ae (gaussian_ae_ne_zero hdim)
      filter_upwards [hb, hc] with p hp hq
      exact ⟨hp, hq⟩
    have hhead := (gaussian_seed_preserving dim n
      ((μ.prod (standardGaussian dim)).prod (standardGaussian dim))).quasiMeasurePreserving.ae hfirst
    filter_upwards [hhead, ih ((μ.prod (standardGaussian dim)).prod (standardGaussian dim))]
      with p hp htail
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [AmbientPairHistory.pairs, Fin.cons_zero] using hp
    · simpa only [AmbientPairHistory.pairs, Fin.cons_succ] using htail j

/-- All finitely many original independent Gaussian starts are nonzero a.e. -/
theorem gaussian_starts_ae_ne_zero {dim : ℕ} (hdim : 0 < dim) (n : ℕ)
    {H : Type u} [MeasurableSpace H] (μ : Measure H) [SFinite μ] :
    ∀ᵐ p ∂gaussianPairLaw dim n μ, ∀ i : Fin (n + n),
      AmbientPairHistory.starts (Vec dim) n p i ≠ 0 := by
  filter_upwards [gaussian_pairs_ae_ne_zero hdim n μ] with p hp
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [AmbientPairHistory.starts, Fin.append_left] using (hp j).1
  · simpa only [AmbientPairHistory.starts, Fin.append_right] using (hp j).2

/-- Exact one-Haar scheduled transcript law and chronological containment,
with genuine independent Gaussian starts and an unqueried source candidate.
The schedule inputs mention only deterministic canonical subspaces. -/
theorem source_haar_gaussian_containment (w : List SourceKind) (d : ℕ)
    (hdim : 0 < d + actionCount w.length) {H : Type u} [MeasurableSpace H]
    (μ : Measure H) [SFinite μ]
    (Q : Vec (d + actionCount w.length) →L[ℝ] Vec (d + actionCount w.length))
    (plan : SourcePolicy (E := Vec (d + actionCount w.length)) w H)
    (I : ℕ → Submodule ℝ (Vec (d + actionCount w.length)))
    (hmono : ∀ t, I t ≤ I (t + 1)) (hschedule : plan.Scheduled Q w I) :
    (μ.prod (haarLaw (Vec (d + actionCount w.length)))).map
      (fun p => plan.run w Q (p.2 : Vec (d + actionCount w.length) →L[ℝ]
        Vec (d + actionCount w.length)) p.1) =
      (gaussianPairLaw (d + actionCount w.length) (actionCount w.length) μ).map
        (fun p => plan.decode w (((plan.compile w).compile Q w.length).directAmbientTranscript
          d (actionCount w.length) (fun _ => .initial) id
            (normalizePairs (d + actionCount w.length) (actionCount w.length) p))) ∧
    (∀ᵐ p ∂gaussianPairLaw (d + actionCount w.length) (actionCount w.length) μ,
      ChronologicalIn I
        (cyclicSpan Q (AmbientPairHistory.starts (Vec (d + actionCount w.length))
          (actionCount w.length) p))
        (((plan.compile w).compile Q w.length).selectQueries (actionCount w.length)
          (((plan.compile w).compile Q w.length).directAmbientTranscript d (actionCount w.length)
            (fun _ => .initial) id
              (normalizePairs (d + actionCount w.length) (actionCount w.length) p)))) := by
  have hr := plan.haar_ambient_containment w d μ Q I hmono hschedule
  have hn := normalizePairs_preserving hdim (actionCount w.length) μ
  constructor
  · have htr := (((plan.compile w).compile Q w.length).haar_ambient_information
      d (actionCount w.length) μ).1
    have hdec := plan.decode_measurable w
    have hm : Measurable (fun p => plan.decode w
      (((plan.compile w).compile Q w.length).directAmbientTranscript
        d (actionCount w.length) (fun _ => .initial) id p)) := hdec.comp htr
    have hp := congrArg (fun ν => ν.map (fun p => plan.decode w
      (((plan.compile w).compile Q w.length).directAmbientTranscript
        d (actionCount w.length) (fun _ => .initial) id p))) hn.map_eq
    dsimp only at hp
    rw [Measure.map_map hm hn.measurable] at hp
    exact hr.1.trans hp.symm
  · have hp := hn.quasiMeasurePreserving.ae hr.2
    simpa only [cyclicSpan_normalizePairs] using hp

end MatchingBounds1005.GaussianHaar
