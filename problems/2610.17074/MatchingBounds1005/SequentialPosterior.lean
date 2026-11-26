import MatchingBounds1005.PosteriorGaussian

/-!
# Sequential posterior factorization for static Gaussian parameters

Finite adaptive row protocols retain the unknown vector unchanged between
observations. The corresponding fresh-residual representation is derived by
iterating the actual Gaussian posterior joint-law identity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators InnerProductSpace ENNReal NNReal

namespace MatchingBounds1005.SequentialPosterior
open GaussianVector AdaptiveGaussian GaussianFitter PosteriorGaussian

theorem map_prod_right {A B H S : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace S] (P : Measure A) (Q : Measure B)
    [SFinite P] [SFinite Q] (f : A → H) (hf : Measurable f)
    (g : H × B → S) (hg : Measurable g) :
    ((P.map f).prod Q).map g = (P.prod Q).map (fun p => g (f p.1, p.2)) := by
  have hp : MeasurePreserving f P (P.map f) := ⟨hf, rfl⟩
  rw [← (hp.prod (MeasurePreserving.id Q)).map_eq,
    Measure.map_map hg (hf.prodMap measurable_id)]
  rfl

theorem fitter_mem_span {d T : ℕ} (rows : Fin T → Vec d) (y : Fin T → ℝ) :
    fitter rows y ∈ Submodule.span ℝ (Set.range rows) := by
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [← span_gramSchmidt ℝ rows]
  exact Submodule.subset_span ⟨i, rfl⟩

attribute [local irreducible] projection fitter Submodule.span

theorem measurable_complement {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (V : Ω → Submodule ℝ (Vec d))
    (hV : Measurable (fun p : Ω × Vec d => projection (V p.1) p.2)) :
    Measurable (fun p : Ω × Vec d => projection (V p.1)ᗮ p.2) := by
  have heq : (fun p : Ω × Vec d => projection (V p.1)ᗮ p.2) =
      fun p => p.2 - projection (V p.1) p.2 := by
    funext p
    exact projection_orthogonal_eq_sub (V p.1) p.2
  rw [heq]
  exact measurable_snd.sub hV

/-- The exact one-step posterior is a product with a genuinely independent
fresh Gaussian seed over the new raw-response history law. -/
theorem posterior_step_factorization {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}
    (ν : Measure Ω) [SFinite ν] (V : Ω → Submodule ℝ (Vec d))
    (hV : Measurable (fun p : Ω × Vec d => projection (V p.1) p.2))
    (rows : Ω → Fin T → Vec d) (hrows : ∀ i, Measurable (fun h => rows h i))
    (hVK : ∀ h, V h ≤ Submodule.span ℝ (Set.range (rows h)))
    (m : Ω → Vec d) (hm : Measurable m) (hmV : ∀ h, m h ∈ V h) (σ : ℝ) :
    let state := fun h z => m h + σ • projection (V h)ᗮ z
    let observe := fun p : Ω × Vec d => (p.1, rowResponse (rows p.1) (state p.1 p.2))
    (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) =
      (((ν.prod (standardGaussian d)).map observe).prod (standardGaussian d)).map
        (fun p => (p.1, fitter (rows p.1.1) p.1.2 +
          σ • projection (Submodule.span ℝ (Set.range (rows p.1.1)))ᗮ p.2)) := by
  dsimp only
  let state := fun h z => m h + σ • projection (V h)ᗮ z
  let observe := fun p : Ω × Vec d => (p.1, rowResponse (rows p.1) (state p.1 p.2))
  let g := fun p : (Ω × (Fin T → ℝ)) × Vec d =>
    (p.1, fitter (rows p.1.1) p.1.2 +
      σ • projection (Submodule.span ℝ (Set.range (rows p.1.1)))ᗮ p.2)
  have hs : Measurable (Function.uncurry state) :=
    (hm.comp measurable_fst).add (measurable_const.smul (measurable_complement V hV))
  have ho : Measurable observe :=
    measurable_fst.prodMk ((measurable_rowResponse_family rows hrows).comp
      (measurable_fst.prodMk hs))
  have hfit : Measurable (fun h : Ω × (Fin T → ℝ) => fitter (rows h.1) h.2) :=
    measurable_fitter (fun h : Ω × (Fin T → ℝ) => rows h.1) (fun h => h.2)
      (fun i => (hrows i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  have hnew : Measurable (fun p : (Ω × (Fin T → ℝ)) × Vec d =>
      projection (Submodule.span ℝ (Set.range (rows p.1.1)))ᗮ p.2) :=
    (measurable_complement (fun h => Submodule.span ℝ (Set.range (rows h)))
      (measurable_spanProjection rows hrows)).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable g := measurable_fst.prodMk
    ((hfit.comp measurable_fst).add (measurable_const.smul hnew))
  have hleft : Measurable (fun p : Ω × (Vec d × Vec d) =>
      g (observe (p.1, p.2.1), p.2.2)) := by
    apply hg.comp
    exact (ho.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have heq := (latent_posterior_joint ν V hV rows hrows hVK m hm hmV σ).symm
  change (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) = _
  calc
    (ν.prod (standardGaussian d)).map (fun p => (observe p, state p.1 p.2)) =
        (ν.prod ((standardGaussian d).prod (standardGaussian d))).map
          (fun p => g (observe (p.1, p.2.1), p.2.2)) := heq
    _ = ((ν.prod (standardGaussian d)).prod (standardGaussian d)).map
        (fun p => g (observe p.1, p.2)) := by
      rw [← Measure.prodAssoc_prod, Measure.map_map hleft MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := (map_prod_right (ν.prod (standardGaussian d)) (standardGaussian d)
      observe ho g hg).symm

/-- Histories retain the initial independent seed and every complete raw
row response. A row protocol may pad its accumulated rows with zeros. -/
def History (Ω : Type*) (T : ℕ) : ℕ → Type _
  | 0 => Ω
  | n + 1 => History Ω T n × (Fin T → ℝ)

instance historyMeasurableSpace (Ω : Type*) [MeasurableSpace Ω] (T n : ℕ) :
    MeasurableSpace (History Ω T n) :=
  match n with
  | 0 => inferInstanceAs (MeasurableSpace Ω)
  | n + 1 =>
      letI := historyMeasurableSpace Ω T n
      inferInstanceAs (MeasurableSpace (History Ω T n × (Fin T → ℝ)))

variable {Ω : Type*} [MeasurableSpace Ω] {d T : ℕ}

def exposure (rows : (n : ℕ) → History Ω T n → Fin T → Vec d) :
    (n : ℕ) → History Ω T n → Submodule ℝ (Vec d)
  | 0, _ => ⊥
  | n + 1, h => Submodule.span ℝ (Set.range (rows n h.1))

def fittedMean (rows : (n : ℕ) → History Ω T n → Fin T → Vec d) :
    (n : ℕ) → History Ω T n → Vec d
  | 0, _ => 0
  | n + 1, h => fitter (rows n h.1) h.2

/-- Purely deterministic protocol requirements: measurable adaptive rows,
and retention of all previously exposed row directions. No probabilistic
posterior or information bound is a field of this structure. -/
structure RowProtocol (Ω : Type*) [MeasurableSpace Ω] (d T : ℕ) where
  rows : (n : ℕ) → History Ω T n → Fin T → Vec d
  measurable_rows : ∀ n i, Measurable (fun h => rows n h i)
  nested : ∀ n h, exposure rows n h ≤ Submodule.span ℝ (Set.range (rows n h))

theorem measurable_exposure (R : RowProtocol Ω d T) (n : ℕ) :
    Measurable (fun p : History Ω T n × Vec d => projection (exposure R.rows n p.1) p.2) := by
  cases n with
  | zero => exact (projection (⊥ : Submodule ℝ (Vec d))).continuous.measurable.comp measurable_snd
  | succ n =>
      exact (measurable_spanProjection (R.rows n) (R.measurable_rows n)).comp
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem measurable_fittedMean (R : RowProtocol Ω d T) (n : ℕ) :
    Measurable (fittedMean R.rows n) := by
  cases n with
  | zero => exact measurable_const
  | succ n =>
      exact measurable_fitter (fun h : History Ω T n × (Fin T → ℝ) => R.rows n h.1)
        (fun h => h.2)
        (fun i => (R.measurable_rows n i).comp measurable_fst)
        (fun i => (measurable_pi_apply i).comp measurable_snd)

theorem fittedMean_mem (R : RowProtocol Ω d T) (n : ℕ) (h : History Ω T n) :
    fittedMean R.rows n h ∈ exposure R.rows n h := by
  cases n with
  | zero => exact Submodule.zero_mem _
  | succ n => exact fitter_mem_span (R.rows n h.1) h.2

def latent (R : RowProtocol Ω d T) (σ : ℝ) (n : ℕ) (p : History Ω T n × Vec d) : Vec d :=
  fittedMean R.rows n p.1 + σ • projection (exposure R.rows n p.1)ᗮ p.2

theorem measurable_latent (R : RowProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (latent R σ n) :=
  ((measurable_fittedMean R n).comp measurable_fst).add
    (measurable_const.smul (measurable_complement (exposure R.rows n) (measurable_exposure R n)))

def observe (R : RowProtocol Ω d T) (σ : ℝ) (n : ℕ)
    (p : History Ω T n × Vec d) : History Ω T (n + 1) :=
  (p.1, rowResponse (R.rows n p.1) (latent R σ n p))

theorem measurable_observe (R : RowProtocol Ω d T) (σ : ℝ) (n : ℕ) :
    Measurable (observe R σ n) :=
  measurable_fst.prodMk ((measurable_rowResponse_family (R.rows n) (R.measurable_rows n)).comp
    (measurable_fst.prodMk (measurable_latent R σ n)))

/-- History law generated using an independent Gaussian seed at every step. -/
def freshHistoryLaw (R : RowProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) :
    (n : ℕ) → Measure (History Ω T n)
  | 0 => ν₀
  | n + 1 => ((freshHistoryLaw R σ ν₀ n).prod (standardGaussian d)).map (observe R σ n)

instance freshHistoryLaw_probability (R : RowProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    IsProbabilityMeasure (freshHistoryLaw R σ ν₀ n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure ν₀)
  | succ n ih =>
      letI := ih
      exact isProbabilityMeasure_map (measurable_observe R σ n).aemeasurable

def representedLaw (R : RowProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) (n : ℕ) :
    Measure (History Ω T n × Vec d) :=
  ((freshHistoryLaw R σ ν₀ n).prod (standardGaussian d)).map
    (fun p => (p.1, latent R σ n p))

def staticUpdate (R : RowProtocol Ω d T) (n : ℕ) (p : History Ω T n × Vec d) :
    History Ω T (n + 1) × Vec d := ((p.1, rowResponse (R.rows n p.1) p.2), p.2)

theorem measurable_staticUpdate (R : RowProtocol Ω d T) (n : ℕ) :
    Measurable (staticUpdate R n) :=
  (measurable_fst.prodMk
    (measurable_rowResponse_family (R.rows n) (R.measurable_rows n))).prodMk measurable_snd

/-- The genuine static experiment: the unknown vector is copied unchanged
at every update, and each new response is evaluated at that same vector. -/
def staticJointLaw (R : RowProtocol Ω d T) (σ : ℝ) (ν₀ : Measure Ω) :
    (n : ℕ) → Measure (History Ω T n × Vec d)
  | 0 => representedLaw R σ ν₀ 0
  | n + 1 => (staticJointLaw R σ ν₀ n).map (staticUpdate R n)

theorem latent_zero (R : RowProtocol Ω d T) (σ : ℝ) (p : Ω × Vec d) :
    latent R σ 0 p = σ • p.2 := by
  simp [latent, fittedMean, exposure, projection]
  exact congrArg (fun x : Vec d => σ • x)
    (Submodule.orthogonalProjection_eq_self_iff.mpr
      (show p.2 ∈ (⊤ : Submodule ℝ (Vec d)) from trivial))

/-- The static experiment starts from an actual independent centered
Gaussian parameter with noise scale `σ`. -/
theorem staticJointLaw_zero (R : RowProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [SFinite ν₀] :
    staticJointLaw R σ ν₀ 0 =
      ν₀.prod ((standardGaussian d).map (fun z => σ • z)) := by
  rw [staticJointLaw, representedLaw, freshHistoryLaw]
  simp_rw [latent_zero]
  have hp := Measure.map_prod_map ν₀ (standardGaussian d) measurable_id
    (show Measurable (fun z : Vec d => σ • z) from by fun_prop)
  simp only [Measure.map_id] at hp
  exact hp.symm

/-- Full finite adaptive posterior factorization, proved by induction from
the actual static experiment. The hypotheses are solely protocol
measurability, nested row spans, and an independent initial seed. -/
theorem staticJointLaw_eq_represented (R : RowProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    staticJointLaw R σ ν₀ n = representedLaw R σ ν₀ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [staticJointLaw, ih, representedLaw,
        Measure.map_map (measurable_staticUpdate R n)
          (measurable_fst.prodMk (measurable_latent R σ n))]
      have hp := posterior_step_factorization (freshHistoryLaw R σ ν₀ n)
        (exposure R.rows n) (measurable_exposure R n) (R.rows n) (R.measurable_rows n)
        (R.nested n) (fittedMean R.rows n) (measurable_fittedMean R n) (fittedMean_mem R n) σ
      simpa only [staticUpdate, representedLaw, freshHistoryLaw, observe, latent,
        fittedMean, exposure, Function.comp_def] using hp

/-- The fresh-history law is exactly the marginal of the static transcript,
so residual resampling does not alter any finite raw-response transcript. -/
theorem static_history_law (R : RowProtocol Ω d T) (σ : ℝ)
    (ν₀ : Measure Ω) [IsProbabilityMeasure ν₀] (n : ℕ) :
    (staticJointLaw R σ ν₀ n).map Prod.fst = freshHistoryLaw R σ ν₀ n := by
  rw [staticJointLaw_eq_represented, representedLaw,
    Measure.map_map measurable_fst (measurable_fst.prodMk (measurable_latent R σ n))]
  change (((freshHistoryLaw R σ ν₀ n).prod (standardGaussian d)).map Prod.fst) = _
  simp

end MatchingBounds1005.SequentialPosterior
