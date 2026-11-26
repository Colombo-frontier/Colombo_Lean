import Matvec.MeasurableGameReduction
import Matvec.PolicyOracleMap
import Matvec.HomogeneousSourcePolicy
import Matvec.SourceMatrixGeometry
import Matvec.SimplexNormalization
import Matvec.FiniteMixtureSuccess

/-!
# Actual successful game algorithms yield measurable source-solving policies

The input right-hand side is public and belongs to the policy input, while
the random seed law stays independent of that input and the unknown source
matrix. The compiler preserves every off-promise transcript and uses `2*T`
ordinary source calls. Probability statements below concern the actual
`Model.Solves` algorithms and the actual compiled runs.
-/

namespace Matvec.GameSourceSolver
open Matrix MeasureTheory MeasurableSimulation SourceIterationPolicy
open scoped Matrix Classical
noncomputable section

local instance matrixMeasurable (a b : Type*) : MeasurableSpace (Matrix a b ℝ) :=
  inferInstanceAs (MeasurableSpace (a → b → ℝ))

section Coordinates
variable {d : Type*} [Fintype d] {Seed : Type*} [MeasurableSpace Seed]
  {m n T : ℕ}

abbrev Euclidean (d : Type*) [Fintype d] := EuclideanSpace ℝ d

def fromCoordinates : (d → ℝ) → Euclidean d := (WithLp.equiv 2 _).symm
def toCoordinates : Euclidean d → (d → ℝ) := WithLp.equiv 2 _

theorem measurable_fromCoordinates : Measurable (fromCoordinates (d := d)) :=
  (PiLp.continuous_equiv_symm 2 _).measurable

theorem measurable_toCoordinates : Measurable (toCoordinates (d := d)) :=
  (PiLp.continuous_equiv 2 _).measurable

theorem coordinate_oracle (H : Matrix d d ℝ) :
    toCoordinates ∘ euclideanMatrixMap H ∘ fromCoordinates = H.mulVec := rfl

def sourcePolicy (alg : Policy (Query m n) (Reply m n) (Query m n) T Seed)
    (sim : TwoCallMap (Query m n) (Reply m n) (d → ℝ) (d → ℝ) Seed)
    (recover : Seed → Query m n → Euclidean d)
    (hr : Measurable (fun p : Seed × Query m n => recover p.1 p.2)) :
    Policy (Euclidean d) (Euclidean d) (Euclidean d) (2 * T) Seed :=
  ((compile alg sim).toPolicy.mapOracle fromCoordinates toCoordinates
    measurable_fromCoordinates measurable_toCoordinates).mapOutput recover hr

theorem sourcePolicy_run (alg : Policy (Query m n) (Reply m n) (Query m n) T Seed)
    (sim : TwoCallMap (Query m n) (Reply m n) (d → ℝ) (d → ℝ) Seed)
    (recover : Seed → Query m n → Euclidean d)
    (hr : Measurable (fun p : Seed × Query m n => recover p.1 p.2))
    (H : Matrix d d ℝ) (target : Seed → Query m n → Reply m n)
    (hsim : ∀ seed q, sim.combine seed q
      (H *ᵥ (sim.first seed q), H *ᵥ (sim.second seed q (H *ᵥ (sim.first seed q)))) =
        target seed q) (seed : Seed) :
    (sourcePolicy alg sim recover hr).run (euclideanMatrixMap H) seed =
      recover seed (alg.run (target seed) seed) := by
  rw [sourcePolicy, Policy.mapOutput_run, Policy.mapOracle_run, coordinate_oracle,
    PairedPolicy.toPolicy_run, compile_run alg sim H.mulVec target hsim]

end Coordinates

section Ball
variable {d m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def ballBeta (κ : ℝ) : ℝ := 1 / (4 * κ)
def ballAlpha (d : ℕ) (κ : ℝ) : ℝ := ballBeta κ / (8 * Real.sqrt d)
def ballAccuracy (d : ℕ) (κ : ℝ) : ℝ := ballAlpha d κ / 16

def ballUnitPolicy (alg : Algorithm m n T Seed)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit)) (κ : ℝ) :
    Policy (Euclidean (Fin d)) (Euclidean (Fin d)) (Euclidean (Fin d)) (2 * T)
      (Euclidean (Fin d) × Seed) :=
  sourcePolicy ((ofAlgorithm alg).seedMap Prod.snd measurable_snd)
    (finBallMap er ec (fun p : Euclidean (Fin d) × Seed => toCoordinates p.1)
      (ballAlpha d κ) (ballBeta κ) (measurable_toCoordinates.comp measurable_fst))
    (fun _ out => fromCoordinates (ballRecovery ec out))
    (measurable_fromCoordinates.comp ((measurable_ballRecovery ec).comp measurable_snd))

theorem ballUnitPolicy_run (alg : Algorithm m n T Seed)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit)) (κ : ℝ)
    (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose = H)
    (b : Euclidean (Fin d)) (seed : Seed) :
    (ballUnitPolicy alg er ec κ).run (euclideanMatrixMap H) (b, seed) =
      let out := alg.run (modelBallMatrix H b (ballAlpha d κ) (ballBeta κ) er ec) seed
      (decodeBallScalar ec out.1)⁻¹ • decodeBallVector ec out.1 := by
  have hsim := finBallMap_correct H hH er ec
    (fun p : Euclidean (Fin d) × Seed => toCoordinates p.1)
    (ballAlpha d κ) (ballBeta κ) (measurable_toCoordinates.comp measurable_fst)
  have hrun := sourcePolicy_run
    ((ofAlgorithm alg).seedMap Prod.snd measurable_snd)
    (finBallMap er ec (fun p : Euclidean (Fin d) × Seed => toCoordinates p.1)
      (ballAlpha d κ) (ballBeta κ) (measurable_toCoordinates.comp measurable_fst))
    (fun (_ : Euclidean (Fin d) × Seed) (out : Query m n) =>
      fromCoordinates (ballRecovery ec out))
    (measurable_fromCoordinates.comp ((measurable_ballRecovery ec).comp measurable_snd)) H
    (fun p => oracle (modelBallMatrix H p.1 (ballAlpha d κ) (ballBeta κ) er ec))
    hsim (b, seed)
  rw [Policy.seedMap_run, ofAlgorithm_run] at hrun
  calc
    _ = fromCoordinates (ballRecovery ec
      (alg.run (modelBallMatrix H b (ballAlpha d κ) (ballBeta κ) er ec) seed)) := hrun
    _ = _ := ?_
  ext i
  rfl

theorem ballUnitPolicy_success (alg : Algorithm m n T Seed)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit))
    (κ : ℝ) (hκ : 1 ≤ κ) (hd : 0 < d)
    (hsolve : Solves alg μ .ballSimplex (ballAccuracy d κ))
    (H : Matrix (Fin d) (Fin d) ℝ) (hsymm : H.transpose = H)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hnorm : ‖euclideanMatrixMap H‖ ≤ κ)
    (b : Euclidean (Fin d)) (hb : ‖b‖ ≤ 1) :
    (2 / 3 : ℝ) ≤ μ.real {seed |
      ‖euclideanMatrixMap H ((ballUnitPolicy alg er ec κ).run (euclideanMatrixMap H) (b, seed)) - b‖
        ≤ 1 / 2} := by
  have hadm := modelBallMatrix_admissible hd H hsymm b hb κ (ballAlpha d κ) (ballBeta κ)
    hκ rfl rfl hnorm er ec
  have hs := hsolve (modelBallMatrix H b (ballAlpha d κ) (ballBeta κ) er ec) hadm
  apply hs.trans
  refine measureReal_mono (fun seed hseed => ?_) (measure_ne_top _ _)
  dsimp only [Set.mem_setOf_eq] at hseed ⊢
  rw [ballUnitPolicy_run alg er ec κ H hsymm]
  have hβ : 0 < ballBeta κ := by unfold ballBeta; positivity
  exact (gameSuccess_ball_residual hd H b (ballAlpha d κ) (ballBeta κ) hβ rfl er ec
    hH hb _ hseed).2.le

def ballSourcePolicy (alg : Algorithm m n T Seed)
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit)) (κ : ℝ) :=
  homogeneousPolicy (ballUnitPolicy alg er ec κ)

theorem ballSourcePolicy_success (alg : Algorithm m n T Seed)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (er : Fin m ≃ (Fin d ⊕ Fin d)) (ec : Fin n ≃ (Fin d ⊕ Unit))
    (κ : ℝ) (hκ : 1 ≤ κ) (hd : 0 < d)
    (hsolve : Solves alg μ .ballSimplex (ballAccuracy d κ))
    (H : Matrix (Fin d) (Fin d) ℝ) (hsymm : H.transpose = H)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hnorm : ‖euclideanMatrixMap H‖ ≤ κ)
    (b : Euclidean (Fin d)) :
    (3 / 5 : ℝ) ≤ μ.real {seed |
      ‖euclideanMatrixMap H ((ballSourcePolicy alg er ec κ).run (euclideanMatrixMap H) (b, seed)) - b‖
        ≤ ‖b‖ / 2} := by
  apply (show (3 / 5 : ℝ) ≤ 2 / 3 by norm_num).trans
  exact homogeneousPolicy_success μ (ballUnitPolicy alg er ec κ) (euclideanMatrixMap H)
    (2 / 3) (by norm_num)
    (fun r hr => ballUnitPolicy_success alg μ er ec κ hκ hd hsolve H hsymm hH hnorm r hr.le) b

end Ball

section ReindexMap
variable {d ι κ : Type*} [Fintype d] [Fintype ι] [Fintype κ]
  {m n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def reindexMap (er : Fin m ≃ ι) (ec : Fin n ≃ κ)
    (sim : TwoCallMap ((κ → ℝ) × (ι → ℝ)) ((ι → ℝ) × (κ → ℝ))
      (d → ℝ) (d → ℝ) Seed) :
    TwoCallMap (Query m n) (Reply m n) (d → ℝ) (d → ℝ) Seed where
  first seed q := sim.first seed (reindexQuery er ec q)
  second seed q r := sim.second seed (reindexQuery er ec q) r
  combine seed q r := reindexReply er ec (sim.combine seed (reindexQuery er ec q) r)
  first_measurable := sim.first_measurable.comp
    (measurable_fst.prodMk ((measurable_reindexQuery er ec).comp measurable_snd))
  second_measurable := sim.second_measurable.comp
    (measurable_fst.prodMk
      (((measurable_reindexQuery er ec).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  combine_measurable := (measurable_reindexReply er ec).comp
    (sim.combine_measurable.comp
      (measurable_fst.prodMk
        (((measurable_reindexQuery er ec).comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))))

theorem reindexMap_correct (er : Fin m ≃ ι) (ec : Fin n ≃ κ)
    (sim : TwoCallMap ((κ → ℝ) × (ι → ℝ)) ((ι → ℝ) × (κ → ℝ))
      (d → ℝ) (d → ℝ) Seed) (H : Matrix d d ℝ) (A : Seed → Matrix ι κ ℝ)
    (hsim : ∀ seed q, sim.combine seed q
      (H *ᵥ (sim.first seed q), H *ᵥ (sim.second seed q (H *ᵥ (sim.first seed q)))) =
        matrixOracle (A seed) q) (seed : Seed) (q : Query m n) :
    (reindexMap er ec sim).combine seed q
      (H *ᵥ ((reindexMap er ec sim).first seed q),
        H *ᵥ ((reindexMap er ec sim).second seed q
          (H *ᵥ ((reindexMap er ec sim).first seed q)))) =
      oracle ((A seed).submatrix er ec) q :=
  (congrArg (reindexReply er ec) (hsim seed (reindexQuery er ec q))).trans
    (matrixOracle_reindex er ec (A seed) q).symm

end ReindexMap

section Simplex
open RandomOrthogonal SimplexNormalization
variable {k m n T : ℕ} {Seed : Type*} [MeasurableSpace Seed]

abbrev SignSeed (k : ℕ) := Cube k → Bool
abbrev SimplexSeed (k : ℕ) (Seed : Type*) := SignSeed k × Seed

def simplexAccuracy (k : ℕ) (κ : ℝ) : ℝ := 1 / (2 * embeddingScale k κ)

def modelSimplexMatrix (k : ℕ) (H : Matrix (Cube k) (Cube k) ℝ)
    (b : Euclidean (Cube k)) (κ : ℝ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k))
    (σ : SignSeed k) : Payoff m n :=
  (walshGame k H (toCoordinates b) κ σ).submatrix er ec

def simplexSimulation (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (κ : ℝ) :
    TwoCallMap (Query m n) (Reply m n) (Cube k → ℝ) (Cube k → ℝ)
      (Euclidean (Cube k) × SimplexSeed k Seed) :=
  reindexMap er ec (simplexMapWithSeed
    (fun p => toCoordinates p.1)
    (fun p => testingBasis k p.2.1 * signedDictionary (Real.sqrt (2 ^ k : ℝ)))
    (fun _ => signedDictionary (Real.sqrt (2 ^ k : ℝ)))
    (fun _ => embeddingScale k κ)
    (measurable_toCoordinates.comp measurable_fst)
    ((measurable_of_countable (fun σ : SignSeed k =>
      testingBasis k σ * (signedDictionary (Real.sqrt (2 ^ k : ℝ)) :
        Matrix (Cube k) (Cube k ⊕ Cube k) ℝ))).comp
          (measurable_fst.comp measurable_snd)) measurable_const measurable_const)

theorem simplexSimulation_correct (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (κ : ℝ)
    (H : Matrix (Cube k) (Cube k) ℝ) (hH : H.transpose = H)
    (seed : Euclidean (Cube k) × SimplexSeed k Seed) (q : Query m n) :
    (simplexSimulation k er ec κ).combine seed q
      (H *ᵥ ((simplexSimulation k er ec κ).first seed q),
        H *ᵥ ((simplexSimulation k er ec κ).second seed q
          (H *ᵥ ((simplexSimulation k er ec κ).first seed q)))) =
      oracle (modelSimplexMatrix k H seed.1 κ er ec seed.2.1) q :=
  reindexMap_correct er ec _ H _
    (simplexMapWithSeed_correct H hH _ _ _ _ _ _ _ _) seed q

def simplexRecovery (k : ℕ) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (out : Query m n) :
    Euclidean (Cube k) :=
  fromCoordinates ((signedDictionary (Real.sqrt (2 ^ k : ℝ)) :
    Matrix (Cube k) (Cube k ⊕ Cube k) ℝ) *ᵥ (out.1 ∘ ec.symm))

theorem measurable_simplexRecovery (k : ℕ) (ec : Fin n ≃ (Cube k ⊕ Cube k)) :
    Measurable (simplexRecovery (m := m) k ec) := by
  apply measurable_fromCoordinates.comp
  apply measurable_pi_lambda
  intro i
  simp only [Matrix.mulVec, dotProduct, Function.comp_apply]
  fun_prop

def simplexUnitPolicy (alg : Algorithm m n T Seed) (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (κ : ℝ) :
    Policy (Euclidean (Cube k)) (Euclidean (Cube k)) (Euclidean (Cube k)) (2 * T)
      (Euclidean (Cube k) × SimplexSeed k Seed) :=
  sourcePolicy ((ofAlgorithm alg).seedMap (fun p => p.2.2)
    (measurable_snd.comp measurable_snd))
    (simplexSimulation k er ec κ) (fun _ out => simplexRecovery k ec out)
    ((measurable_simplexRecovery k ec).comp measurable_snd)

theorem simplexUnitPolicy_run (alg : Algorithm m n T Seed) (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (κ : ℝ)
    (H : Matrix (Cube k) (Cube k) ℝ) (hH : H.transpose = H)
    (b : Euclidean (Cube k)) (seed : SimplexSeed k Seed) :
    (simplexUnitPolicy alg k er ec κ).run (euclideanMatrixMap H) (b, seed) =
      simplexRecovery k ec (alg.run (modelSimplexMatrix k H b κ er ec seed.1) seed.2) := by
  have hrun := sourcePolicy_run
    ((ofAlgorithm alg).seedMap
      (fun p : Euclidean (Cube k) × SimplexSeed k Seed => p.2.2)
      (measurable_snd.comp measurable_snd))
    (simplexSimulation k er ec κ)
    (fun (_ : Euclidean (Cube k) × SimplexSeed k Seed) (out : Query m n) => simplexRecovery k ec out)
    ((measurable_simplexRecovery k ec).comp measurable_snd) H
    (fun p => oracle (modelSimplexMatrix k H p.1 κ er ec p.2.1))
    (simplexSimulation_correct k er ec κ H hH) (b, seed)
  rw [Policy.seedMap_run, ofAlgorithm_run] at hrun
  exact hrun

theorem simplex_success_residual (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k))
    (κ : ℝ) (hκ : 0 < κ) (H : Matrix (Cube k) (Cube k) ℝ)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖)
    (b : Euclidean (Cube k)) (hb : ‖b‖ ≤ 1) (σ : SignSeed k) (out : Query m n)
    (hgood : GameSuccess .simplexSimplex (modelSimplexMatrix k H b κ er ec σ)
      (simplexAccuracy k κ) out) :
    ‖euclideanMatrixMap H (simplexRecovery k ec out) - b‖ ≤ 1 / 2 := by
  let x : Cube k ⊕ Cube k → ℝ := out.1 ∘ ec.symm
  let y : Cube k ⊕ Cube k → ℝ := out.2 ∘ er.symm
  have hsuccess : GameSuccess .simplexSimplex
      ((walshGame k H (toCoordinates b) κ σ).submatrix er ec) (simplexAccuracy k κ)
      ((fun j => x (ec j)), (fun i => y (er i))) := by
    simpa only [x, y, Function.comp_apply, Equiv.symm_apply_apply, Prod.mk.eta] using hgood
  obtain ⟨hx, _, hgap⟩ := gameSuccess_reindex_simplex er ec _ x y _ hsuccess
  have hgap' : FullGapAtMost
      (simplexMatrix H (toCoordinates b)
        (testingBasis k σ * signedDictionary (Real.sqrt (Fintype.card (Cube k))))
        (signedDictionary (Real.sqrt (Fintype.card (Cube k)))) (embeddingScale k κ))
      x y (simplexAccuracy k κ) := by
    simpa only [walshGame, cube_card, Nat.cast_pow, Nat.cast_ofNat] using hgap
  have hres := simplex_source_residual H (testingBasis k σ) (source_expansion_squares H hH)
    (testingBasis_orthogonal k σ) (toCoordinates b) (euclidean_unit_sq b hb)
    (fun _ => false) (embeddingScale k κ) (simplexAccuracy k κ)
    (embeddingScale_pos k hκ) x y hx hgap'
  have hscale : embeddingScale k κ * simplexAccuracy k κ = 1 / 2 := by
    unfold simplexAccuracy
    field_simp [ne_of_gt (embeddingScale_pos k hκ)]
    ring
  rw [hscale] at hres
  simp only [cube_card, Nat.cast_pow, Nat.cast_ofNat] at hres
  have hnorm : Real.sqrt (∑ i,
      ((H *ᵥ ((signedDictionary (Real.sqrt (2 ^ k : ℝ)) :
        Matrix (Cube k) (Cube k ⊕ Cube k) ℝ) *ᵥ x)) i - toCoordinates b i) ^ 2) =
      ‖euclideanMatrixMap H (simplexRecovery k ec out) - b‖ := by
    change Real.sqrt (∑ i, ((euclideanMatrixMap H (simplexRecovery k ec out) - b) i) ^ 2) = _
    rw [← euclidean_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  rwa [hnorm] at hres

theorem simplexUnitPolicy_success (alg : Algorithm m n T Seed)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k))
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hsolve : Solves alg μ .simplexSimplex (simplexAccuracy k κ))
    (H : Matrix (Cube k) (Cube k) ℝ) (hsymm : H.transpose = H)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hnorm : ‖euclideanMatrixMap H‖ ≤ κ)
    (b : Euclidean (Cube k)) (hb : ‖b‖ ≤ 1) :
    (3 / 5 : ℝ) ≤ ((signLaw (Cube k)).prod μ).real {seed |
      ‖euclideanMatrixMap H ((simplexUnitPolicy alg k er ec κ).run
        (euclideanMatrixMap H) (b, seed)) - b‖ ≤ 1 / 2} := by
  let A := modelSimplexMatrix k H b κ er ec
  have hraw := walshGame_bounded_probability k H (toCoordinates b) hκ
    (matrix_column_sq_le_opNorm H κ (by linarith) hnorm) (euclidean_unit_sq b hb)
  have hadm : (1 - 1 / 100 : ℝ) ≤ (signLaw (Cube k)).real
      {σ | Admissible .simplexSimplex (A σ)} := by
    apply (show (1 - 1 / 100 : ℝ) = 99 / 100 by norm_num).le.trans
    apply hraw.trans
    refine measureReal_mono (fun σ hσ => ?_) (measure_ne_top _ _)
    intro i j
    exact hσ (er i) (ec j)
  have hmixture := countable_mixture_success (signLaw (Cube k)) μ
    (fun σ => Admissible .simplexSimplex (A σ))
    (fun σ seed => GameSuccess .simplexSimplex (A σ) (simplexAccuracy k κ) (alg.run (A σ) seed))
    (fun σ => measurableSet_algorithm_success alg .simplexSimplex (A σ) (simplexAccuracy k κ))
    (1 / 100) (2 / 3) (by norm_num) (by norm_num) hadm
    (fun σ hσ => hsolve (A σ) hσ)
  apply (show (3 / 5 : ℝ) ≤ 2 / 3 - 1 / 100 by norm_num).trans (hmixture.trans ?_)
  refine measureReal_mono (fun seed hseed => ?_) (measure_ne_top _ _)
  dsimp only [Set.mem_setOf_eq] at hseed ⊢
  rw [simplexUnitPolicy_run alg k er ec κ H hsymm]
  exact simplex_success_residual k er ec κ (by linarith) H hH b hb seed.1 _ hseed

def simplexSourcePolicy (alg : Algorithm m n T Seed) (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k)) (κ : ℝ) :=
  homogeneousPolicy (simplexUnitPolicy alg k er ec κ)

theorem simplexSourcePolicy_success (alg : Algorithm m n T Seed)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (k : ℕ)
    (er : Fin m ≃ (Cube k ⊕ Cube k)) (ec : Fin n ≃ (Cube k ⊕ Cube k))
    (κ : ℝ) (hκ : 1 ≤ κ)
    (hsolve : Solves alg μ .simplexSimplex (simplexAccuracy k κ))
    (H : Matrix (Cube k) (Cube k) ℝ) (hsymm : H.transpose = H)
    (hH : ∀ z, ‖z‖ ≤ ‖Matrix.toEuclideanLin H z‖) (hnorm : ‖euclideanMatrixMap H‖ ≤ κ)
    (b : Euclidean (Cube k)) :
    (3 / 5 : ℝ) ≤ ((signLaw (Cube k)).prod μ).real {seed |
      ‖euclideanMatrixMap H ((simplexSourcePolicy alg k er ec κ).run
        (euclideanMatrixMap H) (b, seed)) - b‖ ≤ ‖b‖ / 2} := by
  exact homogeneousPolicy_success ((signLaw (Cube k)).prod μ) (simplexUnitPolicy alg k er ec κ)
    (euclideanMatrixMap H) (3 / 5) (by norm_num)
    (fun r hr => simplexUnitPolicy_success alg μ k er ec κ hκ hsolve H hsymm hH hnorm r hr.le) b

end Simplex
end
end Matvec.GameSourceSolver
