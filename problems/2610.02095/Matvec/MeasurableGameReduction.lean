import Matvec.MeasurableFlat
import Matvec.PolicyComposition

/-!
# Measurable game reductions, including public right-hand sides and random bases

The simulation maps below allow the right-hand side and dictionary to depend
measurably on the seed. Finite reindexing connects the ball embedding's sum
coordinates to the actual `Model.Algorithm` interface.
-/

namespace Matvec.MeasurableSimulation
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

universe s

local instance matrixMeasurable (a b : Type*) : MeasurableSpace (Matrix a b ℝ) :=
  inferInstanceAs (MeasurableSpace (a → b → ℝ))

section SeedDependent
variable {d m n : Type*} [Fintype d] [Fintype m] [Fintype n]
  {Seed : Type s} [MeasurableSpace Seed]

def simplexMapWithSeed (b : Seed → d → ℝ) (R : Seed → Matrix d m ℝ)
    (V : Seed → Matrix d n ℝ) (Λ : Seed → ℝ)
    (hb : Measurable b) (hR : Measurable R) (hV : Measurable V) (hΛ : Measurable Λ) :
    TwoCallMap ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) (d → ℝ) (d → ℝ) Seed where
  first seed q := V seed *ᵥ q.1
  second seed q _ := R seed *ᵥ q.2
  combine seed q replies := simplexCombine (b seed) (R seed) (V seed) (Λ seed) q replies.1 replies.2
  first_measurable := by
    have hV' (i : d) (j : n) : Measurable (fun seed => V seed i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hV)
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  second_measurable := by
    have hR' (i : d) (j : m) : Measurable (fun seed => R seed i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hR)
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  combine_measurable := by
    have hV' (i : d) (j : n) : Measurable (fun seed => V seed i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hV)
    have hR' (i : d) (j : m) : Measurable (fun seed => R seed i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hR)
    unfold simplexCombine
    apply Measurable.prodMk
    all_goals
      apply measurable_pi_lambda
      intro i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        Matrix.transpose_apply]
      fun_prop

theorem simplexMapWithSeed_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : Seed → d → ℝ) (R : Seed → Matrix d m ℝ) (V : Seed → Matrix d n ℝ) (Λ : Seed → ℝ)
    (hb : Measurable b) (hR : Measurable R) (hV : Measurable V) (hΛ : Measurable Λ)
    (seed : Seed) (q : (n → ℝ) × (m → ℝ)) :
    (simplexMapWithSeed b R V Λ hb hR hV hΛ).combine seed q
      (H *ᵥ ((simplexMapWithSeed b R V Λ hb hR hV hΛ).first seed q),
        H *ᵥ ((simplexMapWithSeed b R V Λ hb hR hV hΛ).second seed q
          (H *ᵥ ((simplexMapWithSeed b R V Λ hb hR hV hΛ).first seed q)))) =
      matrixOracle (simplexMatrix H (b seed) (R seed) (V seed) (Λ seed)) q :=
  simplexCombine_correct H hH (b seed) (R seed) (V seed) (Λ seed) q

def ballMapWithSeed (b : Seed → d → ℝ) (α β : ℝ) (hb : Measurable b) :
    TwoCallMap (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) (d → ℝ) (d → ℝ) Seed where
  first _ q i := q.1 (Sum.inl i)
  second _ q _ i := q.2 (Sum.inl i) - q.2 (Sum.inr i)
  combine seed q replies := ballCombine (b seed) α β q replies.1 replies.2
  first_measurable := by fun_prop
  second_measurable := by fun_prop
  combine_measurable := by
    unfold ballCombine
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      cases i <;> simp only [Pi.neg_apply, Sum.elim_inl, Sum.elim_inr] <;> fun_prop
    · apply measurable_pi_lambda
      intro i
      cases i <;> simp only [Pi.neg_apply, Sum.elim_inl, Sum.elim_inr,
        Pi.smul_apply, smul_eq_mul, dotProduct, Pi.sub_apply] <;> fun_prop

theorem ballMapWithSeed_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : Seed → d → ℝ) (α β : ℝ) (hb : Measurable b) (seed : Seed)
    (q : ((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ)) :
    (ballMapWithSeed b α β hb).combine seed q
      (H *ᵥ ((ballMapWithSeed b α β hb).first seed q),
        H *ᵥ ((ballMapWithSeed b α β hb).second seed q
          (H *ᵥ ((ballMapWithSeed b α β hb).first seed q)))) =
      matrixOracle (-ballMatrix H (b seed) α β) q :=
  ballCombine_correct H hH (b seed) α β q

end SeedDependent

section Reindex
variable {m n m' n' : Type*} [Fintype m] [Fintype n] [Fintype m'] [Fintype n']

def reindexQuery (erow : m ≃ m') (ecol : n ≃ n') (q : (n → ℝ) × (m → ℝ)) :
    (n' → ℝ) × (m' → ℝ) := (q.1 ∘ ecol.symm, q.2 ∘ erow.symm)

def reindexReply (erow : m ≃ m') (ecol : n ≃ n') (r : (m' → ℝ) × (n' → ℝ)) :
    (m → ℝ) × (n → ℝ) := (r.1 ∘ erow, r.2 ∘ ecol)

omit [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] in
theorem measurable_reindexQuery (erow : m ≃ m') (ecol : n ≃ n') :
    Measurable (reindexQuery erow ecol) := by unfold reindexQuery; fun_prop

omit [Fintype m] [Fintype n] [Fintype m'] [Fintype n'] in
theorem measurable_reindexReply (erow : m ≃ m') (ecol : n ≃ n') :
    Measurable (reindexReply erow ecol) := by unfold reindexReply; fun_prop

omit [Fintype m] [Fintype m'] in
theorem reindex_mulVec (erow : m ≃ m') (ecol : n ≃ n')
    (A : Matrix m' n' ℝ) (x : n → ℝ) :
    (fun i j => A (erow i) (ecol j)) *ᵥ x =
      (A *ᵥ (x ∘ ecol.symm)) ∘ erow := by
  ext i
  unfold Matrix.mulVec dotProduct
  apply Fintype.sum_equiv ecol
  intro j
  simp

theorem matrixOracle_reindex (erow : m ≃ m') (ecol : n ≃ n')
    (A : Matrix m' n' ℝ) (q : (n → ℝ) × (m → ℝ)) :
    matrixOracle (fun i j => A (erow i) (ecol j)) q =
      reindexReply erow ecol (matrixOracle A (reindexQuery erow ecol q)) := by
  apply Prod.ext
  · exact reindex_mulVec erow ecol A q.1
  · exact reindex_mulVec ecol erow A.transpose q.2

end Reindex

section FinBall
variable {d : Type*} [Fintype d] {m n : ℕ} {Seed : Type s} [MeasurableSpace Seed]

def finBallMap (erow : Fin m ≃ d ⊕ d) (ecol : Fin n ≃ d ⊕ Unit)
    (b : Seed → d → ℝ) (α β : ℝ) (hb : Measurable b) :
    TwoCallMap (Query m n) (Reply m n) (d → ℝ) (d → ℝ) Seed where
  first seed q := (ballMapWithSeed b α β hb).first seed (reindexQuery erow ecol q)
  second seed q r := (ballMapWithSeed b α β hb).second seed (reindexQuery erow ecol q) r
  combine seed q r := reindexReply erow ecol
    ((ballMapWithSeed b α β hb).combine seed (reindexQuery erow ecol q) r)
  first_measurable := (ballMapWithSeed b α β hb).first_measurable.comp
    (measurable_fst.prodMk ((measurable_reindexQuery erow ecol).comp measurable_snd))
  second_measurable := (ballMapWithSeed b α β hb).second_measurable.comp
    (measurable_fst.prodMk
      (((measurable_reindexQuery erow ecol).comp (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd)))
  combine_measurable := (measurable_reindexReply erow ecol).comp
    ((ballMapWithSeed b α β hb).combine_measurable.comp
      (measurable_fst.prodMk
        (((measurable_reindexQuery erow ecol).comp (measurable_fst.comp measurable_snd)).prodMk
          (measurable_snd.comp measurable_snd))))

theorem finBallMap_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (erow : Fin m ≃ d ⊕ d) (ecol : Fin n ≃ d ⊕ Unit)
    (b : Seed → d → ℝ) (α β : ℝ) (hb : Measurable b) (seed : Seed) (q : Query m n) :
    (finBallMap erow ecol b α β hb).combine seed q
      (H *ᵥ ((finBallMap erow ecol b α β hb).first seed q),
        H *ᵥ ((finBallMap erow ecol b α β hb).second seed q
          (H *ᵥ ((finBallMap erow ecol b α β hb).first seed q)))) =
      oracle (fun i j => (-ballMatrix H (b seed) α β) (erow i) (ecol j)) q := by
  exact (congrArg (reindexReply erow ecol)
    (ballMapWithSeed_correct H hH b α β hb seed (reindexQuery erow ecol q))).trans
      (matrixOracle_reindex erow ecol (-ballMatrix H (b seed) α β) q).symm

def ballRecovery (ecol : Fin n ≃ d ⊕ Unit) (out : Query m n) : d → ℝ :=
  fun i => (out.1 (ecol.symm (Sum.inr ())))⁻¹ * out.1 (ecol.symm (Sum.inl i))

omit [Fintype d] in
theorem measurable_ballRecovery (ecol : Fin n ≃ d ⊕ Unit) :
    Measurable (ballRecovery (m := m) ecol) := by unfold ballRecovery; fun_prop

end FinBall

theorem compile_seed_simplex_algorithm_run {d m n T : ℕ} {Seed : Type s} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose = H)
    (b : Seed → Fin d → ℝ) (R : Seed → Matrix (Fin d) (Fin m) ℝ)
    (V : Seed → Matrix (Fin d) (Fin n) ℝ) (Λ : Seed → ℝ)
    (hb : Measurable b) (hR : Measurable R) (hV : Measurable V) (hΛ : Measurable Λ) (seed : Seed) :
    (compile (ofAlgorithm alg) (simplexMapWithSeed b R V Λ hb hR hV hΛ)).toPolicy.run
      H.mulVec seed = alg.run (simplexMatrix H (b seed) (R seed) (V seed) (Λ seed)) seed := by
  rw [PairedPolicy.toPolicy_run]
  exact (compile_run _ _ H.mulVec
    (fun seed => matrixOracle (simplexMatrix H (b seed) (R seed) (V seed) (Λ seed)))
    (simplexMapWithSeed_correct H hH b R V Λ hb hR hV hΛ) seed).trans (ofAlgorithm_run alg _ seed)

theorem compile_ball_algorithm_run {d : Type*} [Fintype d] {m n T : ℕ}
    {Seed : Type s} [MeasurableSpace Seed] (alg : Algorithm m n T Seed)
    (H : Matrix d d ℝ) (hH : H.transpose = H)
    (erow : Fin m ≃ d ⊕ d) (ecol : Fin n ≃ d ⊕ Unit)
    (b : Seed → d → ℝ) (α β : ℝ) (hb : Measurable b) (seed : Seed) :
    (compile (ofAlgorithm alg) (finBallMap erow ecol b α β hb)).toPolicy.run H.mulVec seed =
      alg.run (fun i j => (-ballMatrix H (b seed) α β) (erow i) (ecol j)) seed := by
  rw [PairedPolicy.toPolicy_run]
  exact (compile_run _ _ H.mulVec
    (fun seed => oracle (fun i j => (-ballMatrix H (b seed) α β) (erow i) (ecol j)))
    (finBallMap_correct H hH erow ecol b α β hb) seed).trans (ofAlgorithm_run alg _ seed)

end
end Matvec.MeasurableSimulation

