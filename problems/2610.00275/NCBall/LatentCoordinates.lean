import NCBall.FullSuccess

/-! # The hidden table has exactly the Gaussian law used for class verification -/

noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace NCBall

def normalizedBlockCoordinates {n H : ℕ} (b : Fin (H + 1))
    (w : HandleLatent (Transverse n) H) : Fin n → ℝ :=
  fun i => (Real.sqrt (n : ℝ))⁻¹ * w b i

theorem normalizedBlockCoordinates_measurable {n H : ℕ} (b : Fin (H + 1)) :
    Measurable (normalizedBlockCoordinates (n := n) b) := by
  let e : HandleLatent (Transverse n) H →L[ℝ] Transverse n := PiLp.proj 2 _ b
  apply measurable_pi_lambda
  intro i
  exact (((EuclideanSpace.proj i).measurable).comp e.measurable).const_mul _

theorem normalizedBlockCoordinates_law {n H : ℕ} (hn : 0 < n) (b : Fin (H + 1)) :
    (euclideanGaussianLaw (HandleLatent (Transverse n) H)).map (normalizedBlockCoordinates b) =
      isotropicGaussian n := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let v : Fin n → HandleLatent (Transverse n) H :=
    fun i => scale • handleBlock (Transverse n) b (EuclideanSpace.single i 1)
  have hv (i j : Fin n) (hij : i ≠ j) : ⟪v i, v j⟫_ℝ = 0 := by
    dsimp only [v]
    rw [real_inner_smul_left, real_inner_smul_right, handleBlock_inner, if_pos rfl,
      EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, if_neg hij]
    simp
  have hi : (fun w : HandleLatent (Transverse n) H => fun i => ⟪v i, w⟫_ℝ) =
      normalizedBlockCoordinates b := by
    funext w i
    dsimp only [v]
    rw [real_inner_smul_left, handleBlock_inner_apply, EuclideanSpace.inner_single_left]
    simp only [map_one, one_mul]
    rfl
  have hs : scale ^ 2 = 1 / (n : ℝ) := by
    dsimp only [scale]
    rw [inv_pow, Real.sq_sqrt (by exact_mod_cast hn.le), one_div]
  have hnrm (i : Fin n) : ‖v i‖ ^ 2 = 1 / (n : ℝ) := by
    simp only [v, norm_smul, handleBlock_norm, EuclideanSpace.norm_single,
      Real.norm_eq_abs, abs_one, mul_one, sq_abs]
    exact hs
  have hg := gaussian_orthogonal_coordinates v hv
  rw [hi] at hg
  convert hg using 1
  unfold isotropicGaussian
  congr 1
  funext i
  exact NNReal.eq (hnrm i).symm

def latentBlockCoordinates {n H M : ℕ} (b : Fin (H + 1)) (w : RoomLatents n H M) :
    Fin M → Fin n → ℝ := fun j => normalizedBlockCoordinates b (w j)

theorem latentBlockCoordinates_law {n H M : ℕ} (hn : 0 < n) (b : Fin (H + 1)) :
    MeasurePreserving (latentBlockCoordinates (M := M) b) (roomLatentLaw n H M) (gaussianRooms n M) :=
  measurePreserving_pi _ _ (fun _ =>
    ⟨normalizedBlockCoordinates_measurable b, normalizedBlockCoordinates_law hn b⟩)

theorem latentDirections_eq_roomNoise {n H M : ℕ} (w : RoomLatents n H M) :
    latentDirections (Real.sqrt (n : ℝ))⁻¹ w = roomNoise (latentBlockCoordinates 0 w) := by
  funext k
  unfold latentDirections finiteRoomExtension roomNoise
  split_ifs
  · rfl
  · rfl

theorem latent_good_event_probability {n H M : ℕ} (hn : 0 < n)
    (hlog : 2 * Real.log (8 * ((M : ℝ) + 1)) ≤ n) :
    7 / 8 ≤ (roomLatentLaw n H M).real (latentGoodEvent (Real.sqrt (n : ℝ))⁻¹) := by
  have hB : MeasurableSet {z : Fin M → Fin n → ℝ | ∀ j < M, ‖roomNoise z j‖ ≤ 2} := by
    simp only [setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (roomNoise_continuous n M j).measurable.norm measurable_const
  have hlaw := (latentBlockCoordinates_law (H := H) (M := M) hn (0 : Fin (H + 1)))
  have he : (roomLatentLaw n H M) (latentGoodEvent (Real.sqrt (n : ℝ))⁻¹) =
      (gaussianRooms n M) {z | ∀ j < M, ‖roomNoise z j‖ ≤ 2} := by
    rw [← hlaw.map_eq, Measure.map_apply hlaw.measurable hB]
    congr 1
  have hg := actual_good_event_probability hn hlog
  simpa only [measureReal_def, he] using hg

end NCBall
