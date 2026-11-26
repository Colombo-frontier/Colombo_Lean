import NCBall.TranscriptGeometry

/-! # Shared hidden vector and separately reusable Gaussian noise blocks -/

noncomputable section
open scoped InnerProductSpace
namespace NCBall

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev HandleLatent (H : ℕ) := PiLp 2 (fun _ : Fin (H + 1) => F)

instance (priority := 10) handleLatentMeasurableSpace (H : ℕ) : MeasurableSpace (HandleLatent F H) :=
  borel (HandleLatent F H)

instance (priority := 10) handleLatentBorelSpace (H : ℕ) : BorelSpace (HandleLatent F H) := ⟨rfl⟩

def handleBlock {H : ℕ} (j : Fin (H + 1)) (a : F) : HandleLatent F H :=
  (WithLp.equiv 2 _).symm (Pi.single j a)

def hiddenBlock (H : ℕ) : HandleLatent F H →L[ℝ] F :=
  PiLp.proj 2 (fun _ : Fin (H + 1) => F) 0

def noisyHandleDirection {H : ℕ} (σ : ℝ) (h : Fin H) : F →L[ℝ] HandleLatent F H :=
  LinearMap.mkContinuous
    { toFun := fun a => handleBlock F 0 a + σ • handleBlock F h.succ a
      map_add' := by
        intro a b
        ext j
        simp [handleBlock, Pi.single_add, smul_add]
        abel
      map_smul' := by
        intro r a
        ext j
        simp [handleBlock, Pi.single_smul, smul_add, smul_smul, mul_comm] }
    (1 + |σ|) (by
      intro a
      have hn (j : Fin (H + 1)) : ‖handleBlock F j a‖ = ‖a‖ :=
        PiLp.norm_equiv_symm_single 2 (fun _ => F) j a
      calc
        ‖handleBlock F 0 a + σ • handleBlock F h.succ a‖ ≤
            ‖handleBlock F 0 a‖ + ‖σ • handleBlock F h.succ a‖ := norm_add_le _ _
        _ = (1 + |σ|) * ‖a‖ := by rw [norm_smul, hn, hn, Real.norm_eq_abs]; ring)

variable {F}

omit [InnerProductSpace ℝ F] in
theorem handleBlock_norm {H : ℕ} (j : Fin (H + 1)) (a : F) :
    ‖handleBlock F j a‖ = ‖a‖ :=
  PiLp.norm_equiv_symm_single 2 (fun _ => F) j a

theorem handleBlock_inner {H : ℕ} (i j : Fin (H + 1)) (a b : F) :
    ⟪handleBlock F i a, handleBlock F j b⟫_ℝ = if i = j then ⟪a, b⟫_ℝ else 0 := by
  classical
  rw [PiLp.inner_apply]
  simp [handleBlock, Pi.single_apply, apply_ite, inner_zero_right, inner_zero_left]
  split_ifs with hij <;> simp_all

theorem hiddenBlock_norm_le {H : ℕ} (x : HandleLatent F H) :
    ‖hiddenBlock F H x‖ ≤ ‖x‖ := PiLp.norm_apply_le x 0

theorem hiddenBlock_noise {H : ℕ} (h : Fin H) (a : F) :
    hiddenBlock F H (handleBlock F h.succ a) = 0 := by
  simp [hiddenBlock, handleBlock, Pi.single_apply, Fin.succ_ne_zero]

theorem noisyHandleDirection_inner_noise {H : ℕ} (σ : ℝ) (h k : Fin H) (a b : F) :
    ⟪noisyHandleDirection F σ h a, handleBlock F k.succ b⟫_ℝ =
      if h = k then σ * ⟪a, b⟫_ℝ else 0 := by
  change ⟪handleBlock F 0 a + σ • handleBlock F h.succ a, handleBlock F k.succ b⟫_ℝ = _
  rw [inner_add_left, real_inner_smul_left, handleBlock_inner, handleBlock_inner]
  simp [Ne.symm (Fin.succ_ne_zero k), Fin.succ_inj, mul_ite]

theorem handle_fresh_innovation_bound {H : ℕ} (σ : ℝ) (hσ : 0 < σ)
    (Q : HandleLatent F H →L[ℝ] HandleLatent F H) (hQ : IsResidualProjection Q)
    (h : Fin H) (a : F) (ha : ‖a‖ = 1)
    (hfresh : Q (handleBlock F h.succ a) = handleBlock F h.succ a) :
    ‖hiddenBlock F H (normalizedInnovation Q (noisyHandleDirection F σ h a))‖ ^ 2 ≤
      1 / σ ^ 2 := by
  apply noisy_innovation_energy_bound (hiddenBlock F H) hiddenBlock_norm_le hQ
    (handleBlock F 0 a) (handleBlock F h.succ a)
  · simp only [handleBlock_norm, ha, le_refl]
  · simp only [handleBlock_norm, ha]
  · rw [handleBlock_inner, if_neg (Ne.symm (Fin.succ_ne_zero h))]
  · exact hfresh
  · exact hiddenBlock_noise h a
  · exact hσ

end NCBall
