import Mathlib
import PaperAudit.Frontier02

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: BoundaryHessianAcquisition.lean

open scoped BigOperators

namespace FangqingBoundaryHessianAcquisition

open FangqingPacketLeakage

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem path_inner_at_known_coordinate
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (k : Fin (n + 1)) (i : Fin (n + 2)) :
    inner ℝ (pathDirection n v i) (v k.succ.castSucc) =
      if i = k.succ then 1 else if i = k.castSucc then -1 else 0 := by
  have hc : i.castSucc = k.succ.castSucc ↔ i = k.succ := Fin.castSucc_inj
  have hs : i.succ = k.succ.castSucc ↔ i = k.castSucc := by
    constructor
    · intro he
      apply Fin.ext
      have hh := congrArg (fun j : Fin (n + 3) => j.val) he
      simp only [Fin.val_succ, Fin.val_castSucc] at hh ⊢
      omega
    · intro he
      subst i
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_castSucc]
  rw [pathDirection, inner_sub_left]
  simp only [orthonormal_iff_ite.mp hv, hc, hs]
  have hne : k.succ ≠ k.castSucc := by
    intro he
    have hh := congrArg (fun j : Fin (n + 2) => j.val) he
    simp only [Fin.val_succ, Fin.val_castSucc] at hh
    omega
  by_cases hf : i = k.succ
  · subst i
    simp [hne]
  · by_cases hp : i = k.castSucc <;> simp [hf, hp, hne, Ne.symm hne]

theorem actual_path_hessian_at_known_query
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (k : Fin (n + 1)) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t c : ℝ)
    (hplus : deriv (deriv g) t = c) (hminus : deriv (deriv g) (-t) = c) (w : E) :
    fderiv ℝ (fderiv ℝ (edgeSum g (pathDirection n v)))
      (t • v k.succ.castSucc) (v k.succ.castSucc) w =
      -c * inner ℝ (pathDirection n v k.castSucc) w +
        c * inner ℝ (pathDirection n v k.succ) w := by
  rw [hessian_edgeSum_apply g hg]
  have hne : k.succ ≠ k.castSucc := by
    intro he
    have hh := congrArg (fun j : Fin (n + 2) => j.val) he
    simp only [Fin.val_succ, Fin.val_castSucc] at hh
    omega
  calc
    _ = ∑ i : Fin (n + 2),
        ((if i = k.castSucc then -c * inner ℝ (pathDirection n v k.castSucc) w else 0) +
          (if i = k.succ then c * inner ℝ (pathDirection n v k.succ) w else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_right, path_inner_at_known_coordinate n v hv k i]
      by_cases hf : i = k.succ
      · subst i
        simp [hne, hplus]
      · by_cases hp : i = k.castSucc
        · subst i
          simp [Ne.symm hne, hminus]
        · simp [hf, hp]
    _ = _ := by rw [Finset.sum_add_distrib]; simp

noncomputable def pathHessianResponse
    (n : ℕ) (v : Fin (n + 3) → E) (g : ℝ → ℝ) (query direction : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (fderiv ℝ (edgeSum g (pathDirection n v))) query direction)

theorem actual_signed_boundary_decoder
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v)
    (k : Fin (n + 1)) (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (t c : ℝ)
    (hplus : deriv (deriv g) t = c) (hminus : deriv (deriv g) (-t) = c) (hc : c ≠ 0) :
    v k.succ.succ = (2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc -
      c⁻¹ • pathHessianResponse n v g (t • v k.succ.castSucc) (v k.succ.castSucc) := by
  have hmid : k.castSucc.succ = k.succ.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
  have hresp : pathHessianResponse n v g (t • v k.succ.castSucc) (v k.succ.castSucc) =
      c • ((2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc - v k.succ.succ) := by
    apply ext_inner_right ℝ
    intro w
    have hr := (InnerProductSpace.toDual ℝ E).apply_symm_apply
      (fderiv ℝ (fderiv ℝ (edgeSum g (pathDirection n v)))
        (t • v k.succ.castSucc) (v k.succ.castSucc))
    have hh := congrArg (fun f : E →L[ℝ] ℝ => f w) hr
    change inner ℝ (pathHessianResponse n v g (t • v k.succ.castSucc)
      (v k.succ.castSucc)) w = _ at hh
    rw [hh, actual_path_hessian_at_known_query n v hv k g hg t c hplus hminus w]
    simp only [pathDirection, hmid, real_inner_smul_left, inner_sub_left]
    ring
  rw [hresp, smul_smul, inv_mul_cancel₀ hc, one_smul]
  module

theorem actual_flat_edge_boundary_curvature
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta)
    (hhalf : delta ≤ omega / 2) :
    deriv (deriv (FlatCubic.edge P delta omega)) (omega / 2) = omega ∧
      deriv (deriv (FlatCubic.edge P delta omega)) (-(omega / 2)) = omega := by
  have hw : 0 < omega := by linarith only [hd, hhalf]
  have hdw : delta ≤ omega := by linarith only [hd, hhalf]
  have hs : ∀ t : ℝ, |t| = omega / 2 →
      deriv (deriv (FlatCubic.edge P delta omega)) t = omega := by
    intro t ht
    rw [FlatCubic.edge_second_deriv_eq_slope_abs P delta omega hd hdw, ht,
      FlatCubic.slope_matches_usual_after_delta P delta omega (omega / 2) hd hdw hhalf,
      min_eq_left (by linarith only [hw])]
    ring
  exact ⟨hs _ (abs_of_pos (by positivity)), hs _ (by rw [abs_neg, abs_of_pos (by positivity)])⟩

theorem actual_flat_edge_signed_boundary_decoder
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hhalf : delta ≤ omega / 2)
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v) (k : Fin (n + 1)) :
    v k.succ.succ = (2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc -
      omega⁻¹ • pathHessianResponse n v (FlatCubic.edge P delta omega)
        ((omega / 2) • v k.succ.castSucc) (v k.succ.castSucc) := by
  have hh := actual_flat_edge_boundary_curvature P delta omega hd hhalf
  apply actual_signed_boundary_decoder n v hv k (FlatCubic.edge P delta omega)
    (FlatCubic.edge_contDiff_two P delta omega hd (by linarith only [hd, hhalf]))
    (omega / 2) omega hh.1 hh.2
  exact ne_of_gt (by linarith only [hd, hhalf])

end FangqingBoundaryHessianAcquisition
end

section
-- Source component: ActualShellBoundaryAcquisition.lean

namespace FangqingActualShellBoundaryAcquisition

open FangqingPacketLeakage FangqingBoundaryHessianAcquisition
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  FangqingShellMinimizerTransfer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def scalarHessianVector (f : E → ℝ) (query direction : E) : E :=
  (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) query direction)

theorem scalarHessianVector_inner (f : E → ℝ) (query direction w : E) :
    inner ℝ (scalarHessianVector f query direction) w =
      fderiv ℝ (fderiv ℝ f) query direction w := by
  have hh := (InnerProductSpace.toDual ℝ E).apply_symm_apply
    (fderiv ℝ (fderiv ℝ f) query direction)
  exact congrArg (fun t : E →L[ℝ] ℝ => t w) hh

theorem actual_shell_signed_boundary_decoder
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hhalf : delta ≤ omega / 2)
    (n : ℕ) (v : Fin (n + 3) → E) (hv : Orthonormal ℝ v) (k : Fin (n + 1))
    (Q : E → ℝ) (G : E → E →L[ℝ] ℝ) (DG : E →L[ℝ] (E →L[ℝ] ℝ))
    (hQ : ∀ z, HasFDerivAt Q (G z) z)
    (hG : HasFDerivAt G DG ((omega / 2) • v k.succ.castSucc))
    (phi : ℝ → ℝ) (R A s gain scale : ℝ) (hscale : scale ≠ 0)
    (hRA : A ≤ R) (hA : omega / 2 < A)
    (handle : E) (hh : ‖handle‖ ≤ 1) (hphi : ∀ t, |t| < 1 → phi t = t) :
    let H1 := fun z => inactiveShell Q
      (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) z) R gain z -
        localizedSeed theta phi R A (s * A) handle z
    v k.succ.succ = (2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc -
      (scale * omega)⁻¹ •
        (scalarHessianVector H1 ((omega / 2) • v k.succ.castSucc) (v k.succ.castSucc) -
          (InnerProductSpace.toDual ℝ E).symm (DG (v k.succ.castSucc))) := by
  dsimp only
  let query := (omega / 2) • v k.succ.castSucc
  let H1 := fun z => inactiveShell Q
      (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) z) R gain z -
        localizedSeed theta phi R A (s * A) handle z
  have hw : 0 < omega := by linarith only [hd, hhalf]
  have hApos : 0 < A := (by positivity : 0 < omega / 2).trans hA
  have hRpos : 0 < R := hApos.trans_le hRA
  have hnorm : ‖query‖ = omega / 2 := by
    dsimp [query]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), hv.norm_eq_one, mul_one]
  have hlocal := actual_active_shell_eventually_eq_raw Q
    (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) z)
      phi R A s gain hRpos hApos handle query hh hphi
      (by rw [hnorm]; exact hA.trans_le hRA) (by rw [hnorm]; exact hA)
  have hraw : H1 =ᶠ[nhds query]
      (fun z => Q z + scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) z +
        linearSeed s handle z) := by
    filter_upwards [hlocal] with z hz
    simpa only [H1, linearSeed, ContinuousLinearMap.smul_apply, innerSL_apply_apply,
      smul_eq_mul, sub_eq_add_neg, neg_mul] using hz
  have hcurve := actual_flat_edge_boundary_curvature P delta omega hd hhalf
  have hmid : k.castSucc.succ = k.succ.castSucc := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castSucc]
  have hresp : scalarHessianVector H1 query (v k.succ.castSucc) -
      (InnerProductSpace.toDual ℝ E).symm (DG (v k.succ.castSucc)) =
      (scale * omega) • ((2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc - v k.succ.succ) := by
    apply ext_inner_right ℝ
    intro w
    have hpub := congrArg (fun t : E →L[ℝ] ℝ => t w)
      ((InnerProductSpace.toDual ℝ E).apply_symm_apply (DG (v k.succ.castSucc)))
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (DG (v k.succ.castSucc))) w = _ at hpub
    rw [inner_sub_left, scalarHessianVector_inner, hpub,
      second_fderiv_of_eventuallyEq H1 _ query hraw,
      hessian_total_apply Q G DG hQ (FlatCubic.edge P delta omega)
        (FlatCubic.edge_contDiff_two P delta omega hd (by linarith only [hd, hhalf]))
        (pathDirection n v) scale (linearSeed s handle) query (v k.succ.castSucc) w hG,
      actual_path_hessian_at_known_query n v hv k (FlatCubic.edge P delta omega)
        (FlatCubic.edge_contDiff_two P delta omega hd (by linarith only [hd, hhalf]))
        (omega / 2) omega hcurve.1 hcurve.2 w]
    simp only [pathDirection, hmid, real_inner_smul_left, inner_sub_left]
    ring
  change v k.succ.succ = (2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc -
    (scale * omega)⁻¹ • (scalarHessianVector H1 query (v k.succ.castSucc) -
      (InnerProductSpace.toDual ℝ E).symm (DG (v k.succ.castSucc)))
  rw [hresp, smul_smul, inv_mul_cancel₀ (mul_ne_zero hscale (ne_of_gt hw)), one_smul]
  module

theorem actual_public_amplifier_shell_boundary_decoder
    {A0 B0 W : Type*}
    [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
    [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    (C : A0 ≃ₗᵢ[ℝ] B0) (q nu : ℝ)
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hhalf : delta ≤ omega / 2)
    (n : ℕ) (v : Fin (n + 3) → FangqingAmplifier.PhysicalSpace A0 B0 W)
    (hv : Orthonormal ℝ v) (k : Fin (n + 1))
    (phi : ℝ → ℝ) (R A s gain scale : ℝ) (hscale : scale ≠ 0)
    (hRA : A ≤ R) (hA : omega / 2 < A)
    (handle : FangqingAmplifier.PhysicalSpace A0 B0 W) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t) :
    let H1 := fun z => inactiveShell (FangqingAmplifier.QPhysical q nu C)
      (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) z) R gain z -
        localizedSeed theta phi R A (s * A) handle z
    v k.succ.succ = (2 : ℝ) • v k.succ.castSucc - v k.castSucc.castSucc -
      (scale * omega)⁻¹ •
        (scalarHessianVector H1 ((omega / 2) • v k.succ.castSucc) (v k.succ.castSucc) -
          FangqingAmplifier.HPhysical q nu C (v k.succ.castSucc)) := by
  let DG : FangqingAmplifier.PhysicalSpace A0 B0 W →L[ℝ]
      (FangqingAmplifier.PhysicalSpace A0 B0 W →L[ℝ] ℝ) :=
    (innerSL ℝ).comp (FangqingAmplifier.HPhysical q nu C)
  have hpub : (InnerProductSpace.toDual ℝ (FangqingAmplifier.PhysicalSpace A0 B0 W)).symm
      (DG (v k.succ.castSucc)) = FangqingAmplifier.HPhysical q nu C (v k.succ.castSucc) := by
    apply (InnerProductSpace.toDual ℝ (FangqingAmplifier.PhysicalSpace A0 B0 W)).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    rfl
  have hh0 := actual_shell_signed_boundary_decoder P delta omega hd hhalf n v hv k
    (FangqingAmplifier.QPhysical q nu C) DG DG
    (FangqingAmplifier.hasFDerivAt_QPhysical q nu C) DG.hasFDerivAt
    phi R A s gain scale hscale hRA hA handle hh hphi
  simpa only [hpub] using hh0

end FangqingActualShellBoundaryAcquisition
end

section
-- Source component: PrefixSimulatorSymmetryObstruction-typed-infinity.lean

namespace FangqingPrefixSimulatorSymmetryObstruction

open MeasureTheory
open scoped ENNReal

theorem prefix_simulation_event_has_probability_at_most_half
    {Omega Prefix Response : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (flip : Omega → Omega) (hflip : MeasurePreserving flip mu mu)
    (viewData : Omega → Prefix) (response : Omega → Response)
    (hprefix : ∀ omega, viewData (flip omega) = viewData omega)
    (hresponse : ∀ omega, response (flip omega) ≠ response omega)
    (simulator : Prefix → Response)
    (good : Set Omega) (hgood : MeasurableSet good)
    (hsim : ∀ omega ∈ good, response omega = simulator (viewData omega)) :
    mu.real good ≤ 1 / 2 := by
  have hdisjoint : Disjoint good (flip ⁻¹' good) := by
    apply Set.disjoint_left.mpr
    intro omega hg hfg
    have hr := hsim (flip omega) hfg
    rw [hprefix omega] at hr
    exact hresponse omega (hr.trans (hsim omega hg).symm)
  have hfg : MeasurableSet (flip ⁻¹' good) := hflip.measurable hgood
  have hm : mu (flip ⁻¹' good) = mu good := hflip.measure_preimage hgood.nullMeasurableSet
  have hsum : mu good + mu good ≤ 1 := by
    calc
      _ = mu good + mu (flip ⁻¹' good) := congrArg (fun t => mu good + t) hm.symm
      _ = mu (good ∪ flip ⁻¹' good) := (measure_union hdisjoint hfg).symm
      _ ≤ 1 := (measure_mono (Set.subset_univ _)).trans_eq (measure_univ)
  have hr := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) hsum
  rw [ENNReal.toReal_add (measure_ne_top mu good) (measure_ne_top mu good),
    ENNReal.toReal_one] at hr
  change mu.real good + mu.real good ≤ 1 at hr
  linarith only [hr]

theorem no_prefix_simulation_on_more_than_half
    {Omega Prefix Response : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (flip : Omega → Omega) (hflip : MeasurePreserving flip mu mu)
    (viewData : Omega → Prefix) (response : Omega → Response)
    (hprefix : ∀ omega, viewData (flip omega) = viewData omega)
    (hresponse : ∀ omega, response (flip omega) ≠ response omega)
    (good : Set Omega) (hgood : MeasurableSet good) (hprob : 1 / 2 < mu.real good) :
    ¬ ∃ simulator : Prefix → Response,
      ∀ omega ∈ good, response omega = simulator (viewData omega) := by
  rintro ⟨simulator, hsim⟩
  have hh := prefix_simulation_event_has_probability_at_most_half mu flip hflip viewData response
    hprefix hresponse simulator good hgood hsim
  linarith only [hh, hprob]

end FangqingPrefixSimulatorSymmetryObstruction
end

section
-- Source component: HaarColumnSignFlip.lean

namespace FangqingHaarColumnSignFlip

open MeasureTheory FangqingOrthogonalHaar FangqingAdaptiveHaarProduct

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {m : ℕ}

def flipColumn (b : Fin m → E) (j : Fin m) : FangqingOrthogonalHaar.Group E :=
  Unitary.linearIsometryEquiv.symm ((ℝ ∙ b j)ᗮ.reflection)

theorem flipColumn_apply
    (b : Fin m → E) (hb : Orthonormal ℝ b) (j i : Fin m) :
    flipColumn b j • b i = if i = j then -b i else b i := by
  change (ℝ ∙ b j)ᗮ.reflection (b i) = _
  by_cases hij : i = j
  · subst i
    rw [if_pos rfl]
    exact Submodule.reflection_orthogonalComplement_singleton_eq_neg (b j)
  · rw [if_neg hij]
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    simpa only [orthonormal_iff_ite.mp hb, if_neg (Ne.symm hij)]

theorem actual_rotated_frame_flip
    (b : Fin m → E) (hb : Orthonormal ℝ b)
    (j : Fin m) (g : FangqingOrthogonalHaar.Group E) (i : Fin m) :
    frame b (g * flipColumn b j) i =
      if i = j then -(frame b g i) else frame b g i := by
  rw [frame, mul_smul, flipColumn_apply b hb j i]
  by_cases hij : i = j <;> simp [hij, frame]

theorem actual_prefix_unchanged
    (b : Fin m → E) (hb : Orthonormal ℝ b)
    (j : Fin m) (k : ℕ) (hj : k ≤ j.val) (g : FangqingOrthogonalHaar.Group E) :
    FangqingPrefixAdaptedModel.mask k (frame b (g * flipColumn b j)) =
      FangqingPrefixAdaptedModel.mask k (frame b g) := by
  funext i
  unfold FangqingPrefixAdaptedModel.mask
  by_cases hi : i.val < k
  · have hij : i ≠ j := by intro he; subst i; omega
    rw [if_pos hi, if_pos hi, actual_rotated_frame_flip b hb j g i, if_neg hij]
  · rw [if_neg hi, if_neg hi]

theorem rightHaar_flipColumn_preserving (b : Fin m → E) (j : Fin m) :
    MeasurePreserving (fun g : FangqingOrthogonalHaar.Group E => g * flipColumn b j)
      (rightHaar E) (rightHaar E) := by
  letI : MeasurableMul₂ (FangqingOrthogonalHaar.Group E) := ⟨continuous_mul.measurable⟩
  exact measurePreserving_mul_right (rightHaar E) (flipColumn b j)

theorem product_flipColumn_preserving
    {Seed : Type*} [MeasurableSpace Seed] (sigma : Measure Seed) [SFinite sigma]
    (b : Fin m → E) (j : Fin m) :
    MeasurePreserving (fun x : Seed × FangqingOrthogonalHaar.Group E =>
      (x.1, x.2 * flipColumn b j))
      (sigma.prod (rightHaar E)) (sigma.prod (rightHaar E)) :=
  (MeasurePreserving.id sigma).prod (rightHaar_flipColumn_preserving b j)

theorem actual_haar_prefix_simulation_probability_bound
    {Seed Response : Type*} [MeasurableSpace Seed]
    (sigma : Measure Seed) [IsProbabilityMeasure sigma]
    (b : Fin m → E) (hb : Orthonormal ℝ b) (j : Fin m) (k : ℕ) (hj : k ≤ j.val)
    (response : Seed × FangqingOrthogonalHaar.Group E → Response)
    (hresponse : ∀ seed g, response (seed, g * flipColumn b j) ≠ response (seed, g))
    (simulator : Seed × (Fin m → E) → Response)
    (good : Set (Seed × FangqingOrthogonalHaar.Group E)) (hgood : MeasurableSet good)
    (hsim : ∀ x ∈ good, response x =
      simulator (x.1, FangqingPrefixAdaptedModel.mask k (frame b x.2))) :
    (sigma.prod (rightHaar E)).real good ≤ 1 / 2 := by
  apply FangqingPrefixSimulatorSymmetryObstruction.prefix_simulation_event_has_probability_at_most_half
    (sigma.prod (rightHaar E))
    (fun x : Seed × FangqingOrthogonalHaar.Group E => (x.1, x.2 * flipColumn b j))
    (product_flipColumn_preserving sigma b j)
    (fun x : Seed × FangqingOrthogonalHaar.Group E =>
      (x.1, FangqingPrefixAdaptedModel.mask k (frame b x.2)))
    response ?_ (fun x => hresponse x.1 x.2) simulator good hgood hsim
  intro x
  exact congrArg (fun V => (x.1, V)) (actual_prefix_unchanged b hb j k hj x.2)

end
end FangqingHaarColumnSignFlip
end

section
-- Source component: LateGateKnownSphere.lean

namespace FangqingLateGateKnownSphere

theorem profile_has_public_transition_point
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (lo hi : ℝ) (hlo : 0 ≤ lo) (hlt : lo < hi)
    (hinner : theta lo = 1) (houter : theta hi = 0) :
    ∃ t : ℝ, lo < t ∧ t < hi ∧ 0 < t ∧ deriv theta t < 0 := by
  obtain ⟨t, ht, hd⟩ := exists_deriv_eq_slope theta hlt htheta.continuous.continuousOn
    htheta.differentiableOn
  refine ⟨t, ht.1, ht.2, hlo.trans_lt ht.1, ?_⟩
  rw [hd, houter, hinner]
  exact div_neg_of_neg_of_pos (by norm_num) (sub_pos.mpr hlt)

noncomputable def knownOffset (ell t alpha beta : ℝ) : ℝ :=
  Real.sqrt (ell ^ 2 * t - alpha ^ 2 - beta ^ 2)

theorem knownOffset_properties
    (ell t alpha beta : ℝ) (hsmall : alpha ^ 2 + beta ^ 2 < ell ^ 2 * t) :
    0 < knownOffset ell t alpha beta ∧
      knownOffset ell t alpha beta ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t := by
  have hx : 0 < ell ^ 2 * t - alpha ^ 2 - beta ^ 2 := by linarith only [hsmall]
  refine ⟨Real.sqrt_pos.mpr hx, ?_⟩
  rw [knownOffset, Real.sq_sqrt hx.le]
  ring

theorem two_last_coefficients_residual_bound
    (q omega tau Cw z1 z2 : ℝ) (hq : 0 < q) (hw : 0 ≤ omega) (hC : 0 ≤ Cw)
    (hz1 : 0 ≤ z1) (hz2 : 0 ≤ z2)
    (hup1 : z1 ≤ 2 * Cw * q * omega) (hup2 : z2 ≤ 2 * Cw * q * omega) :
    (tau * z1) ^ 2 + (tau * z2) ^ 2 ≤
      8 * Cw ^ 2 * (tau * (q * Real.sqrt q * omega)) ^ 2 / q := by
  have hK : 0 ≤ 2 * Cw * q * omega := by positivity
  have hs1 := (sq_le_sq₀ hz1 hK).mpr hup1
  have hs2 := (sq_le_sq₀ hz2 hK).mpr hup2
  have hs : z1 ^ 2 + z2 ^ 2 ≤ 8 * Cw ^ 2 * q ^ 2 * omega ^ 2 := by
    nlinarith only [hs1, hs2]
  calc
    _ = tau ^ 2 * (z1 ^ 2 + z2 ^ 2) := by ring
    _ ≤ tau ^ 2 * (8 * Cw ^ 2 * q ^ 2 * omega ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg tau)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hq.le]
      field_simp

theorem three_last_coefficients_residual_bound
    (q omega tau Cw z1 z2 z3 : ℝ) (hq : 0 < q) (hw : 0 ≤ omega) (hC : 0 ≤ Cw)
    (hz1 : 0 ≤ z1) (hz2 : 0 ≤ z2) (hz3 : 0 ≤ z3)
    (hup1 : z1 ≤ 2 * Cw * q * omega) (hup2 : z2 ≤ 2 * Cw * q * omega)
    (hup3 : z3 ≤ 2 * Cw * q * omega) :
    (tau * z1) ^ 2 + (tau * z2) ^ 2 + (tau * z3) ^ 2 ≤
      12 * Cw ^ 2 * (tau * (q * Real.sqrt q * omega)) ^ 2 / q := by
  have hK : 0 ≤ 2 * Cw * q * omega := by positivity
  have hs1 := (sq_le_sq₀ hz1 hK).mpr hup1
  have hs2 := (sq_le_sq₀ hz2 hK).mpr hup2
  have hs3 := (sq_le_sq₀ hz3 hK).mpr hup3
  have hs : z1 ^ 2 + z2 ^ 2 + z3 ^ 2 ≤ 12 * Cw ^ 2 * q ^ 2 * omega ^ 2 := by
    nlinarith only [hs1, hs2, hs3]
  calc
    _ = tau ^ 2 * (z1 ^ 2 + z2 ^ 2 + z3 ^ 2) := by ring
    _ ≤ tau ^ 2 * (12 * Cw ^ 2 * q ^ 2 * omega ^ 2) :=
      mul_le_mul_of_nonneg_left hs (sq_nonneg tau)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hq.le]
      field_simp

end FangqingLateGateKnownSphere
end

section
-- Source component: BundledCoordinateHessian.lean

namespace FangqingBundledCoordinateHessian

open FangqingLateGateRelaySlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_scalar_hessian_vector_eq_gradient_derivative
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (z v : E) :
    (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) z v) =
      fderiv ℝ (gradient f) z v := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hh := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp z
    (hfd z).hasFDerivAt
  have hd : HasFDerivAt (gradient f)
      ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ f) z)) z := by
    convert! hh using 1
  rw [hd.fderiv]
  rfl

section Coordinates

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_coordinate_slice_gradient_everywhere
    (G : PiLp 2 (fun _ : I => E) → ℝ) (hG : Differentiable ℝ G)
    (Z : PiLp 2 (fun _ : I => E)) (i : I) (z : E) :
    gradient (fun w : E => G (WithLp.toLp 2 (Function.update Z i w))) z =
      gradient G (WithLp.toLp 2 (Function.update Z i z)) i := by
  let U : PiLp 2 (fun _ : I => E) := WithLp.toLp 2 (Function.update Z i z)
  have hh := actual_bundle_coordinate_slice_gradient G hG U i
  have he : (fun w : E => G (WithLp.toLp 2 (Function.update U i w))) =
      (fun w : E => G (WithLp.toLp 2 (Function.update Z i w))) := by
    funext w
    congr 1
    ext j
    by_cases hj : j = i <;> simp [U, Function.update_apply, hj]
  rw [he] at hh
  simpa only [U, PiLp.toLp_apply, Function.update_self] using hh

theorem actual_full_hessian_coordinate_projection
    (G : PiLp 2 (fun _ : I => E) → ℝ) (hG : Differentiable ℝ G)
    (hGrad : Differentiable ℝ (gradient G))
    (Z : PiLp 2 (fun _ : I => E)) (i : I) (v : E) :
    fderiv ℝ (gradient (fun w : E => G (WithLp.toLp 2 (Function.update Z i w)))) (Z i) v =
      fderiv ℝ (gradient G) Z (coordinateIsometry i v) i := by
  let C := coordinateIsometry (E := E) i
  let U : E → PiLp 2 (fun _ : I => E) := fun z => WithLp.toLp 2 (Function.update Z i z)
  let P : PiLp 2 (fun _ : I => E) →L[ℝ] E := PiLp.proj 2 (fun _ : I => E) i
  have hU : U = fun z : E => Z + C (z - Z i) := by
    funext z
    ext j
    by_cases hj : j = i
    · subst j
      simp [U, C, coordinateIsometry]
    · simp [U, C, coordinateIsometry, Function.update_of_ne hj, hj]
  have hUz : U (Z i) = Z := by ext j; simp [U]
  have hc0 := C.toContinuousLinearMap.hasFDerivAt.comp (Z i)
    ((hasFDerivAt_id (Z i)).sub_const (Z i))
  have hc : HasFDerivAt U C.toContinuousLinearMap (Z i) := by
    rw [hU]
    convert! hc0.const_add Z using 1 <;>
      simp only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id]
  have hGz : DifferentiableAt ℝ (gradient G) (U (Z i)) := by
    rw [hUz]
    exact hGrad Z
  have hh := P.hasFDerivAt.comp (Z i) (hGz.hasFDerivAt.comp (Z i) hc)
  have hfun : gradient (fun w : E => G (WithLp.toLp 2 (Function.update Z i w))) =
      (fun w : E => P (gradient G (U w))) := by
    funext w
    exact actual_coordinate_slice_gradient_everywhere G hG Z i w
  rw [hfun]
  have hd : HasFDerivAt (fun w : E => P (gradient G (U w)))
      (P.comp ((fderiv ℝ (gradient G) Z).comp C.toContinuousLinearMap)) (Z i) := by
    convert! hh using 1 <;> simp only [hUz, Function.comp_def]
  rw [hd.fderiv]
  rfl

end Coordinates
end FangqingBundledCoordinateHessian
end

section
-- Source component: RelayFirstPacketHessian.lean

namespace FangqingRelayFirstPacketHessian

open FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingLateGateRelaySlice FangqingBundledCoordinateHessian FangqingActualShellBoundaryAcquisition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_assembled_first_y_slice
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (W : FlatJoint n E) (z : E) :
    assembled n bet lam a sigma reward h0 h1 m0 m1 gate
      (WithLp.toLp 2 (Function.update W (1, 0) z)) =
    assembled n bet lam a sigma reward h0 h1 m0 m1 gate W +
      endpoint bet lam (h1 0) (m1 0) (W (0, 0)) z -
      endpoint bet lam (h1 0) (m1 0) (W (0, 0)) (W (1, 0)) := by
  let x : Fin (n + 1) → E := fun t => W (0, t)
  let y : Fin (n + 1) → E := fun t => W (1, t)
  let s : Fin (n + 1) → E := fun t => W (2, t)
  have hx : (fun t => Function.update W (1, 0) z (0, t)) = x := by
    funext t
    simp [x, Function.update_apply, show (0 : Fin 3) ≠ 1 by decide]
  have hy : (fun t => Function.update W (1, 0) z (1, t)) = Function.update y 0 z := by
    funext t
    by_cases ht : t = 0 <;> simp [y, Function.update_apply, ht]
  have hs : (fun t => Function.update W (1, 0) z (2, t)) = s := by
    funext t
    simp [s, Function.update_apply, show (2 : Fin 3) ≠ 1 by decide]
  rw [assembled_eq_family, assembled_eq_family]
  simp only [PiLp.toLp_apply]
  rw [hx, hy, hs]
  have hh := family_y_vary n bet lam a sigma reward h0 h1 m0 m1 gate x y s 0 (z - y 0) 1
  have he : y 0 + (1 : ℝ) • (z - y 0) = z := by module
  simp only [vary, he, incoming, Fin.cases_zero, one_mul] at hh
  rw [hh]
  dsimp only [endpoint, delta, x, y, s]
  ring

theorem affine_quadratic_minus_hessian
    (H : E → ℝ) (hH : ContDiff ℝ 2 H) (x z v w : E) (K lam c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun u => K + lam * inner ℝ x u + c / 2 * ‖u‖ ^ 2 - H u)) z v w =
      c * inner ℝ v w - fderiv ℝ (fderiv ℝ H) z v w := by
  let D : E →L[ℝ] (E →L[ℝ] ℝ) := c • innerSL ℝ
  have hfirst : fderiv ℝ (fun u => K + lam * inner ℝ x u + c / 2 * ‖u‖ ^ 2 - H u) =
      (fun u => lam • innerSL ℝ x + D u - fderiv ℝ H u) := by
    funext u
    have hd := ((((innerSL ℝ x).hasFDerivAt.const_mul lam).const_add K).add
      ((hasFDerivAt_id u).norm_sq.const_mul (c / 2))).sub
        (hH.differentiable (by norm_num) u).hasFDerivAt
    have hd' : HasFDerivAt
        (fun u => K + lam * inner ℝ x u + c / 2 * ‖u‖ ^ 2 - H u)
        (lam • innerSL ℝ x + D u - fderiv ℝ H u) u := by
      convert! hd using 1
      ext r
      simp only [D, innerSL_apply_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, id_eq, smul_eq_mul]
      ring
      rfl
    exact hd'.fderiv
  rw [hfirst]
  have hdiff : Differentiable ℝ (fderiv ℝ H) :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hh := (D.hasFDerivAt.const_add (lam • innerSL ℝ x)).sub (hdiff z).hasFDerivAt
  have hd : HasFDerivAt (fun u => lam • innerSL ℝ x + D u - fderiv ℝ H u)
      (D - fderiv ℝ (fderiv ℝ H) z) z := by
    convert! hh using 1
  rw [hd.fderiv]
  simp only [D, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    innerSL_apply_apply, smul_eq_mul]
  rfl

theorem actual_full_relay_reads_first_shell_hessian
    (n : ℕ) (bet lam a sigma reward c : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (H : E → ℝ) (hH : ContDiff ℝ 2 H)
    (hfirst : h1 0 = fun z => H z - c / 2 * ‖z‖ ^ 2)
    (hJ : ContDiff ℝ 2 (assembled n bet lam a sigma reward h0 h1 m0 m1 gate))
    (W : FlatJoint n E) (v : E) :
    -(fderiv ℝ (gradient (assembled n bet lam a sigma reward h0 h1 m0 m1 gate)) W
        (coordinateIsometry (1, (0 : Fin (n + 1))) v)) (1, 0) + c • v =
      scalarHessianVector H (W (1, 0)) v := by
  let J := assembled n bet lam a sigma reward h0 h1 m0 m1 gate
  let f : E → ℝ := fun z => J (WithLp.toLp 2 (Function.update W (1, 0) z))
  let K := J W - endpoint bet lam (h1 0) (m1 0) (W (0, 0)) (W (1, 0)) +
    bet / 2 * ‖W (0, 0)‖ ^ 2 + m1 0
  have he : f = fun z => K + lam * inner ℝ (W (0, 0)) z + c / 2 * ‖z‖ ^ 2 - H z := by
    funext z
    dsimp only [f, J]
    rw [actual_assembled_first_y_slice, hfirst]
    dsimp only [endpoint, K, J]
    rw [hfirst]
    ring
  have hfdiff : Differentiable ℝ (fderiv ℝ J) :=
    (hJ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hGrad : Differentiable ℝ (gradient J) := by
    exact (InnerProductSpace.toDual ℝ (FlatJoint n E)).symm.toContinuousLinearEquiv.differentiable.comp hfdiff
  have hp := actual_full_hessian_coordinate_projection J (hJ.differentiable (by norm_num)) hGrad
    W (1, (0 : Fin (n + 1))) v
  have hf : ContDiff ℝ 2 f := by
    rw [he]
    exact ((contDiff_const.add
      (contDiff_const.mul (contDiff_const.inner ℝ contDiff_id))).add
        (contDiff_const.mul (contDiff_id.norm_sq ℝ))).sub hH
  have hv : (fderiv ℝ (gradient J) W (coordinateIsometry (1, (0 : Fin (n + 1))) v)) (1, 0) =
      c • v - scalarHessianVector H (W (1, 0)) v := by
    apply ext_inner_right ℝ
    intro w
    rw [← hp]
    change inner ℝ (fderiv ℝ (gradient f) (W (1, 0)) v) w = _
    rw [← actual_scalar_hessian_vector_eq_gradient_derivative f hf,
      show (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fderiv ℝ f) (W (1, 0)) v) =
        scalarHessianVector f (W (1, 0)) v from rfl,
      scalarHessianVector_inner, he,
      affine_quadratic_minus_hessian H hH (W (0, 0)) (W (1, 0)) v w K lam c]
    simp only [inner_sub_left, real_inner_smul_left, scalarHessianVector_inner]
  change -(fderiv ℝ (gradient J) W (coordinateIsometry (1, (0 : Fin (n + 1))) v)) (1, 0) + c • v = _
  rw [hv]
  module

end FangqingRelayFirstPacketHessian
end

section
-- Source component: RelayGateGradientSignal.lean

namespace FangqingRelayGateGradientSignal

open FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingLateGateRelaySlice FangqingLateGateLeakageKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_assembled_s_slice
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (W : FlatJoint n E) (i : Fin (n + 1)) (z : E) :
    assembled n bet lam a sigma reward h0 h1 m0 m1 gate
      (WithLp.toLp 2 (Function.update W (2, i) z)) =
      family n bet lam a sigma reward h0 h1 m0 m1 gate
        (fun t => W (0, t)) (fun t => W (1, t)) (Function.update (fun t => W (2, t)) i z) := by
  rw [assembled_eq_family]
  have hx : (fun t => Function.update W (2, i) z (0, t)) = fun t => W (0, t) := by
    funext t
    simp [Function.update_apply, show (0 : Fin 3) ≠ 2 by decide]
  have hy : (fun t => Function.update W (2, i) z (1, t)) = fun t => W (1, t) := by
    funext t
    simp [Function.update_apply, show (1 : Fin 3) ≠ 2 by decide]
  have hs : (fun t => Function.update W (2, i) z (2, t)) =
      Function.update (fun t => W (2, t)) i z := by
    funext t
    by_cases ht : t = i <;> simp [Function.update_apply, ht]
  simpa only [PiLp.toLp_apply, hx, hy, hs]

theorem actual_full_relay_s_gradient
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ)
    (hJ : Differentiable ℝ (assembled n bet lam a sigma reward h0 h1 m0 m1 gate))
    (W : FlatJoint n E) (i : Fin (n + 1)) (p : E)
    (hp : HasGradientAt (gateExt n gate i) p (W (2, i))) :
    gradient (assembled n bet lam a sigma reward h0 h1 m0 m1 gate) W (2, i) =
      coefficient n reward h0 h1 m0 m1 (fun t => W (1, t)) i • p -
        sigma • (W (2, i) - a • W (0, i)) := by
  have he : (fun z => assembled n bet lam a sigma reward h0 h1 m0 m1 gate
      (WithLp.toLp 2 (Function.update W (2, i) z))) =
      (fun z => family n bet lam a sigma reward h0 h1 m0 m1 gate
        (fun t => W (0, t)) (fun t => W (1, t))
          (Function.update (fun t => W (2, t)) i z)) := by
    funext z
    exact actual_assembled_s_slice n bet lam a sigma reward h0 h1 m0 m1 gate W i z
  have hh := actual_bundle_coordinate_slice_gradient
    (assembled n bet lam a sigma reward h0 h1 m0 m1 gate) hJ W (2, i)
  rw [he, actual_relay_s_slice_gradient n bet lam a sigma reward h0 h1 m0 m1 gate
    (fun t => W (0, t)) (fun t => W (1, t)) (fun t => W (2, t)) i p hp] at hh
  exact hh.symm

theorem actual_full_relay_known_sphere_center_decoder
    (n : ℕ) (bet lam a sigma reward ell : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (star : Fin n → E)
    (hJ : Differentiable ℝ (assembled n bet lam a sigma reward h0 h1 m0 m1
      (fun j => radialGate theta a ell (star j))))
    (W : FlatJoint n E) (i : Fin n)
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (known : E)
    (r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell)
    (hstar : star i = known + alpha • v 1 + beta • v 2)
    (hquery : W (2, i.castSucc) = a • (known + r • v 0))
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0)
    (hderiv : deriv theta t0 ≠ 0)
    (hB : coefficient n reward h0 h1 m0 m1 (fun t => W (1, t)) i.castSucc ≠ 0) :
    star i = a⁻¹ • (W (2, i.castSucc) -
      (coefficient n reward h0 h1 m0 m1 (fun t => W (1, t)) i.castSucc *
        (2 * deriv theta t0 / (a ^ 2 * ell ^ 2)))⁻¹ •
      (gradient (assembled n bet lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j))) W (2, i.castSucc) +
          sigma • (W (2, i.castSucc) - a • W (0, i.castSucc)))) := by
  let C := 2 * deriv theta t0 / (a ^ 2 * ell ^ 2)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hderiv)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (pow_ne_zero 2 (ne_of_gt hell)))
  have hgate : HasGradientAt
      (gateExt n (fun j => radialGate theta a ell (star j)) i.castSucc)
      (C • (W (2, i.castSucc) - a • star i)) (W (2, i.castSucc)) := by
    have hh := radialGate_hasGradientAt theta a ell (star i) (W (2, i.castSucc)) htheta
    have harg := known_query_radial_argument v hv known a ell r alpha beta t0 ha hell hsphere
    rw [← hstar, ← hquery] at harg
    simpa only [gateExt, Fin.lastCases_castSucc, eta, harg, neg_div, neg_neg, C] using hh
  rw [actual_full_relay_s_gradient n bet lam a sigma reward h0 h1 m0 m1
    (fun j => radialGate theta a ell (star j)) hJ W i.castSucc _ hgate]
  let B := coefficient n reward h0 h1 m0 m1 (fun t => W (1, t)) i.castSucc
  have hc : B • (C • (W (2, i.castSucc) - a • star i)) -
      sigma • (W (2, i.castSucc) - a • W (0, i.castSucc)) +
      sigma • (W (2, i.castSucc) - a • W (0, i.castSucc)) =
      (B * C) • (W (2, i.castSucc) - a • star i) := by module
  change star i = a⁻¹ • (W (2, i.castSucc) - (B * C)⁻¹ •
    (B • (C • (W (2, i.castSucc) - a • star i)) -
      sigma • (W (2, i.castSucc) - a • W (0, i.castSucc)) +
      sigma • (W (2, i.castSucc) - a • W (0, i.castSucc))))
  rw [hc, smul_smul, inv_mul_cancel₀ (mul_ne_zero hB hC), one_smul]
  have he : W (2, i.castSucc) - (W (2, i.castSucc) - a • star i) = a • star i := by module
  rw [he, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]

end FangqingRelayGateGradientSignal
end

section
-- Source component: TwoTailSameResponseDecoder.lean

namespace FangqingTwoTailSameResponseDecoder

open FangqingAmplifier FangqingPacketLeakage FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingPublicShellProfiles FangqingRelayStationarity FangqingRelayAnalyticAssembly
  FangqingRelayJointReindexing FangqingLateGateRelaySlice FangqingActualShellBoundaryAcquisition
  FangqingRelayFirstPacketHessian FangqingRelayGateGradientSignal

noncomputable section

variable {A0 B0 W0 : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W0] [InnerProductSpace ℝ W0] [CompleteSpace W0]

abbrev Space := PhysicalSpace A0 B0 W0

def boundaryDecoder (F : FlatJoint 1 (Space (A0 := A0) (B0 := B0) (W0 := W0)) → ℝ)
    (point : FlatJoint 1 (Space (A0 := A0) (B0 := B0) (W0 := W0)))
    (C : A0 ≃ₗᵢ[ℝ] B0) (q nu c scale omega : ℝ) (previous known : Space (A0 := A0) (B0 := B0) (W0 := W0)) :
    Space (A0 := A0) (B0 := B0) (W0 := W0) :=
  (2 : ℝ) • known - previous - (scale * omega)⁻¹ •
    (-(fderiv ℝ (gradient F) point (coordinateIsometry (1, (0 : Fin 2)) known)) (1, 0) +
      c • known - HPhysical q nu C known)

def centerDecoder (F : FlatJoint 1 (Space (A0 := A0) (B0 := B0) (W0 := W0)) → ℝ)
    (point : FlatJoint 1 (Space (A0 := A0) (B0 := B0) (W0 := W0)))
    (a sigma B Ctheta : ℝ) : Space (A0 := A0) (B0 := B0) (W0 := W0) :=
  a⁻¹ • (point (2, 0) - (B * Ctheta)⁻¹ •
    (gradient F point (2, 0) + sigma • (point (2, 0) - a • point (0, 0))))

theorem actual_original_F2_same_response_recovers_two_tails
    (C : A0 ≃ₗᵢ[ℝ] B0) (q nu : ℝ)
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hhalf : delta ≤ omega / 2)
    (n : ℕ) (V : Fin (n + 3) → Space (A0 := A0) (B0 := B0) (W0 := W0))
    (hV : Orthonormal ℝ V) (k : Fin (n + 1))
    (phi : ℝ → ℝ) (R A s gain scale : ℝ) (hscale : scale ≠ 0)
    (hRA : A ≤ R) (hA : omega / 2 < A)
    (handle : Space (A0 := A0) (B0 := B0) (W0 := W0)) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t)
    (bet lam a sigma reward ell c : ℝ)
    (h0 h1 : Fin 2 → Space (A0 := A0) (B0 := B0) (W0 := W0) → ℝ) (m0 m1 : Fin 2 → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (star : Space (A0 := A0) (B0 := B0) (W0 := W0))
    (point : FlatJoint 1 (Space (A0 := A0) (B0 := B0) (W0 := W0)))
    (directions : Fin 3 → Space (A0 := A0) (B0 := B0) (W0 := W0))
    (hdir : Orthonormal ℝ directions)
    (knownPart : Space (A0 := A0) (B0 := B0) (W0 := W0))
    (r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell) (hbeta : beta ≠ 0)
    (hstar : star = knownPart + alpha • directions 1 + beta • directions 2)
    (hfirst : directions 1 = V k.succ.succ)
    (hy : point (1, 0) = (omega / 2) • V k.succ.castSucc)
    (hs : point (2, 0) = a • (knownPart + r • directions 0))
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0)
    (hderiv : deriv theta t0 ≠ 0)
    (hB : coefficient 1 reward h0 h1 m0 m1 (fun t => point (1, t)) 0 ≠ 0)
    (hHclass : ContDiff ℝ 2 (fun z => inactiveShell (QPhysical q nu C)
      (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n V) z) R gain z -
        localizedSeed FangqingPublicShellProfiles.theta phi R A (s * A) handle z))
    (hendpoint : h1 0 = fun z =>
      (inactiveShell (QPhysical q nu C)
        (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n V) z) R gain z -
          localizedSeed FangqingPublicShellProfiles.theta phi R A (s * A) handle z) - c / 2 * ‖z‖ ^ 2)
    (hJ : ContDiff ℝ 2 (assembled 1 bet lam a sigma reward h0 h1 m0 m1
      (fun _ => radialGate theta a ell star))) :
    let F := assembled 1 bet lam a sigma reward h0 h1 m0 m1 (fun _ => radialGate theta a ell star)
    let B := coefficient 1 reward h0 h1 m0 m1 (fun t => point (1, t)) 0
    let Ctheta := 2 * deriv theta t0 / (a ^ 2 * ell ^ 2)
    boundaryDecoder F point C q nu c scale omega (V k.castSucc.castSucc) (V k.succ.castSucc) = directions 1 ∧
    beta⁻¹ • (centerDecoder F point a sigma B Ctheta - knownPart -
      alpha • boundaryDecoder F point C q nu c scale omega
        (V k.castSucc.castSucc) (V k.succ.castSucc)) = directions 2 := by
  intro F B Ctheta
  let H := fun z => inactiveShell (QPhysical q nu C)
      (fun z => scale * edgeSum (FlatCubic.edge P delta omega) (pathDirection n V) z) R gain z -
        localizedSeed FangqingPublicShellProfiles.theta phi R A (s * A) handle z
  have hbdy := actual_public_amplifier_shell_boundary_decoder C q nu P delta omega hd hhalf n V hV k
    phi R A s gain scale hscale hRA hA handle hh hphi
  have hread := actual_full_relay_reads_first_shell_hessian 1 bet lam a sigma reward c h0 h1 m0 m1
    (fun _ => radialGate theta a ell star) H hHclass hendpoint hJ point (V k.succ.castSucc)
  rw [hy] at hread
  have hdec : boundaryDecoder F point C q nu c scale omega
      (V k.castSucc.castSucc) (V k.succ.castSucc) = directions 1 := by
    dsimp only at hbdy
    rw [← hread] at hbdy
    exact hbdy.symm.trans hfirst.symm
  have hcenter := actual_full_relay_known_sphere_center_decoder 1 bet lam a sigma reward ell h0 h1 m0 m1
    theta htheta (fun _ => star) (hJ.differentiable (by norm_num)) point 0 directions hdir knownPart
    r alpha beta t0 ha hell hstar hs hsphere hderiv hB
  change star = centerDecoder F point a sigma B Ctheta at hcenter
  refine ⟨hdec, ?_⟩
  rw [hdec, ← hcenter, hstar]
  have he : knownPart + alpha • directions 1 + beta • directions 2 -
      knownPart - alpha • directions 1 = beta • directions 2 := by module
  rw [he, smul_smul, inv_mul_cancel₀ hbeta, one_smul]

end
end FangqingTwoTailSameResponseDecoder
end

section
-- Source component: ObservableGateCenterDecoder.lean

namespace FangqingObservableGateCenterDecoder

open FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingRelayGateGradientSignal FangqingLateGateLeakageKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def measuredMultiplier (a r : ℝ) (knownDirection signal : E) : ℝ :=
  inner ℝ knownDirection signal / (a * r)

noncomputable def observableCenter (a r : ℝ) (knownDirection query signal : E) : E :=
  a⁻¹ • (query - (measuredMultiplier a r knownDirection signal)⁻¹ • signal)

noncomputable def centerFromAnswer (a sigma r : ℝ) (knownDirection : E)
    (point : FlatJoint 1 E) (answer : ℝ × FlatJoint 1 E × (FlatJoint 1 E →L[ℝ] FlatJoint 1 E)) : E :=
  observableCenter a r knownDirection (point (2, 0))
    (answer.2.1 (2, 0) + sigma • (point (2, 0) - a • point (0, 0)))

theorem actual_center_decoder_needs_no_private_normalizer
    (bet lam a sigma reward ell : ℝ)
    (h0 h1 : Fin 2 → E → ℝ) (m0 m1 : Fin 2 → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta) (star : E)
    (hJ : Differentiable ℝ (assembled 1 bet lam a sigma reward h0 h1 m0 m1
      (fun _ => radialGate theta a ell star)))
    (point : FlatJoint 1 E) (v : Fin 3 → E) (hv : Orthonormal ℝ v) (known : E)
    (r alpha beta t0 : ℝ) (ha : 0 < a) (hr : 0 < r) (hell : 0 < ell)
    (hstar : star = known + alpha • v 1 + beta • v 2)
    (hquery : point (2, 0) = a • (known + r • v 0))
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0)
    (hderiv : deriv theta t0 ≠ 0)
    (hB : coefficient 1 reward h0 h1 m0 m1 (fun t => point (1, t)) 0 ≠ 0) :
    let F := assembled 1 bet lam a sigma reward h0 h1 m0 m1 (fun _ => radialGate theta a ell star)
    let B := coefficient 1 reward h0 h1 m0 m1 (fun t => point (1, t)) 0
    let C := 2 * deriv theta t0 / (a ^ 2 * ell ^ 2)
    let signal := gradient F point (2, 0) + sigma • (point (2, 0) - a • point (0, 0))
    measuredMultiplier a r (v 0) signal = B * C ∧
      measuredMultiplier a r (v 0) signal ≠ 0 ∧
      centerFromAnswer a sigma r (v 0) point (FangqingShellPrefixLocality.bundle F point) = star := by
  intro F B C signal
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hderiv)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (pow_ne_zero 2 (ne_of_gt hell)))
  have hgate : HasGradientAt
      (gateExt 1 (fun _ => radialGate theta a ell star) (0 : Fin 2))
      (C • (point (2, 0) - a • star)) (point (2, 0)) := by
    have hfun : gateExt 1 (fun _ : Fin 1 => radialGate theta a ell star) (0 : Fin 2) =
        radialGate theta a ell star := by
      change Fin.lastCases (motive := fun _ : Fin 2 => E → ℝ) (fun _ : E => 0)
        (fun _ : Fin 1 => radialGate theta a ell star) (0 : Fin 1).castSucc = _
      rw [Fin.lastCases_castSucc]
    rw [hfun]
    have hh := radialGate_hasGradientAt theta a ell star (point (2, 0)) htheta
    have harg := known_query_radial_argument v hv known a ell r alpha beta t0 ha hell hsphere
    rw [← hstar, ← hquery] at harg
    simpa only [eta, harg, neg_div, neg_neg, C] using hh
  have hgrad := actual_full_relay_s_gradient 1 bet lam a sigma reward h0 h1 m0 m1
    (fun _ => radialGate theta a ell star) hJ point 0 _ hgate
  have hsignal : signal = (B * C) • (point (2, 0) - a • star) := by
    dsimp only [signal, F]
    rw [hgrad]
    change B • (C • (point (2, 0) - a • star)) -
      sigma • (point (2, 0) - a • point (0, 0)) +
      sigma • (point (2, 0) - a • point (0, 0)) = _
    module
  have hres : point (2, 0) - a • star = a • (r • v 0 - alpha • v 1 - beta • v 2) := by
    rw [hquery, hstar]
    module
  have h00 : inner ℝ (v 0) (v 0) = 1 := by simpa using (orthonormal_iff_ite.mp hv (0 : Fin 3) 0)
  have h01 : inner ℝ (v 0) (v 1) = 0 := by
    simpa using (orthonormal_iff_ite.mp hv (0 : Fin 3) 1)
  have h02 : inner ℝ (v 0) (v 2) = 0 := by
    simpa using (orthonormal_iff_ite.mp hv (0 : Fin 3) 2)
  have hinner : inner ℝ (v 0) (point (2, 0) - a • star) = a * r := by
    rw [hres]
    simp only [real_inner_smul_right, inner_sub_right, h00, h01, h02, mul_one, mul_zero, sub_zero]
  have hmeasured : measuredMultiplier a r (v 0) signal = B * C := by
    rw [measuredMultiplier, hsignal, real_inner_smul_right, hinner]
    field_simp [ne_of_gt ha, ne_of_gt hr]
  have hnonzero : measuredMultiplier a r (v 0) signal ≠ 0 := by
    rw [hmeasured]
    exact mul_ne_zero hB hC
  refine ⟨hmeasured, hnonzero, ?_⟩
  change observableCenter a r (v 0) (point (2, 0)) signal = star
  rw [observableCenter, hmeasured, hsignal, smul_smul, inv_mul_cancel₀ (mul_ne_zero hB hC), one_smul]
  have he : point (2, 0) - (point (2, 0) - a • star) = a • star := by module
  rw [he, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]

end FangqingObservableGateCenterDecoder
end

section
-- Source component: UnrevealedBulkSeparation.lean

/- Actual minimizer bulk coefficients imply a quantitative chamber
   separation on any sufficiently large unrevealed subset. -/

open scoped BigOperators

namespace OriginalUnrevealedBulkSeparation

open OriginalPacketDistanceGapBounds

noncomputable section

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

theorem distance_from_unrevealed_coefficients
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z w : E)
    (q omega : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ omega)
    (hcard : q / 4 ≤ (J.card : ℝ))
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z)
    (hsmall : ∀ i ∈ J, |inner ℝ (v i) w| ≤ q * omega) :
    distanceScale q omega ≤ ‖Z - w‖ := by
  have hcoef : ∀ i ∈ J, (2 * q * omega) ^ 2 ≤ (inner ℝ (v i) (Z - w)) ^ 2 := by
    intro i hi
    have hs : inner ℝ (v i) w ≤ q * omega := (le_abs_self _).trans (hsmall i hi)
    have hd : 2 * q * omega ≤ inner ℝ (v i) (Z - w) := by
      rw [inner_sub_right]
      linarith only [hbulk i hi, hs]
    have hp : 0 ≤ 2 * q * omega := by positivity
    exact (sq_le_sq₀ hp (hp.trans hd)).mpr hd
  have hsum : (J.card : ℝ) * (2 * q * omega) ^ 2 ≤
      ∑ i ∈ J, (inner ℝ (v i) (Z - w)) ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcoef
  have hB := hv.sum_inner_products_le (Z - w) (s := J)
  simp only [Real.norm_eq_abs, sq_abs] at hB
  have hcount := mul_le_mul_of_nonneg_right hcard (sq_nonneg (2 * q * omega))
  have hsq : (distanceScale q omega) ^ 2 ≤ ‖Z - w‖ ^ 2 := by
    rw [distanceScale_sq q omega hq]
    nlinarith only [hcount, hsum, hB]
  have hD : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  nlinarith only [hsq, hD, norm_nonneg (Z - w)]

def finiteProjection (v : I → E) (J : Finset I) (Z : E) : E :=
  ∑ i ∈ J, inner ℝ (v i) Z • v i

theorem finiteProjection_keeps_selected_coefficients
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E) (i : I) (hi : i ∈ J) :
    inner ℝ (v i) (finiteProjection v J Z) = inner ℝ (v i) Z := by
  exact hv.inner_right_sum (fun i => inner ℝ (v i) Z) hi

theorem finiteProjection_is_actual_orthogonal_projection [FiniteDimensional ℝ E]
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E) :
    finiteProjection v J Z =
      (Submodule.span ℝ (v '' (J : Set I))).starProjection Z := by
  let K := Submodule.span ℝ (v '' (J : Set I))
  have hmem : finiteProjection v J Z ∈ K := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem K _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  have hker : K ≤ LinearMap.ker (innerSL ℝ (Z - finiteProjection v J Z)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    change inner ℝ (Z - finiteProjection v J Z) (v i) = 0
    rw [real_inner_comm, inner_sub_right, finiteProjection_keeps_selected_coefficients v hv J Z i hi]
    ring
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro Y hY
  have hh := hker hY
  change inner ℝ (Z - finiteProjection v J Z) Y = 0 at hh
  exact hh

theorem finiteProjection_large_on_bulk
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z : E)
    (q omega : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ omega)
    (hcard : q / 4 ≤ (J.card : ℝ))
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z) :
    distanceScale q omega ≤ ‖finiteProjection v J Z‖ := by
  have hh := distance_from_unrevealed_coefficients v hv J (finiteProjection v J Z) 0 q omega hq hw hcard
    (fun i hi => by rw [finiteProjection_keeps_selected_coefficients v hv J Z i hi]; exact hbulk i hi)
    (fun _ _ => by simpa using mul_nonneg hq hw)
  simpa only [sub_zero] using hh

universe u

theorem actual_private_packet_unrevealed_separation
    {A B W : Type u}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 1 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : FangqingAmplifier.PhysicalSpace A B W,
      (∀ Y, OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      ∀ J : Finset (Fin (n + 3)),
        (∀ j ∈ J, (j.val : ℝ) ≤ q) → q / 4 ≤ (J.card : ℝ) →
        distanceScale q omega ≤ ‖finiteProjection
          (OriginalPacketOrientationNormalization.physicalFrame C h n tail) J Z‖ ∧
        (∀ w : FangqingAmplifier.PhysicalSpace A B W,
          (∀ j ∈ J, |inner ℝ (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) w| ≤ q * omega) →
          distanceScale q omega ≤ ‖Z - w‖) := by
  obtain ⟨Z, hm, _, _, _, hb⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
  have hv := OriginalPhysicalPacketMinimizer.physicalFrame_orthonormal C h hh n tail ht
  have hq0 : 0 ≤ q := by linarith
  have hw0 : 0 ≤ omega := (hd.trans_le hdw).le
  refine ⟨Z, hm, ?_⟩
  intro J hJ hcard
  have hbulk : ∀ j ∈ J, 3 * q * omega ≤ inner ℝ
      (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) Z :=
    fun j hj => hb j (hJ j hj)
  exact ⟨finiteProjection_large_on_bulk _ hv J Z q omega hq0 hw0 hcard hbulk,
    fun w hs => distance_from_unrevealed_coefficients _ hv J Z w q omega hq0 hw0 hcard hbulk hs⟩

end
end OriginalUnrevealedBulkSeparation
end

section
-- Source component: PacketBulkIndexing.lean

/- Original ceil length and q^(3/2) scale, plus the actual unrevealed
   first-q tail subset. This converts a disclosed-count bound into a
   genuine no-chamber-hit statement for the actual packet minimizer. -/

open scoped BigOperators

namespace OriginalPacketBulkIndexing

open OriginalPacketDistanceGapBounds OriginalUnrevealedBulkSeparation

noncomputable section

def packetLength (Cm : ℝ) (q : ℕ) : ℕ := Nat.ceil (Cm * q)
def packetIndex (Cm : ℝ) (q : ℕ) : ℕ := packetLength Cm q - 3

theorem original_ceil_path_conditions (Cm : ℝ) (hCm : 4 ≤ Cm) (q : ℕ) (hq : 1 ≤ q) :
    3 ≤ packetLength Cm q ∧
    packetLength Cm q = packetIndex Cm q + 3 ∧
    ((packetIndex Cm q + 2 : ℕ) : ℝ) ≤ Cm * q ∧
    q ≤ packetIndex Cm q + 2 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hm := Nat.le_ceil (Cm * (q : ℝ))
  change Cm * (q : ℝ) ≤ (packetLength Cm q : ℝ) at hm
  have hmul := mul_le_mul_of_nonneg_right hCm (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  have hm3 : 3 ≤ packetLength Cm q := by
    have hh : (3 : ℝ) ≤ packetLength Cm q := by linarith only [hm, hmul, hqR]
    exact_mod_cast hh
  have hindex : packetLength Cm q = packetIndex Cm q + 3 := by unfold packetIndex; omega
  have hqfit : q + 1 ≤ packetLength Cm q := by
    have hh : (q : ℝ) + 1 ≤ packetLength Cm q := by linarith only [hm, hmul, hqR]
    exact_mod_cast hh
  have hceil := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ Cm * q)
  change (packetLength Cm q : ℝ) < Cm * q + 1 at hceil
  have hindexR : (packetLength Cm q : ℝ) = (packetIndex Cm q : ℝ) + 3 := by exact_mod_cast hindex
  refine ⟨hm3, hindex, ?_, by omega⟩
  push_cast
  linarith only [hindexR, hceil]

theorem distanceScale_is_original_power (q omega : ℝ) (hq : 0 < q) :
    distanceScale q omega = q ^ ((3 : ℝ) / 2) * omega := by
  unfold distanceScale
  rw [Real.sqrt_eq_rpow]
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq, Real.rpow_one]

def unrevealedFirstTail (n q k : ℕ) (hfit : q ≤ n + 2) : Finset (Fin (n + 3)) :=
  (Finset.univ.filter (fun i : Fin q => k ≤ i.val)).image (fun i => (i.castLE hfit).succ)

theorem unrevealedFirstTail_card (n q k : ℕ) (hfit : q ≤ n + 2) (hk : k ≤ q) :
    (unrevealedFirstTail n q k hfit).card = q - k := by
  have hinj : Function.Injective (fun i : Fin q => (i.castLE hfit).succ) := by
    intro i j hij
    apply Fin.ext
    have hh := congrArg (fun x : Fin (n + 3) => x.val) hij
    simpa only [Fin.val_succ, Fin.val_castLE, Nat.add_right_cancel_iff] using hh
  unfold unrevealedFirstTail
  rw [Finset.card_image_of_injective _ hinj]
  have hset : Finset.univ.filter (fun i : Fin q => k ≤ i.val) =
      Finset.univ \ Finset.univ.filter (fun i : Fin q => i.val < k) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    omega
  rw [hset, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, Fintype.card_fin, Fin.card_filter_val_lt,
    Nat.min_eq_right hk]

theorem actual_unrevealed_index_properties
    (n q k : ℕ) (hfit : q ≤ n + 2) (hk : k ≤ q / 2) :
    (∀ j ∈ unrevealedFirstTail n q k hfit, (j.val : ℝ) ≤ q ∧ k ≤ j.val) ∧
      (q : ℝ) / 4 ≤ ((unrevealedFirstTail n q k hfit).card : ℝ) := by
  constructor
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hik := (Finset.mem_filter.mp hi).2
    constructor
    · exact_mod_cast (show (i.castLE hfit).succ.val ≤ q by simp only [Fin.val_succ, Fin.val_castLE]; omega)
    · simp only [Fin.val_succ, Fin.val_castLE]
      omega
  · rw [unrevealedFirstTail_card n q k hfit (by omega)]
    have hh : q ≤ 4 * (q - k) := by omega
    have hr : (q : ℝ) ≤ 4 * ((q - k : ℕ) : ℝ) := by exact_mod_cast hh
    linarith only [hr]

def originalBulkTail (n q : ℕ) (hfit : q ≤ n + 2) : Finset (Fin (n + 3)) :=
  unrevealedFirstTail n (q / 2 - 1) 0 (by omega)

theorem original_bulk_tail_indices
    (n q : ℕ) (hfit : q ≤ n + 2) :
    (originalBulkTail n q hfit : Set (Fin (n + 3))) =
      {j | 1 ≤ j.val ∧ j.val < q / 2} := by
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    simp only [Set.mem_setOf_eq, Fin.val_succ, Fin.val_castLE]
    have hiq := i.isLt
    omega
  · intro hj
    have h1 : 1 ≤ j.val := hj.1
    have hlt : j.val < q / 2 := hj.2
    let i : Fin (q / 2 - 1) := ⟨j.val - 1, by omega⟩
    apply Finset.mem_image.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩, ?_⟩
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_castLE, i]
    omega

theorem original_bulk_tail_large_enough
    (n q : ℕ) (hfit : q ≤ n + 2) (hq : 8 ≤ q) :
    (∀ j ∈ originalBulkTail n q hfit, (j.val : ℝ) ≤ q) ∧
      (q : ℝ) / 4 ≤ ((originalBulkTail n q hfit).card : ℝ) := by
  constructor
  · intro j hj
    have hs : j ∈ (originalBulkTail n q hfit : Set (Fin (n + 3))) := hj
    rw [original_bulk_tail_indices n q hfit] at hs
    exact_mod_cast (show j.val ≤ q by have := hs.2; omega)
  · unfold originalBulkTail
    rw [unrevealedFirstTail_card n (q / 2 - 1) 0 (by omega) (by omega), Nat.sub_zero]
    have hn : q ≤ 4 * (q / 2 - 1) := by omega
    have hr : (q : ℝ) ≤ 4 * ((q / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast hn
    linarith only [hr]

universe u

theorem actual_packet_cannot_be_hit_with_few_disclosures
    {A B W : Type u}
    [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (q : ℕ) (hq : 1 ≤ q) (hfit : q ≤ n + 2)
    (delta omega Cm Cw scale lam : ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * (q : ℝ) ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    ∃ Z : FangqingAmplifier.PhysicalSpace A B W,
      (∀ Y, OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        OriginalPhysicalPacketMinimizer.rawPacket C h n tail (FlatCubic.edge P delta omega)
          q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (distanceScale q omega ≤ ‖(Submodule.span ℝ
        (OriginalPacketOrientationNormalization.physicalFrame C h n tail ''
          (unrevealedFirstTail n q 0 hfit : Set (Fin (n + 3))))).starProjection Z‖) ∧
      ∀ k : ℕ, k ≤ q / 2 → ∀ w : FangqingAmplifier.PhysicalSpace A B W,
        (∀ j : Fin (n + 3), k ≤ j.val →
          |inner ℝ (OriginalPacketOrientationNormalization.physicalFrame C h n tail j) w| ≤ (q : ℝ) * omega) →
        distanceScale q omega ≤ ‖Z - w‖ := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  obtain ⟨Z, hm, hsep⟩ := actual_private_packet_unrevealed_separation P C h hh n tail ht delta omega
    q Cm Cw scale lam hd hdw hqR hCm hCw hscale hlam homega hn
  have hv := OriginalPhysicalPacketMinimizer.physicalFrame_orthonormal C h hh n tail ht
  have hidx0 := actual_unrevealed_index_properties n q 0 hfit (by omega)
  have hp := (hsep (unrevealedFirstTail n q 0 hfit) (fun j hj => (hidx0.1 j hj).1) hidx0.2).1
  rw [finiteProjection_is_actual_orthogonal_projection _ hv] at hp
  refine ⟨Z, hm, hp, ?_⟩
  intro k hk w hw
  have hidx := actual_unrevealed_index_properties n q k hfit hk
  exact (hsep (unrevealedFirstTail n q k hfit) (fun j hj => (hidx.1 j hj).1) hidx.2).2 w
    (fun j hj => hw j (hidx.1 j hj).2)

end
end OriginalPacketBulkIndexing
end

section
-- Source component: CanonicalPacketTailSupport.lean

set_option maxHeartbeats 1500000
open scoped BigOperators

namespace OriginalCanonicalPacketTailSupport
open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
open OriginalScalarPacketMinimizer OriginalPhysicalPacketMinimizer OriginalPhysicalPacketExistence
open OriginalPacketDistanceGapBounds

noncomputable section

/-- This definition has no orientation, handle, frame, scale, or ambient-space input. -/
def canonicalScalarPair (P : FlatCubic.Profile) (delta omega : ℝ) (n : ℕ) (q lam : ℝ) :
    ℝ × (Fin (n + 3) → ℝ) :=
  Classical.epsilon (fun p => ∀ (a : ℝ) (w : Fin (n + 3) → ℝ),
    scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q) p.1 p.2 ≤
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q) a w)

def positiveIndices {n : ℕ} (z : Fin (n + 3) → ℝ) : Finset (Fin (n + 3)) :=
  Finset.univ.filter (fun i => 0 < z i)

def lastPositiveIndex {n : ℕ} (z : Fin (n + 3) → ℝ) : Fin (n + 3) :=
  if h : (positiveIndices z).Nonempty then (positiveIndices z).max' h else 0

theorem last_positive_support {n : ℕ} (hn : 1 ≤ n) (z : Fin (n + 3) → ℝ)
    (hz : ∀ i, 0 ≤ z i) (hmono : Antitone z) (hthree : 0 < z ⟨3, by omega⟩) :
    3 ≤ (lastPositiveIndex z).val ∧ 0 < z (lastPositiveIndex z) ∧
      (∀ i, (lastPositiveIndex z).val < i.val → z i = 0) ∧
      (∀ i, i.val ≤ (lastPositiveIndex z).val → 0 < z i) := by
  let i3 : Fin (n + 3) := ⟨3, by omega⟩
  have hmem3 : i3 ∈ positiveIndices z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hthree⟩
  have hne : (positiveIndices z).Nonempty := ⟨i3, hmem3⟩
  have hlast : lastPositiveIndex z = (positiveIndices z).max' hne := by simp only [lastPositiveIndex, dif_pos hne]
  have hjmem : lastPositiveIndex z ∈ positiveIndices z := by rw [hlast]; exact Finset.max'_mem _ _
  have hjpos : 0 < z (lastPositiveIndex z) := (Finset.mem_filter.mp hjmem).2
  have h3le : i3 ≤ lastPositiveIndex z := by rw [hlast]; exact Finset.le_max' _ _ hmem3
  refine ⟨h3le, hjpos, ?_, ?_⟩
  · intro i hi
    apply le_antisymm
    · apply le_of_not_gt
      intro hipos
      have hm : i ∈ positiveIndices z := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hipos⟩
      have hl : i ≤ lastPositiveIndex z := by rw [hlast]; exact Finset.le_max' _ _ hm
      exact (not_le_of_gt hi) hl
    · exact hz i
  · intro i hi
    exact hjpos.trans_le (hmono hi)

section ActualPhysical
universe u
variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem canonical_pair_minimizes_from_actual_raw_minimizer
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 ≤ q)
    (hscale : 0 < scale) (hlam : 0 < lam) (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
      (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) :
    ∀ (a : ℝ) (w : Fin (n + 3) → ℝ),
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q)
        (canonicalScalarPair P delta omega n q lam).1 (canonicalScalarPair P delta omega n q lam).2 ≤
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q) a w := by
  have hc := actual_raw_packet_contDiff_strongConvex P C h hh n tail ht delta omega q (scale * lam) scale
    (scale * (2 * omega ^ 2 / Real.sqrt q)) hd hdw hq (mul_pos hscale hlam).le hscale.le
  obtain ⟨alpha, z, hZ, hs⟩ := actual_physical_minimizer_reduces_to_scalar_minimizer C h hh n tail ht
    (FlatCubic.edge P delta omega) q scale lam (2 * omega ^ 2 / Real.sqrt q) hscale
    (hc.2.strictConvexOn (mul_pos hscale hlam)) Z hmin
  unfold canonicalScalarPair
  have hex : ∃ p : ℝ × (Fin (n + 3) → ℝ), ∀ (a : ℝ) (w : Fin (n + 3) → ℝ),
      scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q) p.1 p.2 ≤
        scalarObjective (FlatCubic.edge P delta omega) (n + 2) q lam (2 * omega ^ 2 / Real.sqrt q) a w := ⟨(alpha, z), hs⟩
  exact Classical.epsilon_spec hex

theorem actual_raw_minimizer_uses_public_coefficients
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 ≤ q)
    (hscale : 0 < scale) (hlam : 0 < lam) (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
      (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) :
    Z = coordinatePoint C h n tail (canonicalScalarPair P delta omega n q lam).1 (canonicalScalarPair P delta omega n q lam).2 := by
  let F := rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q))
  let p := canonicalScalarPair P delta omega n q lam
  let Zc := coordinatePoint C h n tail p.1 p.2
  have hc := actual_raw_packet_contDiff_strongConvex P C h hh n tail ht delta omega q (scale * lam) scale
    (scale * (2 * omega ^ 2 / Real.sqrt q)) hd hdw hq (mul_pos hscale hlam).le hscale.le
  have hstrict := hc.2.strictConvexOn (mul_pos hscale hlam)
  obtain ⟨alpha, z, hZ, hs⟩ := actual_physical_minimizer_reduces_to_scalar_minimizer C h hh n tail ht
    (FlatCubic.edge P delta omega) q scale lam (2 * omega ^ 2 / Real.sqrt q) hscale hstrict Z hmin
  have hpublic := canonical_pair_minimizes_from_actual_raw_minimizer P C h hh n tail ht delta omega q scale lam hd hdw hq hscale hlam Z hmin
  have hcomp : F Zc ≤ F Z := by
    change rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Zc ≤ rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z
    rw [hZ]
    rw [actual_physical_scalar_value_identity C h hh n tail ht, actual_physical_scalar_value_identity C h hh n tail ht]
    exact mul_le_mul_of_nonneg_left (hpublic alpha z) hscale.le
  have hm : ∀ Y, F Zc ≤ F Y := fun Y => hcomp.trans (hmin Y)
  exact (hstrict.eq_of_isMinOn (fun Y _ => hm Y) (fun Y _ => hmin Y) (Set.mem_univ _) (Set.mem_univ _)).symm

theorem actual_public_coefficients_and_last_support
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (hn0 : 1 ≤ n) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 4 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q)
    (Z : PhysicalSpace A B W)
    (hmin : ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
      (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) :
    let p := canonicalScalarPair P delta omega n q lam
    let j := lastPositiveIndex p.2
    Z = coordinatePoint C h n tail p.1 p.2 ∧
      (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ 2 * Cw * q * omega) ∧ Antitone p.2 ∧
      3 ≤ j.val ∧ 0 < p.2 j ∧ (∀ i, j.val < i.val → p.2 i = 0) ∧
      (∀ i, i.val ≤ j.val → 0 < p.2 i) := by
  dsimp only
  let p := canonicalScalarPair P delta omega n q lam
  have hq1 : 1 ≤ q := by linarith only [hq]
  have hpublic := canonical_pair_minimizes_from_actual_raw_minimizer P C h hh n tail ht delta omega q scale lam hd hdw
    (by linarith only [hq]) hscale hlam Z hmin
  have hcoord := actual_raw_minimizer_uses_public_coefficients P C h hh n tail ht delta omega q scale lam hd hdw
    (by linarith only [hq]) hscale hlam Z hmin
  have hsize := actual_scalar_minimizer_size_bounds P delta omega q Cm Cw lam p.1 hd hdw hq1 hCm hCw hlam homega (n + 2) hn p.2 hpublic
  have hbulk := actual_scalar_minimizer_bulk P delta omega q Cm Cw lam p.1 hd hdw hq1 hCm hCw hlam homega (n + 2) hn p.2 hpublic
  have hmono : Antitone p.2 := Fin.antitone_iff_succ_le.mpr (fun i => by linarith only [(hbulk.2.2.1 i).1])
  have hw : 0 < omega := hd.trans_le hdw
  have hthree : 0 < p.2 ⟨3, by omega⟩ := by
    have hh := hbulk.2.2.2.2 ⟨3, by omega⟩ (by norm_num; linarith only [hq])
    have hprod : 0 < 3 * q * omega := by positivity
    exact hprod.trans_le hh
  have hlast := last_positive_support hn0 p.2 (fun i => (hsize.1 i).1) hmono hthree
  exact ⟨hcoord, hsize.1, hmono, hlast⟩

/-- Existence is derived from the actual packet's coercive strong convexity; the
    public pair and last support index are not hypotheses. -/
theorem actual_raw_minimizer_exists_with_public_last_support
    (P : FlatCubic.Profile) (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (hn0 : 1 ≤ n) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cm Cw scale lam : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 4 ≤ q)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hscale : 0 < scale) (hlam : 0 < lam)
    (homega : omega = Cw * lam * q ^ 2) (hn : ((n + 2 : ℕ) : ℝ) ≤ Cm * q) :
    let p := canonicalScalarPair P delta omega n q lam
    let j := lastPositiveIndex p.2
    ∃ Z : PhysicalSpace A B W,
      (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
        rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      Z = coordinatePoint C h n tail p.1 p.2 ∧
      (∀ i, 0 ≤ p.2 i ∧ p.2 i ≤ 2 * Cw * q * omega) ∧ Antitone p.2 ∧
      3 ≤ j.val ∧ 0 < p.2 j ∧ (∀ i, j.val < i.val → p.2 i = 0) ∧
      (∀ i, i.val ≤ j.val → 0 < p.2 i) := by
  obtain ⟨Z, alpha, z, hm, _⟩ := actual_physical_minimizer_exists_with_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw (by linarith only [hq]) hCm hCw hscale hlam homega hn
  exact ⟨Z, hm, actual_public_coefficients_and_last_support P C h hh n hn0 tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn Z hm⟩

end ActualPhysical
end
end OriginalCanonicalPacketTailSupport
end

section
-- Source component: CanonicalPacketTailDecomposition.lean

set_option maxHeartbeats 1500000
open scoped BigOperators
namespace OriginalCanonicalPacketTailSupport
open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
open OriginalPhysicalPacketMinimizer
noncomputable section
variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

def knownPrefixPoint (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (cutoff : ℕ) : PhysicalSpace A B W :=
  mkPhysical (alpha • h) 0 0 + ∑ i, if i.val < cutoff then z i • physicalFrame C h n tail i else 0

def previousIndex {n : ℕ} (j : Fin (n + 3)) (r : ℕ) : Fin (n + 3) :=
  ⟨j.val - r, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

theorem coordinatePoint_frame_expansion
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) :
    coordinatePoint C h n tail alpha z =
      mkPhysical (alpha • h) 0 0 + ∑ i, z i • physicalFrame C h n tail i := by
  rw [Fin.sum_univ_succ]
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;>
      simp [coordinatePoint, physicalFrame, mkPhysical, WithLp.ofLp_sum, Prod.fst_sum]
  · simp [coordinatePoint, physicalFrame, mkPhysical, WithLp.ofLp_sum, Prod.snd_sum]

theorem coordinatePoint_last_two_decomposition
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 1 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    coordinatePoint C h n tail alpha z =
      knownPrefixPoint C h n tail alpha z (j.val - 1) +
        z (previousIndex j 1) • physicalFrame C h n tail (previousIndex j 1) +
        z j • physicalFrame C h n tail j := by
  have hf (i : Fin (n + 3)) : z i • physicalFrame C h n tail i =
      (if i.val < j.val - 1 then z i • physicalFrame C h n tail i else 0) +
      (if i = previousIndex j 1 then z i • physicalFrame C h n tail i else 0) +
      (if i = j then z i • physicalFrame C h n tail i else 0) := by
    by_cases hp : i.val < j.val - 1
    · have hne1 : i ≠ previousIndex j 1 := by intro he; have := congrArg Fin.val he; dsimp [previousIndex] at this; omega
      have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
      simp only [if_pos hp, if_neg hne1, if_neg hne, add_zero]
    · by_cases he1 : i = previousIndex j 1
      · have hne : i ≠ j := by intro he; have hv := congrArg Fin.val he1; have hv2 := congrArg Fin.val he; dsimp [previousIndex] at hv; omega
        simp only [if_neg hp, if_pos he1, if_neg hne, zero_add, add_zero]
      · by_cases he : i = j
        · simp only [if_neg hp, if_neg he1, if_pos he, zero_add, add_zero]
        · have hgt : j.val < i.val := by
            have hneq1 : i.val ≠ j.val - 1 := by intro he; apply he1; apply Fin.ext; exact he
            have hneq : i.val ≠ j.val := by intro heq; exact he (Fin.ext heq)
            omega
          simp only [if_neg hp, if_neg he1, if_neg he, hzero i hgt, zero_smul, zero_add]
  rw [coordinatePoint_frame_expansion]
  conv_lhs => arg 2; arg 2; ext i; rw [hf i]
  simp only [Finset.sum_add_distrib]
  simp [knownPrefixPoint, add_assoc]

theorem coordinatePoint_last_three_decomposition
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 2 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    coordinatePoint C h n tail alpha z =
      knownPrefixPoint C h n tail alpha z (j.val - 2) +
        z (previousIndex j 2) • physicalFrame C h n tail (previousIndex j 2) +
        z (previousIndex j 1) • physicalFrame C h n tail (previousIndex j 1) +
        z j • physicalFrame C h n tail j := by
  have hf (i : Fin (n + 3)) : z i • physicalFrame C h n tail i =
      (if i.val < j.val - 2 then z i • physicalFrame C h n tail i else 0) +
      (if i = previousIndex j 2 then z i • physicalFrame C h n tail i else 0) +
      (if i = previousIndex j 1 then z i • physicalFrame C h n tail i else 0) +
      (if i = j then z i • physicalFrame C h n tail i else 0) := by
    by_cases hp : i.val < j.val - 2
    · have hne2 : i ≠ previousIndex j 2 := by intro he; have := congrArg Fin.val he; dsimp [previousIndex] at this; omega
      have hne1 : i ≠ previousIndex j 1 := by intro he; have := congrArg Fin.val he; dsimp [previousIndex] at this; omega
      have hne : i ≠ j := by intro he; have := congrArg Fin.val he; omega
      simp only [if_pos hp, if_neg hne2, if_neg hne1, if_neg hne, add_zero]
    · by_cases he2 : i = previousIndex j 2
      · have hne1 : i ≠ previousIndex j 1 := by intro he; have h1 := congrArg Fin.val he2; have h2 := congrArg Fin.val he; dsimp [previousIndex] at h1 h2; omega
        have hne : i ≠ j := by intro he; have h1 := congrArg Fin.val he2; have h2 := congrArg Fin.val he; dsimp [previousIndex] at h1; omega
        simp only [if_neg hp, if_pos he2, if_neg hne1, if_neg hne, zero_add, add_zero]
      · by_cases he1 : i = previousIndex j 1
        · have hne : i ≠ j := by intro he; have h1 := congrArg Fin.val he1; have h2 := congrArg Fin.val he; dsimp [previousIndex] at h1; omega
          simp only [if_neg hp, if_neg he2, if_pos he1, if_neg hne, zero_add, add_zero]
        · by_cases he : i = j
          · simp only [if_neg hp, if_neg he2, if_neg he1, if_pos he, zero_add, add_zero]
          · have hgt : j.val < i.val := by
              have hneq2 : i.val ≠ j.val - 2 := by intro he; apply he2; apply Fin.ext; exact he
              have hneq1 : i.val ≠ j.val - 1 := by intro he; apply he1; apply Fin.ext; exact he
              have hneq : i.val ≠ j.val := by intro heq; exact he (Fin.ext heq)
              omega
            simp only [if_neg hp, if_neg he2, if_neg he1, if_neg he, hzero i hgt, zero_smul, zero_add]
  rw [coordinatePoint_frame_expansion]
  conv_lhs => arg 2; arg 2; ext i; rw [hf i]
  simp only [Finset.sum_add_distrib]
  simp [knownPrefixPoint, add_assoc]

theorem knownPrefixPoint_depends_only_on_prefix
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail tail' : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (cutoff : ℕ)
    (hprefix : ∀ i : Fin (n + 3), i.val < cutoff →
      physicalFrame C h n tail i = physicalFrame C h n tail' i) :
    knownPrefixPoint C h n tail alpha z cutoff = knownPrefixPoint C h n tail' alpha z cutoff := by
  unfold knownPrefixPoint
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < cutoff
  · simp only [if_pos hi, hprefix i hi]
  · simp only [if_neg hi]

theorem physicalFrame_positive_index_in_W
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (i : Fin (n + 3)) (hi : 1 ≤ i.val) :
    (physicalFrame C h n tail i).fst = 0 := by
  revert hi
  refine Fin.cases ?_ (fun k => ?_) i
  · intro hi; norm_num at hi
  · intro _; rfl

theorem last_three_positive_distinct_in_tail {n : ℕ}
    (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 3 ≤ j.val)
    (hpos : ∀ i, i.val ≤ j.val → 0 < z i) :
    0 < z (previousIndex j 2) ∧ 0 < z (previousIndex j 1) ∧ 0 < z j ∧
      1 ≤ (previousIndex j 2).val ∧ 1 ≤ (previousIndex j 1).val ∧ 1 ≤ j.val ∧
      previousIndex j 2 ≠ previousIndex j 1 ∧ previousIndex j 2 ≠ j ∧ previousIndex j 1 ≠ j := by
  refine ⟨hpos _ (Nat.sub_le _ _), hpos _ (Nat.sub_le _ _), hpos _ le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [previousIndex]; omega
  · dsimp only [previousIndex]; omega
  · omega
  · intro he; have := congrArg Fin.val he; dsimp only [previousIndex] at this; omega
  · intro he; have := congrArg Fin.val he; dsimp only [previousIndex] at this; omega
  · intro he; have := congrArg Fin.val he; dsimp only [previousIndex] at this; omega

end
end OriginalCanonicalPacketTailSupport
end

section
-- Source component: CanonicalLateGateGeometry.lean

namespace FangqingCanonicalLateGateGeometry

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalCanonicalPacketTailSupport

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem actual_handle_orthogonal_to_whole_path
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W) (i : Fin (n + 3)) :
    inner ℝ (mkPhysical h (0 : B) (0 : W)) (physicalFrame C h n tail i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · change (inner ℝ h (0 : A) + inner ℝ (0 : B) (C h)) + inner ℝ (0 : W) (0 : W) = 0
    simp
  · change (inner ℝ h (0 : A) + inner ℝ (0 : B) (0 : B)) + inner ℝ (0 : W) (tail j) = 0
    simp

noncomputable def handleFrameTriple
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W) (i j : Fin (n + 3)) :
    Fin 3 → PhysicalSpace A B W :=
  ![mkPhysical h 0 0, physicalFrame C h n tail i, physicalFrame C h n tail j]

theorem actual_handle_two_columns_orthonormal
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (i j : Fin (n + 3)) (hij : i ≠ j) :
    Orthonormal ℝ (handleFrameTriple C h n tail i j) := by
  have hV := physicalFrame_orthonormal C h hh n tail ht
  have hself : inner ℝ (mkPhysical h (0 : B) (0 : W)) (mkPhysical h (0 : B) (0 : W)) = 1 := by
    change (inner ℝ h h + inner ℝ (0 : B) (0 : B)) + inner ℝ (0 : W) (0 : W) = 1
    simp [real_inner_self_eq_norm_sq, hh]
  have hnorm : ‖mkPhysical h (0 : B) (0 : W)‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hself
    nlinarith only [hself, norm_nonneg (mkPhysical h (0 : B) (0 : W))]
  have hl (k : Fin (n + 3)) := actual_handle_orthogonal_to_whole_path C h n tail k
  have hr (k : Fin (n + 3)) :
      inner ℝ (physicalFrame C h n tail k) (mkPhysical h (0 : B) (0 : W)) = 0 := by
    rw [real_inner_comm]
    exact hl k
  rw [orthonormal_iff_ite]
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [handleFrameTriple, hnorm, hV.norm_eq_one, hself, hl, hr, orthonormal_iff_ite.mp hV, hij, Ne.symm hij]

theorem actual_scaled_center_last_two_decomposition
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha tau : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 1 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    -(tau • coordinatePoint C h n tail alpha z) =
      -(tau • knownPrefixPoint C h n tail alpha z (j.val - 1)) +
        (-tau * z (previousIndex j 1)) • physicalFrame C h n tail (previousIndex j 1) +
        (-tau * z j) • physicalFrame C h n tail j := by
  rw [coordinatePoint_last_two_decomposition C h n tail alpha z j hj hzero]
  module

theorem actual_scaled_center_last_three_decomposition
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha tau : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 2 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    -(tau • coordinatePoint C h n tail alpha z) =
      -(tau • knownPrefixPoint C h n tail alpha z (j.val - 2)) +
        (-tau * z (previousIndex j 2)) • physicalFrame C h n tail (previousIndex j 2) +
        (-tau * z (previousIndex j 1)) • physicalFrame C h n tail (previousIndex j 1) +
        (-tau * z j) • physicalFrame C h n tail j := by
  rw [coordinatePoint_last_three_decomposition C h n tail alpha z j hj hzero]
  module

theorem actual_scaled_last_two_residual_norm
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (alpha tau : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 1 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    ‖-(tau • coordinatePoint C h n tail alpha z) -
      (-(tau • knownPrefixPoint C h n tail alpha z (j.val - 1)))‖ ^ 2 =
      tau ^ 2 * (z (previousIndex j 1) ^ 2 + z j ^ 2) := by
  have hV := physicalFrame_orthonormal C h hh n tail ht
  have hne : previousIndex j 1 ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  have he : -(tau • coordinatePoint C h n tail alpha z) -
      (-(tau • knownPrefixPoint C h n tail alpha z (j.val - 1))) =
      (-tau * z (previousIndex j 1)) • physicalFrame C h n tail (previousIndex j 1) +
        (-tau * z j) • physicalFrame C h n tail j := by
    rw [actual_scaled_center_last_two_decomposition C h n tail alpha tau z j hj hzero]
    module
  rw [he, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hV, if_pos rfl, if_neg hne, if_neg (Ne.symm hne), mul_zero, mul_one,
    add_zero, zero_mul, zero_add]
  simp only [ite_true]
  ring

theorem actual_scaled_last_three_residual_norm
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (alpha tau : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 3)) (hj : 2 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0) :
    ‖-(tau • coordinatePoint C h n tail alpha z) -
      (-(tau • knownPrefixPoint C h n tail alpha z (j.val - 2)))‖ ^ 2 =
      tau ^ 2 * (z (previousIndex j 2) ^ 2 + z (previousIndex j 1) ^ 2 + z j ^ 2) := by
  have hV := physicalFrame_orthonormal C h hh n tail ht
  have h20 : previousIndex j 2 ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  have h10 : previousIndex j 1 ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  have h21 : previousIndex j 2 ≠ previousIndex j 1 := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  have he : -(tau • coordinatePoint C h n tail alpha z) -
      (-(tau • knownPrefixPoint C h n tail alpha z (j.val - 2))) =
      (-tau * z (previousIndex j 2)) • physicalFrame C h n tail (previousIndex j 2) +
        (-tau * z (previousIndex j 1)) • physicalFrame C h n tail (previousIndex j 1) +
        (-tau * z j) • physicalFrame C h n tail j := by
    rw [actual_scaled_center_last_three_decomposition C h n tail alpha tau z j hj hzero]
    module
  rw [he, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.mp hV, if_pos rfl, if_neg h20, if_neg (Ne.symm h20), if_neg h10,
    if_neg (Ne.symm h10), if_neg h21, if_neg (Ne.symm h21), mul_zero, mul_one,
    add_zero, zero_mul, zero_add]
  simp only [ite_true]
  ring

end FangqingCanonicalLateGateGeometry
end

section
-- Source component: RelayLinkJetBounds.lean

open scoped ContDiff

namespace FangqingRelayLinkJetBounds

open FangqingRelayProductBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev Pair (E : Type*) := WithLp 2 (E × E)

def link (gate delta : E → ℝ) (reward : ℝ) (p : Pair E) : ℝ := gate p.fst * (delta p.snd - reward)

theorem projection_x_norm_le : ‖WithLp.fstL 2 ℝ E E‖ ≤ 1 :=
  (WithLp.fstL 2 ℝ E E).opNorm_le_bound (by norm_num) (fun z => by simpa only [one_mul] using! WithLp.norm_fst_le E z)

theorem projection_y_norm_le : ‖WithLp.sndL 2 ℝ E E‖ ≤ 1 :=
  (WithLp.sndL 2 ℝ E E).opNorm_le_bound (by norm_num) (fun z => by simpa only [one_mul] using! WithLp.norm_snd_le E z)

theorem subtract_reward_jet (delta : E → ℝ) (hd : ContDiff ℝ 3 delta) (reward : ℝ)
    (j : ℕ) (hj1 : 1 ≤ j) (hj3 : j ≤ 3) (z : E) :
    iteratedFDeriv ℝ j (fun y => delta y - reward) z = iteratedFDeriv ℝ j delta z := by
  rw [fun_iteratedFDeriv_sub_apply (hd.of_le (by exact_mod_cast hj3)).contDiffAt contDiffAt_const,
    iteratedFDeriv_const_of_ne (by omega)]
  simp only [Pi.zero_apply, sub_zero]

theorem actual_link_jet_budgets (gate delta : E → ℝ) (hg : ContDiff ℝ 3 gate) (hd : ContDiff ℝ 3 delta)
    (reward G1 G2 G3 D0 D1 D2 D3 : ℝ) (hr : 0 ≤ reward)
    (hg0 : ∀ z, |gate z| ≤ 1)
    (hg1 : ∀ z, ‖iteratedFDeriv ℝ 1 gate z‖ ≤ G1)
    (hg2 : ∀ z, ‖iteratedFDeriv ℝ 2 gate z‖ ≤ G2)
    (hg3 : ∀ z, ‖iteratedFDeriv ℝ 3 gate z‖ ≤ G3)
    (hd0 : ∀ z, |delta z| ≤ D0)
    (hd1 : ∀ z, ‖iteratedFDeriv ℝ 1 delta z‖ ≤ D1)
    (hd2 : ∀ z, ‖iteratedFDeriv ℝ 2 delta z‖ ≤ D2)
    (hd3 : ∀ z, ‖iteratedFDeriv ℝ 3 delta z‖ ≤ D3) :
    ContDiff ℝ 3 (link gate delta reward) ∧
    (∀ p, ‖iteratedFDeriv ℝ 2 (link gate delta reward) p‖ ≤ D2 + 2 * G1 * D1 + G2 * (D0 + reward)) ∧
    (∀ p, ‖iteratedFDeriv ℝ 3 (link gate delta reward) p‖ ≤
      D3 + 3 * G1 * D2 + 3 * G2 * D1 + G3 * (D0 + reward)) := by
  let px : Pair E →L[ℝ] E := WithLp.fstL 2 ℝ E E
  let py : Pair E →L[ℝ] E := WithLp.sndL 2 ℝ E E
  let f : Pair E → ℝ := gate ∘ px
  let g : Pair E → ℝ := (fun y => delta y - reward) ∘ py
  have hf : ContDiff ℝ 3 f := hg.comp px.contDiff
  have hgc : ContDiff ℝ 3 g := (hd.sub contDiff_const).comp py.contDiff
  have hfi : ∀ j, 1 ≤ j → j ≤ 3 → ∀ p, ‖iteratedFDeriv ℝ j f p‖ ≤ ‖iteratedFDeriv ℝ j gate (px p)‖ := by
    intro j hj1 hj3 p
    exact norm_iterated_comp_contraction gate px 3 hg projection_x_norm_le p j (by exact_mod_cast hj3)
  have hgi : ∀ j, 1 ≤ j → j ≤ 3 → ∀ p, ‖iteratedFDeriv ℝ j g p‖ ≤ ‖iteratedFDeriv ℝ j delta (py p)‖ := by
    intro j hj1 hj3 p
    have hh := norm_iterated_comp_contraction (fun y => delta y - reward) py 3 (hd.sub contDiff_const)
      projection_y_norm_le p j (by exact_mod_cast hj3)
    rw [subtract_reward_jet delta hd reward j hj1 hj3] at hh
    exact hh
  have hf0 : ∀ p, ‖f p‖ ≤ 1 := fun p => hg0 (px p)
  have hg0b : ∀ p, ‖g p‖ ≤ D0 + reward := by
    intro p
    have hh := norm_sub_le (delta (py p)) reward
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr] at hh
    exact hh.trans (add_le_add (hd0 (py p)) (le_refl reward))
  refine ⟨hf.mul hgc, ?_, ?_⟩
  · intro p
    have hh := product_second_bound f g hf hgc p 1 G1 G2 (D0 + reward) D1 D2
      (hf0 p) ((hfi 1 (by norm_num) (by norm_num) p).trans (hg1 _))
      ((hfi 2 (by norm_num) (by norm_num) p).trans (hg2 _)) (hg0b p)
      ((hgi 1 (by norm_num) (by norm_num) p).trans (hd1 _))
      ((hgi 2 (by norm_num) (by norm_num) p).trans (hd2 _))
    simpa only [one_mul] using! hh
  · intro p
    have hh := product_third_bound f g hf hgc p 1 G1 G2 G3 (D0 + reward) D1 D2 D3
      (hf0 p) ((hfi 1 (by norm_num) (by norm_num) p).trans (hg1 _))
      ((hfi 2 (by norm_num) (by norm_num) p).trans (hg2 _))
      ((hfi 3 (by norm_num) (by norm_num) p).trans (hg3 _)) (hg0b p)
      ((hgi 1 (by norm_num) (by norm_num) p).trans (hd1 _))
      ((hgi 2 (by norm_num) (by norm_num) p).trans (hd2 _))
      ((hgi 3 (by norm_num) (by norm_num) p).trans (hd3 _))
    simpa only [one_mul] using! hh

end
end FangqingRelayLinkJetBounds
end

section
-- Source component: ActualRelayLink.lean

open scoped ContDiff

namespace FangqingActualRelayLink

open FangqingRadialGateBounds FangqingGateBudgetBridge FangqingPublicShellProfiles
  FangqingLocalizedSeedJets FangqingActualLocalizedSeedBounds FangqingRelayLinkJetBounds
  FangqingRelayStationarity FangqingRelayFenchelInterfaces

noncomputable section

universe u

theorem actual_normalized_gate_link (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∃ Kg : ℝ, 0 ≤ Kg ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (Rp A amp D Rg c reward : ℝ) (handle center : F) (H0 H1 : F → ℝ) (z0 z1 : F),
      0 < D → D ≤ Rp → D ≤ A → 0 ≤ amp → ‖handle‖ ≤ 1 → 0 < Rg → 0 ≤ reward →
      (∀ z, H1 z = H0 z - localizedSeed theta phi Rp A amp handle z) →
      (∀ z, H0 z0 ≤ H0 z) → (∀ z, H1 z1 ≤ H1 z) →
      let gate := scaledGate theta Rg center
      let dd := delta (reduced H0 c) (reduced H1 c) (H0 z0) (H1 z1)
      ContDiff ℝ 3 gate ∧ (∀ z, 0 ≤ gate z ∧ gate z ≤ 1) ∧
      ContDiff ℝ 3 dd ∧ (∀ z, |dd z| ≤ Kd * amp) ∧
      (∀ j, 1 ≤ j → j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j dd z‖ ≤ Kd * amp / D ^ j) ∧
      ContDiff ℝ 3 (FangqingRelayLinkJetBounds.link gate dd reward) ∧
      (∀ p, ‖iteratedFDeriv ℝ 2 (FangqingRelayLinkJetBounds.link gate dd reward) p‖ ≤
        Kd * amp / D ^ 2 + 2 * (Kg / Rg) * (Kd * amp / D) +
          (Kg / Rg ^ 2) * (Kd * amp + reward)) ∧
      (∀ p, ‖iteratedFDeriv ℝ 3 (FangqingRelayLinkJetBounds.link gate dd reward) p‖ ≤
        Kd * amp / D ^ 3 + 3 * (Kg / Rg) * (Kd * amp / D ^ 2) +
          3 * (Kg / Rg ^ 2) * (Kd * amp / D) + (Kg / Rg ^ 3) * (Kd * amp + reward)) := by
  have ht : ContDiff ℝ 3 theta := theta_smooth.of_le (by decide)
  obtain ⟨Kd, hKd, hd⟩ := universal_normalized_seed_bounds.{u} theta phi (7 / 4) B left right
    (by norm_num) ht hp (fun t ht => theta_one t (by linarith only [ht]))
    (fun t ht => theta_zero t (by nlinarith only [ht])) hl hr
  obtain ⟨Kg, hKg, hg⟩ := universal_three_gate_bounds.{u} theta (7 / 4) (by norm_num) ht
    (fun t ht => theta_one t (by linarith only [ht])) (fun t ht => theta_zero t (by nlinarith only [ht]))
  refine ⟨Kd, hKd, Kg, hKg, ?_⟩
  intro F inst inst' inst'' Rp A amp D Rg c reward handle center H0 H1 z0 z1 hD hRp hA hamp hh hRg hrw hrel hm0 hm1 gate dd
  obtain ⟨hdc, hd0, hdj⟩ := hd F Rp A amp D handle hD hRp hA hamp hh H0 H1 z0 z1 hrel hm0 hm1
  have heq : dd = normalizedDifference H0 H1 z0 z1 := by
    funext z
    exact delta_from_actual_minima H0 H1 c z0 z1 z
  have hdc' : ContDiff ℝ 3 dd := heq ▸ hdc
  have hd0' : ∀ z, |dd z| ≤ Kd * amp := by rw [heq]; exact hd0
  have hdj' : ∀ j, 1 ≤ j → j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j dd z‖ ≤ Kd * amp / D ^ j := by
    rw [heq]
    exact hdj
  have hgc : ContDiff ℝ 3 gate := scaledGate_contDiff theta Rg center hRg ht
  have hg0 : ∀ z, 0 ≤ gate z ∧ gate z ≤ 1 := fun z => theta_range _
  have hgj : ∀ j, 1 ≤ j → j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j gate z‖ ≤ Kg / Rg ^ j :=
    fun j hj hj3 z => hg F Rg hRg center z j hj hj3
  obtain ⟨hlink, hl2, hl3⟩ := actual_link_jet_budgets gate dd hgc hdc' reward
    (Kg / Rg) (Kg / Rg ^ 2) (Kg / Rg ^ 3) (Kd * amp) (Kd * amp / D) (Kd * amp / D ^ 2) (Kd * amp / D ^ 3)
    hrw (fun z => by rw [abs_of_nonneg (hg0 z).1]; exact (hg0 z).2)
    (fun z => by simpa only [pow_one] using hgj 1 (by norm_num) (by norm_num) z)
    (hgj 2 (by norm_num) (by norm_num)) (hgj 3 (by norm_num) (by norm_num)) hd0'
    (fun z => by simpa only [pow_one] using hdj' 1 (by norm_num) (by norm_num) z)
    (hdj' 2 (by norm_num) (by norm_num)) (hdj' 3 (by norm_num) (by norm_num))
  exact ⟨hgc, hg0, hdc', hd0', hdj', hlink, hl2, hl3⟩

end
end FangqingActualRelayLink
end

section
-- Source component: RelayQuadraticBounds.lean

open scoped ContDiff NNReal


namespace FangqingRelayQuadraticBounds

open FangqingRelayBlockGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def K (a sigma : ℝ) : Pair E →L[ℝ] Pair E :=
  pairMap
    ((sigma * a) • (WithLp.sndL 2 ℝ E E - a • WithLp.fstL 2 ℝ E E))
    (-sigma • (WithLp.sndL 2 ℝ E E - a • WithLp.fstL 2 ℝ E E))

def quadratic (a sigma : ℝ) (z : Pair E) : ℝ :=
  -sigma / 2 * ‖z.snd - a • z.fst‖ ^ 2

theorem K_symmetric (a sigma : ℝ) : (K (E := E) a sigma).toLinearMap.IsSymmetric := by
  intro z w
  change inner ℝ (K a sigma z) w = inner ℝ z (K a sigma w)
  change inner ℝ ((sigma * a) • (z.snd - a • z.fst)) w.fst +
      inner ℝ (-sigma • (z.snd - a • z.fst)) w.snd =
    inner ℝ z.fst ((sigma * a) • (w.snd - a • w.fst)) +
      inner ℝ z.snd (-sigma • (w.snd - a • w.fst))
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right]
  ring

theorem inner_K_self (a sigma : ℝ) (z : Pair E) :
    inner ℝ (K a sigma z) z = -sigma * ‖z.snd - a • z.fst‖ ^ 2 := by
  change inner ℝ ((sigma * a) • (z.snd - a • z.fst)) z.fst +
    inner ℝ (-sigma • (z.snd - a • z.fst)) z.snd = _
  simp only [real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq]
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  rw [real_inner_comm z.fst z.snd]
  ring

theorem hasFDerivAt_quadratic (a sigma : ℝ) (z : Pair E) :
    HasFDerivAt (quadratic (E := E) a sigma) (innerSL ℝ (K a sigma z)) z := by
  have hfun : quadratic (E := E) a sigma =
      (fun z => (1 / 2 : ℝ) * (K a sigma).reApplyInnerSelf z) := by
    funext z
    change quadratic a sigma z = (1 / 2 : ℝ) * inner ℝ (K a sigma z) z
    rw [inner_K_self]
    unfold quadratic
    ring
  rw [hfun]
  have hh := ((K_symmetric (E := E) a sigma).hasStrictFDerivAt_reApplyInnerSelf z).hasFDerivAt.const_mul
    (1 / 2 : ℝ)
  convert! hh using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, two_smul, smul_eq_mul]
  ring

theorem actual_hessian_constant (a sigma : ℝ) :
    fderiv ℝ (fderiv ℝ (quadratic (E := E) a sigma)) =
      (fun _ => (innerSL ℝ).comp (K (E := E) a sigma)) := by
  have hfun : fderiv ℝ (quadratic (E := E) a sigma) =
      ((innerSL ℝ).comp (K (E := E) a sigma) : Pair E →L[ℝ] (Pair E →L[ℝ] ℝ)) := by
    funext z
    exact (hasFDerivAt_quadratic a sigma z).fderiv
  rw [hfun]
  funext z
  exact ContinuousLinearMap.fderiv _

theorem relay_residual_square (a : ℝ) (z : Pair E) :
    ‖z.snd - a • z.fst‖ ^ 2 + ‖z.fst + a • z.snd‖ ^ 2 =
      (1 + a ^ 2) * ‖z‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2, norm_sub_sq_real, norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
  rw [real_inner_comm z.fst z.snd]
  ring

theorem K_norm_sq (a sigma : ℝ) (z : Pair E) :
    ‖K a sigma z‖ ^ 2 = sigma ^ 2 * (1 + a ^ 2) * ‖z.snd - a • z.fst‖ ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(sigma * a) • (z.snd - a • z.fst)‖ ^ 2 +
    ‖-sigma • (z.snd - a • z.fst)‖ ^ 2 = _
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem K_apply_norm_le (a sigma : ℝ) (hsigma : 0 ≤ sigma) (z : Pair E) :
    ‖K a sigma z‖ ≤ sigma * (1 + a ^ 2) * ‖z‖ := by
  have hres : ‖z.snd - a • z.fst‖ ^ 2 ≤ (1 + a ^ 2) * ‖z‖ ^ 2 := by
    have hh := relay_residual_square a z
    nlinarith only [hh, sq_nonneg ‖z.fst + a • z.snd‖]
  have hm := mul_le_mul_of_nonneg_left hres (by positivity : 0 ≤ sigma ^ 2 * (1 + a ^ 2))
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ sigma * (1 + a ^ 2) * ‖z‖)).mp
  rw [K_norm_sq]
  nlinarith only [hm]

theorem K_norm_le (a sigma : ℝ) (hsigma : 0 ≤ sigma) :
    ‖K (E := E) a sigma‖ ≤ sigma * (1 + a ^ 2) := by
  exact (K (E := E) a sigma).opNorm_le_bound (by positivity) (K_apply_norm_le a sigma hsigma)

theorem actual_hessian_bilinear_bound (a sigma : ℝ) (hsigma : 0 ≤ sigma) (z h k : Pair E) :
    |fderiv ℝ (fderiv ℝ (quadratic (E := E) a sigma)) z h k| ≤
      (sigma * (1 + a ^ 2)) * ‖h‖ * ‖k‖ := by
  rw [actual_hessian_constant]
  change |inner ℝ (K a sigma h) k| ≤ _
  have hop : ‖K a sigma h‖ ≤ sigma * (1 + a ^ 2) * ‖h‖ := K_apply_norm_le a sigma hsigma h
  have hh := (abs_real_inner_le_norm (K a sigma h) k).trans
    (mul_le_mul_of_nonneg_right hop (norm_nonneg k))
  exact hh

theorem actual_hessian_budget (a sigma : ℝ) (hsigma : 0 ≤ sigma) :
    (fderiv ℝ (fderiv ℝ (quadratic (E := E) a sigma)) =
      (fun _ => (innerSL ℝ).comp (K (E := E) a sigma))) ∧
      ‖K (E := E) a sigma‖ ≤ sigma * (1 + a ^ 2) :=
  ⟨actual_hessian_constant a sigma, K_norm_le a sigma hsigma⟩

end
end FangqingRelayQuadraticBounds
end

section
-- Source component: RelayGlobalJointClass.lean

open scoped BigOperators ContDiff NNReal

namespace FangqingRelayGlobalJointClass

open FangqingRelayBlockGeometry FangqingRelayAnalyticAssembly FangqingDisjointBlockBounds
  FangqingC2BlockRegularity FangqingJetToRegularity FangqingHessianTensorIsometry

set_option maxHeartbeats 1800000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem blockSum_contDiff_two {I X : Type*} [Fintype I] [NormedAddCommGroup X] [NormedSpace ℝ X]
    (P : I → X →L[ℝ] E) (f : I → E → ℝ) (hc : ∀ i, ContDiff ℝ 2 (f i)) :
    ContDiff ℝ 2 (blockSum P f) := by
  classical
  apply ContDiff.sum
  intro i hi
  exact (hc i).comp (P i).contDiff

theorem relay_contDiff (a sigma : ℝ) : ContDiff ℝ 2 (localRelay (E := E) a sigma) := by
  have hi : ContDiff ℝ 2 (fun z : Pair E => z.snd - a • z.fst) :=
    (WithLp.sndL 2 ℝ E E).contDiff.sub ((WithLp.fstL 2 ℝ E E).contDiff.const_smul a)
  exact contDiff_const.mul (hi.norm_sq ℝ)

theorem relay_actual_second_jet (a sigma : ℝ) (hs : 0 ≤ sigma) (z : Pair E) :
    ‖iteratedFDeriv ℝ 2 (localRelay a sigma) z‖ ≤ sigma * (1 + a ^ 2) := by
  refine (iteratedFDeriv ℝ 2 (localRelay a sigma) z).opNorm_le_bound (by positivity) ?_
  intro v
  simp only [iteratedFDeriv_two_apply, Fin.prod_univ_two]
  simpa only [Real.norm_eq_abs, mul_assoc] using!
    FangqingRelayQuadraticBounds.actual_hessian_bilinear_bound a sigma hs z (v 0) (v 1)

theorem relay_actual_second_jet_lip (a sigma : ℝ) (x y : Pair E) :
    ‖iteratedFDeriv ℝ 2 (localRelay a sigma) x - iteratedFDeriv ℝ 2 (localRelay a sigma) y‖ = 0 := by
  have heq : iteratedFDeriv ℝ 2 (localRelay a sigma) x = iteratedFDeriv ℝ 2 (localRelay a sigma) y := by
    ext v
    simp only [iteratedFDeriv_two_apply]
    change fderiv ℝ (fderiv ℝ (FangqingRelayQuadraticBounds.quadratic a sigma)) x (v 0) (v 1) =
      fderiv ℝ (fderiv ℝ (FangqingRelayQuadraticBounds.quadratic a sigma)) y (v 0) (v 1)
    rw [FangqingRelayQuadraticBounds.actual_hessian_constant]
  rw [heq, sub_self, norm_zero]

theorem sum3_c2_jet_bounds {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g h : X → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h)
    (A B C Rf Rg Rh : ℝ)
    (hA : ∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ A)
    (hB : ∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ B)
    (hC : ∀ z, ‖iteratedFDeriv ℝ 2 h z‖ ≤ C)
    (hRf : ∀ x y, ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y‖ ≤ Rf * ‖x - y‖)
    (hRg : ∀ x y, ‖iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y‖ ≤ Rg * ‖x - y‖)
    (hRh : ∀ x y, ‖iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y‖ ≤ Rh * ‖x - y‖) :
    (∀ z, ‖iteratedFDeriv ℝ 2 (fun z => f z + g z + h z) z‖ ≤ A + B + C) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 (fun z => f z + g z + h z) x -
      iteratedFDeriv ℝ 2 (fun z => f z + g z + h z) y‖ ≤ (Rf + Rg + Rh) * ‖x - y‖) := by
  have heq : ∀ z, iteratedFDeriv ℝ 2 (fun z => f z + g z + h z) z =
      iteratedFDeriv ℝ 2 f z + iteratedFDeriv ℝ 2 g z + iteratedFDeriv ℝ 2 h z := by
    intro z
    rw [fun_iteratedFDeriv_add_apply (hf.add hg).contDiffAt hh.contDiffAt,
      fun_iteratedFDeriv_add_apply hf.contDiffAt hg.contDiffAt]
  refine ⟨?_, ?_⟩
  · intro z
    rw [heq]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hA z) (hB z))) (hC z))
  · intro x y
    rw [heq x, heq y]
    have halg : iteratedFDeriv ℝ 2 f x + iteratedFDeriv ℝ 2 g x + iteratedFDeriv ℝ 2 h x -
        (iteratedFDeriv ℝ 2 f y + iteratedFDeriv ℝ 2 g y + iteratedFDeriv ℝ 2 h y) =
        (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y) +
        (iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y) +
        (iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y) := by abel
    rw [halg]
    have hfg := norm_add_le (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y)
      (iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y)
    have hall := norm_add_le
      ((iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y) + (iteratedFDeriv ℝ 2 g x - iteratedFDeriv ℝ 2 g y))
      (iteratedFDeriv ℝ 2 h x - iteratedFDeriv ℝ 2 h y)
    have hb := hall.trans (add_le_add (hfg.trans (add_le_add (hRf x y) (hRg x y))) (hRh x y))
    convert! hb using 1 <;> try ring

def HessianRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (J : X → ℝ) (rho : ℝ) : Prop :=
  ∀ x y, ‖fderiv ℝ (fderiv ℝ J) x - fderiv ℝ (fderiv ℝ J) y‖ ≤ rho * ‖x - y‖

theorem actual_assembled_joint_class (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (Lp Rp Ll Rl : ℝ) (hsigma : 0 ≤ sigma) (hLp : 0 ≤ Lp) (hRp : 0 ≤ Rp) (hLl : 0 ≤ Ll) (hRl : 0 ≤ Rl)
    (hpc : ∀ t, ContDiff ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t))
    (hp2 : ∀ t z, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) z‖ ≤ Lp)
    (hpLip : ∀ t x y, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) x -
      iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) y‖ ≤ Rp * ‖x - y‖)
    (hlc : ∀ j, ContDiff ℝ 3 (localLink n reward h0 h1 m0 m1 gate j))
    (hl2 : ∀ j z, ‖iteratedFDeriv ℝ 2 (localLink n reward h0 h1 m0 m1 gate j) z‖ ≤ Ll)
    (hl3 : ∀ j z, ‖iteratedFDeriv ℝ 3 (localLink n reward h0 h1 m0 m1 gate j) z‖ ≤ Rl) :
    let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
    ContDiff ℝ 2 J ∧
    (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Lp + sigma * (1 + a ^ 2) + Ll) * ‖x - y‖) ∧
    HessianRate J (Rp + Rl) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 J z‖ ≤ Lp + sigma * (1 + a ^ 2) + Ll) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 J x - iteratedFDeriv ℝ 2 J y‖ ≤ (Rp + Rl) * ‖x - y‖) := by
  intro J
  let fp := blockSum (packet n) (localPacket n beta lam h0 h1 m0 m1)
  let fr := blockSum (relay n) (fun _ : Fin (n + 1) => localRelay (E := E) a sigma)
  let fl := blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)
  have hfc : ContDiff ℝ 2 fp := blockSum_contDiff_two _ _ hpc
  have hrc : ContDiff ℝ 2 fr := blockSum_contDiff_two _ _ (fun _ => relay_contDiff a sigma)
  have hlc2 : ∀ j, ContDiff ℝ 2 (localLink n reward h0 h1 m0 m1 gate j) := fun j => (hlc j).of_le (by norm_num)
  have hflc : ContDiff ℝ 2 fl := blockSum_contDiff_two _ _ hlc2
  have hfp2 : ∀ z, ‖iteratedFDeriv ℝ 2 fp z‖ ≤ Lp := fun z =>
    second_blockSum_bound_c2 _ _ hpc (packet_energy n) Lp hLp z (fun t => hp2 t _)
  have hfr2 : ∀ z, ‖iteratedFDeriv ℝ 2 fr z‖ ≤ sigma * (1 + a ^ 2) := fun z =>
    second_blockSum_bound_c2 _ _ (fun _ => relay_contDiff a sigma) (relay_energy n) _ (by positivity) z
      (fun t => relay_actual_second_jet a sigma hsigma _)
  have hfl2 : ∀ z, ‖iteratedFDeriv ℝ 2 fl z‖ ≤ Ll := fun z =>
    second_blockSum_bound_c2 _ _ hlc2 (link_energy n) Ll hLl z (fun t => hl2 t _)
  have hfpLip : ∀ x y, ‖iteratedFDeriv ℝ 2 fp x - iteratedFDeriv ℝ 2 fp y‖ ≤ Rp * ‖x - y‖ :=
    blockSum_second_jet_lipschitz _ _ hpc (packet_energy n) Rp hRp hpLip
  have hfrLip : ∀ x y, ‖iteratedFDeriv ℝ 2 fr x - iteratedFDeriv ℝ 2 fr y‖ ≤ 0 * ‖x - y‖ :=
    blockSum_second_jet_lipschitz _ _ (fun _ => relay_contDiff a sigma) (relay_energy n) 0 (by norm_num)
      (fun _ x y => by rw [relay_actual_second_jet_lip, zero_mul])
  let Rln : ℝ≥0 := ⟨Rl, hRl⟩
  have hLinkLip : ∀ j x y, ‖iteratedFDeriv ℝ 2 (localLink n reward h0 h1 m0 m1 gate j) x -
      iteratedFDeriv ℝ 2 (localLink n reward h0 h1 m0 m1 gate j) y‖ ≤ Rl * ‖x - y‖ := by
    intro j x y
    exact (second_jet_lipschitz_from_third_jet _ (hlc j) Rln (hl3 j)).norm_sub_le x y
  have hflLip : ∀ x y, ‖iteratedFDeriv ℝ 2 fl x - iteratedFDeriv ℝ 2 fl y‖ ≤ Rl * ‖x - y‖ :=
    blockSum_second_jet_lipschitz _ _ hlc2 (link_energy n) Rl hRl hLinkLip
  obtain ⟨h2, h2Lip⟩ := sum3_c2_jet_bounds fp fr fl hfc hrc hflc Lp (sigma * (1 + a ^ 2)) Ll Rp 0 Rl
    hfp2 hfr2 hfl2 hfpLip hfrLip hflLip
  have hc : ContDiff ℝ 2 J := (hfc.add hrc).add hflc
  let Ln : ℝ≥0 := ⟨Lp + sigma * (1 + a ^ 2) + Ll, by positivity⟩
  have hgrad := gradient_lipschitz_from_second_jet J hc Ln h2
  have hJlip : ∀ x y, ‖iteratedFDeriv ℝ 2 J x - iteratedFDeriv ℝ 2 J y‖ ≤ (Rp + Rl) * ‖x - y‖ := by
    intro x y
    simpa only [add_zero] using! h2Lip x y
  refine ⟨hc, fun x y => hgrad.norm_sub_le x y, ?_, h2, hJlip⟩
  intro x y
  exact (FangqingJetToRegularity.hessian_difference_norm_le_second_jet J x y).trans (hJlip x y)

end
end FangqingRelayGlobalJointClass
end

section
-- Source component: RelayPairHessian.lean

open scoped ContDiff

namespace FangqingRelayPairHessian

open FangqingRelayBlockGeometry FangqingRelayStationarity FangqingC2HessianAlgebra

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def base (h : E → ℝ) (lam constant : ℝ) (xc y : E) : ℝ :=
  h y - lam * inner ℝ xc y + constant

theorem base_eq_neg_endpoint (β lam m : ℝ) (h : E → ℝ) (xc y : E) :
    base h lam (-β / 2 * ‖xc‖ ^ 2 - m) xc y = -endpoint β lam h m xc y := by
  dsimp [base, endpoint]
  ring

theorem base_contDiff (h : E → ℝ) (lam constant : ℝ) (xc : E) (hh : ContDiff ℝ 2 h) :
    ContDiff ℝ 2 (base h lam constant xc) := by
  have hlin : ContDiff ℝ 2 (fun y : E => inner ℝ xc y) := (innerSL ℝ xc).contDiff
  exact (hh.sub (contDiff_const.mul hlin)).add contDiff_const

theorem base_hessian (h : E → ℝ) (lam constant : ℝ) (xc y u v : E)
    (hh : ContDiff ℝ 2 h) :
    fderiv ℝ (fderiv ℝ (base h lam constant xc)) y u v = fderiv ℝ (fderiv ℝ h) y u v := by
  have hd := hh.differentiable (by norm_num)
  have hfirst : fderiv ℝ (base h lam constant xc) = fun z => fderiv ℝ h z - lam • innerSL ℝ xc := by
    funext z
    exact (((hd z).hasFDerivAt.sub ((innerSL ℝ xc).hasFDerivAt.const_mul lam)).add_const constant).fderiv
  have hd2 := (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hsecond := ((hd2 y).hasFDerivAt.sub_const (lam • innerSL ℝ xc))
  rw [hfirst, hsecond.fderiv]

theorem delta_contDiff (h0 h1 : E → ℝ) (m0 m1 : ℝ)
    (h0c : ContDiff ℝ 2 h0) (h1c : ContDiff ℝ 2 h1) :
    ContDiff ℝ 2 (delta h0 h1 m0 m1) := ((h0c.sub h1c).add contDiff_const).sub contDiff_const

theorem delta_first (h0 h1 : E → ℝ) (m0 m1 : ℝ)
    (h0d : Differentiable ℝ h0) (h1d : Differentiable ℝ h1) (y v : E) :
    fderiv ℝ (delta h0 h1 m0 m1) y v = fderiv ℝ h0 y v - fderiv ℝ h1 y v := by
  have hd : HasFDerivAt (delta h0 h1 m0 m1) (fderiv ℝ h0 y - fderiv ℝ h1 y) y := by
    simpa only [delta, Pi.sub_apply] using!
      (((h0d y).hasFDerivAt.sub (h1d y).hasFDerivAt).add_const m1).sub_const m0
  rw [hd.fderiv]
  rfl

theorem delta_hessian (h0 h1 : E → ℝ) (m0 m1 : ℝ)
    (h0c : ContDiff ℝ 2 h0) (h1c : ContDiff ℝ 2 h1) (y u v : E) :
    fderiv ℝ (fderiv ℝ (delta h0 h1 m0 m1)) y u v =
      fderiv ℝ (fderiv ℝ h0) y u v - fderiv ℝ (fderiv ℝ h1) y u v := by
  have hfirst : fderiv ℝ (delta h0 h1 m0 m1) = fun z => fderiv ℝ h0 z - fderiv ℝ h1 z := by
    funext z
    exact ((((h0c.differentiable (by norm_num) z).hasFDerivAt.sub
      (h1c.differentiable (by norm_num) z).hasFDerivAt).add_const m1).sub_const m0).fderiv
  have h0d := (h0c.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1d := (h1c.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hs := ((h0d y).hasFDerivAt.sub (h1d y).hasFDerivAt)
  have hsf : HasFDerivAt (fun z => fderiv ℝ h0 z - fderiv ℝ h1 z)
      (fderiv ℝ (fderiv ℝ h0) y - fderiv ℝ (fderiv ℝ h1) y) y := hs
  rw [hfirst, hsf.fderiv]
  rfl

theorem norm_sub_sq_hessian (center x h k : E) :
    fderiv ℝ (fderiv ℝ (fun z : E => ‖z - center‖ ^ 2)) x h k = 2 * inner ℝ h k := by
  have hfirst : fderiv ℝ (fun z : E => ‖z - center‖ ^ 2) =
      (fun z => (2 : ℕ) • innerSL ℝ (z - center)) := by
    funext z
    have hh := ((hasFDerivAt_id z).sub_const center).norm_sq
    simpa only [id_eq, ContinuousLinearMap.comp_id] using hh.fderiv
  have hlin := ((innerSL ℝ).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const center))
  have hs := hlin.add hlin
  have hs' : HasFDerivAt (fun z => (2 : ℕ) • innerSL ℝ (z - center)) ((2 : ℕ) • innerSL ℝ) x := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id, two_nsmul, Pi.add_apply] using! hs
  rw [hfirst, hs'.fderiv]
  rw [two_nsmul, ContinuousLinearMap.add_apply]
  change inner ℝ h k + inner ℝ h k = 2 * inner ℝ h k
  ring

def negativePair (h0 h1 gate : E → ℝ) (lam constant m0 m1 reward sigma : ℝ)
    (xc center : E) (z : Pair E) : ℝ :=
  base h0 lam constant xc z.snd -
    gate z.fst * (delta h0 h1 m0 m1 z.snd - reward) +
    sigma / 2 * ‖z.fst - center‖ ^ 2

theorem negativePair_contDiff (h0 h1 gate : E → ℝ)
    (lam constant m0 m1 reward sigma : ℝ) (xc center : E)
    (h0c : ContDiff ℝ 2 h0) (h1c : ContDiff ℝ 2 h1) (hgc : ContDiff ℝ 2 gate) :
    ContDiff ℝ 2 (negativePair h0 h1 gate lam constant m0 m1 reward sigma xc center) := by
  let P : Pair E →L[ℝ] E := WithLp.fstL 2 ℝ E E
  let Q : Pair E →L[ℝ] E := WithLp.sndL 2 ℝ E E
  let D : E → ℝ := fun y => delta h0 h1 m0 m1 y - reward
  let N : E → ℝ := fun s => ‖s - center‖ ^ 2
  have hbc := base_contDiff h0 lam constant xc h0c
  have hdc : ContDiff ℝ 2 D := (delta_contDiff h0 h1 m0 m1 h0c h1c).sub contDiff_const
  have hNc : ContDiff ℝ 2 N := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hbQ : ContDiff ℝ 2 ((base h0 lam constant xc) ∘ Q) := hbc.comp_continuousLinearMap
  have hgP : ContDiff ℝ 2 (gate ∘ P) := hgc.comp_continuousLinearMap
  have hdQ : ContDiff ℝ 2 (D ∘ Q) := hdc.comp_continuousLinearMap
  have hnP : ContDiff ℝ 2 (N ∘ P) := hNc.comp_continuousLinearMap
  simpa only [negativePair, D, N, P, Q, Function.comp_def] using!
    (hbQ.sub (hgP.mul hdQ)).add (contDiff_const.mul hnP)

theorem negativePair_hessian_form (h0 h1 gate : E → ℝ)
    (lam constant m0 m1 reward sigma : ℝ) (xc center : E)
    (h0c : ContDiff ℝ 2 h0) (h1c : ContDiff ℝ 2 h1) (hgc : ContDiff ℝ 2 gate)
    (z v : Pair E) :
    fderiv ℝ (fderiv ℝ (negativePair h0 h1 gate lam constant m0 m1 reward sigma xc center)) z v v =
      sigma * ‖v.fst‖ ^ 2 +
      (1 - gate z.fst) * fderiv ℝ (fderiv ℝ h0) z.snd v.snd v.snd +
      gate z.fst * fderiv ℝ (fderiv ℝ h1) z.snd v.snd v.snd -
      (delta h0 h1 m0 m1 z.snd - reward) * fderiv ℝ (fderiv ℝ gate) z.fst v.fst v.fst -
      2 * fderiv ℝ gate z.fst v.fst *
        (fderiv ℝ h0 z.snd v.snd - fderiv ℝ h1 z.snd v.snd) := by
  let P : Pair E →L[ℝ] E := WithLp.fstL 2 ℝ E E
  let Q : Pair E →L[ℝ] E := WithLp.sndL 2 ℝ E E
  let F : Pair E → ℝ := (base h0 lam constant xc) ∘ Q
  let G : Pair E → ℝ := gate ∘ P
  let D : E → ℝ := fun y => delta h0 h1 m0 m1 y - reward
  let J : Pair E → ℝ := D ∘ Q
  let N : E → ℝ := fun s => ‖s - center‖ ^ 2
  let R : Pair E → ℝ := fun w => sigma / 2 * N (P w)
  have hbc := base_contDiff h0 lam constant xc h0c
  have hdc : ContDiff ℝ 2 D := (delta_contDiff h0 h1 m0 m1 h0c h1c).sub contDiff_const
  have hNc : ContDiff ℝ 2 N := (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hFc : ContDiff ℝ 2 F := hbc.comp_continuousLinearMap
  have hGc : ContDiff ℝ 2 G := hgc.comp_continuousLinearMap
  have hJc : ContDiff ℝ 2 J := hdc.comp_continuousLinearMap
  have hNPc : ContDiff ℝ 2 (N ∘ P) := hNc.comp_continuousLinearMap
  have hRc : ContDiff ℝ 2 R := contDiff_const.mul hNPc
  have hfun : negativePair h0 h1 gate lam constant m0 m1 reward sigma xc center =
      (fun w => F w - G w * J w + R w) := rfl
  rw [hfun, hessian_add (fun w => F w - G w * J w) R (hFc.sub (hGc.mul hJc)) hRc,
    hessian_sub F (fun w => G w * J w) hFc (hGc.mul hJc), hessian_mul G J hGc hJc]
  rw [hessian_pullback _ Q hbc, base_hessian _ lam constant xc _ _ _ h0c]
  have hRhes : fderiv ℝ (fderiv ℝ R) z v v = sigma * ‖v.fst‖ ^ 2 := by
    change fderiv ℝ (fderiv ℝ (fun w => sigma / 2 * (N ∘ P) w)) z v v = _
    rw [hessian_const_mul (N ∘ P) hNPc (sigma / 2), hessian_pullback N P hNc]
    dsimp only [N]
    rw [norm_sub_sq_hessian, real_inner_self_eq_norm_sq]
    change sigma / 2 * (2 * ‖v.fst‖ ^ 2) = _
    ring
  have hGhes : fderiv ℝ (fderiv ℝ G) z v v = fderiv ℝ (fderiv ℝ gate) (P z) (P v) (P v) :=
    hessian_pullback gate P hgc z v v
  have hJhes : fderiv ℝ (fderiv ℝ J) z v v = fderiv ℝ (fderiv ℝ D) (Q z) (Q v) (Q v) :=
    hessian_pullback D Q hdc z v v
  rw [hRhes, hGhes, hJhes]
  have hDsecond : fderiv ℝ (fderiv ℝ D) z.snd v.snd v.snd =
      fderiv ℝ (fderiv ℝ h0) z.snd v.snd v.snd - fderiv ℝ (fderiv ℝ h1) z.snd v.snd v.snd := by
    have heq : D = fun y => delta h0 h1 m0 m1 y - reward := rfl
    rw [heq, hessian_sub _ (fun _ => reward)
      (delta_contDiff h0 h1 m0 m1 h0c h1c) contDiff_const]
    have hc0 : fderiv ℝ (fderiv ℝ (fun _ : E => reward)) z.snd v.snd v.snd = 0 := by
      have hcfirst : fderiv ℝ (fun _ : E => reward) = fun _ => (0 : E →L[ℝ] ℝ) := by
        funext w
        exact (hasFDerivAt_const reward w).fderiv
      rw [hcfirst, (hasFDerivAt_const (0 : E →L[ℝ] ℝ) z.snd).fderiv]
      rfl
    rw [hc0, sub_zero]
    exact delta_hessian h0 h1 m0 m1 h0c h1c _ _ _
  have hDfirst : fderiv ℝ D z.snd v.snd = fderiv ℝ h0 z.snd v.snd - fderiv ℝ h1 z.snd v.snd := by
    change fderiv ℝ (fun y => delta h0 h1 m0 m1 y - reward) z.snd v.snd = _
    rw [(((delta_contDiff h0 h1 m0 m1 h0c h1c).differentiable (by norm_num) z.snd).hasFDerivAt.sub_const reward).fderiv]
    exact delta_first h0 h1 m0 m1 (h0c.differentiable (by norm_num)) (h1c.differentiable (by norm_num)) _ _
  have hGfirst : fderiv ℝ G z v = fderiv ℝ gate (P z) (P v) :=
    first_pullback gate P (hgc.differentiable (by norm_num)) z v
  have hJfirst : fderiv ℝ J z v = fderiv ℝ D (Q z) (Q v) :=
    first_pullback D Q (hdc.differentiable (by norm_num)) z v
  rw [hGfirst, hJfirst]
  change fderiv ℝ (fderiv ℝ h0) z.snd v.snd v.snd -
    (gate z.fst * fderiv ℝ (fderiv ℝ D) z.snd v.snd v.snd +
      fderiv ℝ gate z.fst v.fst * fderiv ℝ D z.snd v.snd +
      fderiv ℝ gate z.fst v.fst * fderiv ℝ D z.snd v.snd +
      D z.snd * fderiv ℝ (fderiv ℝ gate) z.fst v.fst v.fst) + sigma * ‖v.fst‖ ^ 2 = _
  rw [hDsecond, hDfirst]
  dsimp [D]
  ring

end
end FangqingRelayPairHessian
end

section
-- Source component: RelayDualCurvature.lean

namespace FangqingRelayDualCurvature

open FangqingRelayBlockGeometry

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def upperLeft (sigma B : ℝ) (H : E →L[ℝ] E) : E →L[ℝ] E :=
  sigma • ContinuousLinearMap.id ℝ E - B • H

def coupledBlock (A D : E →L[ℝ] E) (p g : E) : Pair E →L[ℝ] Pair E :=
  pairMap
    (A.comp (WithLp.fstL 2 ℝ E E) -
      ((innerSL ℝ g).comp (WithLp.sndL 2 ℝ E E)).smulRight p)
    (D.comp (WithLp.sndL 2 ℝ E E) -
      ((innerSL ℝ p).comp (WithLp.fstL 2 ℝ E E)).smulRight g)

theorem coupledBlock_quadratic (A D : E →L[ℝ] E) (p g : E) (z : Pair E) :
    inner ℝ (coupledBlock A D p g z) z =
      inner ℝ (A z.fst) z.fst + inner ℝ (D z.snd) z.snd -
      2 * inner ℝ p z.fst * inner ℝ g z.snd := by
  change inner ℝ (A z.fst - inner ℝ g z.snd • p) z.fst +
    inner ℝ (D z.snd - inner ℝ p z.fst • g) z.snd = _
  rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  ring

theorem upperLeft_coercive (sigma B M Hbound : ℝ) (H : E →L[ℝ] E)
    (hB : |B| ≤ M) (hH : ‖H‖ ≤ Hbound) (hsmall : M * Hbound ≤ sigma / 2) (v : E) :
    sigma / 2 * ‖v‖ ^ 2 ≤ inner ℝ (upperLeft sigma B H v) v := by
  have hM : 0 ≤ M := (abs_nonneg B).trans hB
  have hH0 : 0 ≤ Hbound := (norm_nonneg H).trans hH
  have hop : ‖H v‖ ≤ Hbound * ‖v‖ :=
    (H.le_opNorm v).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg v))
  have hi : |inner ℝ (H v) v| ≤ Hbound * ‖v‖ ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hop (norm_nonneg v)
    nlinarith only [abs_real_inner_le_norm (H v) v, hh]
  have hmul := mul_le_mul hB hi (abs_nonneg _) hM
  rw [← abs_mul] at hmul
  have hu : B * inner ℝ (H v) v ≤ M * Hbound * ‖v‖ ^ 2 :=
    (le_abs_self _).trans (by nlinarith only [hmul])
  have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖v‖)
  simp only [upperLeft, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  nlinarith only [hu, hs]

theorem scalar_cross_young (sigma P G v w : ℝ) (hsigma : 0 < sigma) :
    2 * P * G * v * w ≤ sigma / 4 * v ^ 2 + (4 * P ^ 2 * G ^ 2 / sigma) * w ^ 2 := by
  have hh : 0 ≤ (sigma * v - 4 * P * G * w) ^ 2 / (4 * sigma) := by positivity
  have heq : (sigma * v - 4 * P * G * w) ^ 2 / (4 * sigma) =
      sigma / 4 * v ^ 2 + (4 * P ^ 2 * G ^ 2 / sigma) * w ^ 2 -
        2 * P * G * v * w := by
    field_simp
    <;> ring
  rw [heq] at hh
  linarith only [hh]

theorem coupledBlock_coercive (A D : E →L[ℝ] E) (p g : E)
    (sigma d mu : ℝ) (hsigma : 0 < sigma) (hmu : 4 * mu ≤ sigma)
    (hschur : mu + 4 * ‖p‖ ^ 2 * ‖g‖ ^ 2 / sigma ≤ d)
    (hA : ∀ v, sigma / 2 * ‖v‖ ^ 2 ≤ inner ℝ (A v) v)
    (hD : ∀ w, d * ‖w‖ ^ 2 ≤ inner ℝ (D w) w) (z : Pair E) :
    mu * ‖z‖ ^ 2 ≤ inner ℝ (coupledBlock A D p g z) z := by
  have hip := abs_real_inner_le_norm p z.fst
  have hig := abs_real_inner_le_norm g z.snd
  have hm := mul_le_mul hip hig (abs_nonneg _) (by positivity : 0 ≤ ‖p‖ * ‖z.fst‖)
  rw [← abs_mul] at hm
  have hcross : 2 * inner ℝ p z.fst * inner ℝ g z.snd ≤
      2 * ‖p‖ * ‖g‖ * ‖z.fst‖ * ‖z.snd‖ := by
    have hraw := (le_abs_self (inner ℝ p z.fst * inner ℝ g z.snd)).trans hm
    nlinarith only [hraw]
  have hy := scalar_cross_young sigma ‖p‖ ‖g‖ ‖z.fst‖ ‖z.snd‖ hsigma
  have hnum := mul_le_mul_of_nonneg_right hschur (sq_nonneg ‖z.snd‖)
  have hcurv := mul_le_mul_of_nonneg_right hmu (sq_nonneg ‖z.fst‖)
  rw [coupledBlock_quadratic, WithLp.prod_norm_sq_eq_of_L2]
  nlinarith only [hA z.fst, hD z.snd, hcross, hy, hnum, hcurv]

theorem private_relay_dual_block_coercive (sigma B M Hbound d mu : ℝ)
    (H D : E →L[ℝ] E) (p g : E)
    (hsigma : 0 < sigma) (hmu : 4 * mu ≤ sigma)
    (hB : |B| ≤ M) (hH : ‖H‖ ≤ Hbound) (hsmall : M * Hbound ≤ sigma / 2)
    (hschur : mu + 4 * ‖p‖ ^ 2 * ‖g‖ ^ 2 / sigma ≤ d)
    (hD : ∀ w, d * ‖w‖ ^ 2 ≤ inner ℝ (D w) w) (z : Pair E) :
    mu * ‖z‖ ^ 2 ≤ inner ℝ (coupledBlock (upperLeft sigma B H) D p g z) z :=
  coupledBlock_coercive _ D p g sigma d mu hsigma hmu hschur
    (upperLeft_coercive sigma B M Hbound H hB hH hsmall) hD z

end
end FangqingRelayDualCurvature
end

section
-- Source component: RelayPairConcavity.lean

namespace FangqingRelayPairConcavity

open FangqingRelayBlockGeometry FangqingRelayStationarity FangqingRelayPairHessian
  FangqingRelayDualCurvature FangqingHessianStrongConvexity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem negativePair_strongConvex (h0 h1 gate : E → ℝ)
    (lam constant m0 m1 reward sigma d mu M Hbound Pbound Gbound : ℝ) (xc center : E)
    (h0c : ContDiff ℝ 2 h0) (h1c : ContDiff ℝ 2 h1) (hgc : ContDiff ℝ 2 gate)
    (h0sc : StrongConvexOn (Set.univ : Set E) d h0)
    (h1sc : StrongConvexOn (Set.univ : Set E) d h1)
    (hrange : ∀ s, 0 ≤ gate s ∧ gate s ≤ 1)
    (hM : 0 ≤ M) (hHbound : 0 ≤ Hbound) (hP : 0 ≤ Pbound) (hG : 0 ≤ Gbound)
    (hB : ∀ y, |delta h0 h1 m0 m1 y - reward| ≤ M)
    (hGateH : ∀ s v, |fderiv ℝ (fderiv ℝ gate) s v v| ≤ Hbound * ‖v‖ ^ 2)
    (hGateG : ∀ s v, |fderiv ℝ gate s v| ≤ Pbound * ‖v‖)
    (hDeltaG : ∀ y v, |fderiv ℝ (delta h0 h1 m0 m1) y v| ≤ Gbound * ‖v‖)
    (hsigma : 0 < sigma) (hmu : 4 * mu ≤ sigma)
    (hpure : M * Hbound ≤ sigma / 2)
    (hschur : mu + 4 * Pbound ^ 2 * Gbound ^ 2 / sigma ≤ d) :
    StrongConvexOn (Set.univ : Set (Pair E)) mu
      (negativePair h0 h1 gate lam constant m0 m1 reward sigma xc center) := by
  apply strongConvex_of_hessian_lower _ mu
    (negativePair_contDiff h0 h1 gate lam constant m0 m1 reward sigma xc center h0c h1c hgc)
  intro z v
  have h0q := hessian_lower_of_strongConvex h0 d h0c h0sc z.snd v.snd
  have h1q := hessian_lower_of_strongConvex h1 d h1c h1sc z.snd v.snd
  have hα := hrange z.fst
  have h0weighted := mul_le_mul_of_nonneg_left h0q (sub_nonneg.mpr hα.2)
  have h1weighted := mul_le_mul_of_nonneg_left h1q hα.1
  have hpacket : d * ‖v.snd‖ ^ 2 ≤
      (1 - gate z.fst) * fderiv ℝ (fderiv ℝ h0) z.snd v.snd v.snd +
      gate z.fst * fderiv ℝ (fderiv ℝ h1) z.snd v.snd v.snd := by
    nlinarith only [h0weighted, h1weighted]
  have hBH := mul_le_mul (hB z.snd) (hGateH z.fst v.fst)
    (abs_nonneg _) hM
  rw [← abs_mul] at hBH
  have hpureterm : (delta h0 h1 m0 m1 z.snd - reward) *
      fderiv ℝ (fderiv ℝ gate) z.fst v.fst v.fst ≤ M * Hbound * ‖v.fst‖ ^ 2 := by
    have hh := (le_abs_self ((delta h0 h1 m0 m1 z.snd - reward) *
      fderiv ℝ (fderiv ℝ gate) z.fst v.fst v.fst)).trans hBH
    nlinarith only [hh]
  have hpuresmall := mul_le_mul_of_nonneg_right hpure (sq_nonneg ‖v.fst‖)
  have hcross := mul_le_mul (hGateG z.fst v.fst) (hDeltaG z.snd v.snd)
    (abs_nonneg _) (mul_nonneg hP (norm_nonneg _))
  rw [← abs_mul, delta_first h0 h1 m0 m1 (h0c.differentiable (by norm_num))
    (h1c.differentiable (by norm_num))] at hcross
  have hmixed : 2 * fderiv ℝ gate z.fst v.fst *
      (fderiv ℝ h0 z.snd v.snd - fderiv ℝ h1 z.snd v.snd) ≤
      2 * Pbound * Gbound * ‖v.fst‖ * ‖v.snd‖ := by
    have hh := (le_abs_self (fderiv ℝ gate z.fst v.fst *
      (fderiv ℝ h0 z.snd v.snd - fderiv ℝ h1 z.snd v.snd))).trans hcross
    nlinarith only [hh]
  have hy := scalar_cross_young sigma Pbound Gbound ‖v.fst‖ ‖v.snd‖ hsigma
  have hd := mul_le_mul_of_nonneg_right hschur (sq_nonneg ‖v.snd‖)
  have hs := mul_le_mul_of_nonneg_right hmu (sq_nonneg ‖v.fst‖)
  rw [negativePair_hessian_form h0 h1 gate lam constant m0 m1 reward sigma xc center h0c h1c hgc,
    WithLp.prod_norm_sq_eq_of_L2]
  nlinarith only [hpacket, hpureterm, hpuresmall, hmixed, hy, hd, hs]

end
end FangqingRelayPairConcavity
end

section
-- Source component: StrongConvexBlockAssembly.lean

open scoped BigOperators

namespace FangqingStrongConvexBlockAssembly

variable {I X A B C : Type*} [Fintype I]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]

theorem score_pullback (f : A → ℝ) (mu : ℝ)
    (hf : StrongConvexOn (Set.univ : Set A) mu f) (P : X →L[ℝ] A)
    (x y : X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (P (a • x + b • y)) - mu / 2 * ‖P (a • x + b • y)‖ ^ 2 ≤
      a * (f (P x) - mu / 2 * ‖P x‖ ^ 2) +
      b * (f (P y) - mu / 2 * ‖P y‖ ^ 2) := by
  have hh := (strongConvexOn_iff_convex.mp hf).2 (Set.mem_univ (P x)) (Set.mem_univ (P y)) ha hb hab
  have hmap : P (a • x + b • y) = a • P x + b • P y := by simp
  rw [← hmap] at hh
  simpa only [smul_eq_mul] using hh

theorem three_group_strongConvex (mu : ℝ) (f : A → ℝ) (g : B → ℝ) (h : I → C → ℝ)
    (P : X →L[ℝ] A) (Q : X →L[ℝ] B) (R : I → X →L[ℝ] C)
    (hf : StrongConvexOn (Set.univ : Set A) mu f)
    (hg : StrongConvexOn (Set.univ : Set B) mu g)
    (hh : ∀ i, StrongConvexOn (Set.univ : Set C) mu (h i))
    (henergy : ∀ z : X, ‖P z‖ ^ 2 + (∑ i, ‖R i z‖ ^ 2) + ‖Q z‖ ^ 2 = ‖z‖ ^ 2) :
    StrongConvexOn (Set.univ : Set X) mu (fun z => f (P z) + (∑ i, h i (R i z)) + g (Q z)) := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hP := score_pullback f mu hf P x y a b ha hb hab
  have hQ := score_pullback g mu hg Q x y a b ha hb hab
  have hR := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset I)) => score_pullback (h i) mu (hh i) (R i) x y a b ha hb hab)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hR
  have hez := congrArg (fun v : ℝ => mu / 2 * v) (henergy z)
  have hex := congrArg (fun v : ℝ => a * (mu / 2 * v)) (henergy x)
  have hey := congrArg (fun v : ℝ => b * (mu / 2 * v)) (henergy y)
  change f (P z) + (∑ i, h i (R i z)) + g (Q z) - mu / 2 * ‖z‖ ^ 2 ≤
    a * (f (P x) + (∑ i, h i (R i x)) + g (Q x) - mu / 2 * ‖x‖ ^ 2) +
    b * (f (P y) + (∑ i, h i (R i y)) + g (Q y) - mu / 2 * ‖y‖ ^ 2)
  change _ ≤ _ at hP hQ hR
  nlinarith only [hP, hQ, hR, hez, hex, hey]

end FangqingStrongConvexBlockAssembly
end

section
-- Source component: RelayDualAssembly.lean

open scoped BigOperators ContDiff

namespace FangqingRelayDualAssembly

open FangqingRelayBlockGeometry FangqingRelayStationarity FangqingRelayPairHessian
  FangqingStrongConvexBlockAssembly FangqingHessianStrongConvexity FangqingC2HessianAlgebra
  FangqingRelayPairConcavity

noncomputable section

abbrev Dual (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin 2 × Fin (n + 1) => E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def first (n : ℕ) : Dual n E →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin 2 × Fin (n + 1) => E) (0, 0)

def last (n : ℕ) : Dual n E →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin 2 × Fin (n + 1) => E) (1, Fin.last n)

def dualLink (n : ℕ) (j : Fin n) : Dual n E →L[ℝ] Pair E :=
  pairMap (PiLp.proj 2 (fun _ : Fin 2 × Fin (n + 1) => E) (1, j.castSucc))
    (PiLp.proj 2 (fun _ : Fin 2 × Fin (n + 1) => E) (0, j.succ))

theorem dual_energy (n : ℕ) (z : Dual n E) :
    ‖first n z‖ ^ 2 + (∑ j, ‖dualLink n j z‖ ^ 2) + ‖last n z‖ ^ 2 = ‖z‖ ^ 2 := by
  have hy : (∑ t : Fin (n + 1), ‖z (0, t)‖ ^ 2) =
      ‖z (0, 0)‖ ^ 2 + ∑ j : Fin n, ‖z (0, j.succ)‖ ^ 2 := Fin.sum_univ_succ _
  have hs : (∑ t : Fin (n + 1), ‖z (1, t)‖ ^ 2) =
      (∑ j : Fin n, ‖z (1, j.castSucc)‖ ^ 2) + ‖z (1, Fin.last n)‖ ^ 2 := Fin.sum_univ_castSucc _
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Fin.sum_univ_two, hy, hs]
  simp_rw [dualLink, pairMap_norm_sq]
  rw [Finset.sum_add_distrib]
  simp only [first, last, PiLp.proj_apply]
  ring

def firstFunction (n : ℕ) (β lam : ℝ) (h1 : Fin (n + 1) → E → ℝ)
    (m1 : Fin (n + 1) → ℝ) (x : Fin (n + 1) → E) : E → ℝ :=
  base (h1 0) lam (-β / 2 * ‖x 0‖ ^ 2 - m1 0) (x 0)

def lastFunction (n : ℕ) (a sigma : ℝ) (x : Fin (n + 1) → E) (s : E) : ℝ :=
  sigma / 2 * ‖s - a • x (Fin.last n)‖ ^ 2

def pairFunction (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x : Fin (n + 1) → E) (j : Fin n) : Pair E → ℝ :=
  negativePair (h0 j.succ) (h1 j.succ) (gate j) lam
    (-β / 2 * ‖x j.succ‖ ^ 2 - m0 j.succ) (m0 j.succ) (m1 j.succ) reward sigma
    (x j.succ) (a • x j.castSucc)

def negativeFamily (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x : Fin (n + 1) → E) (z : Dual n E) : ℝ :=
  -family n β lam a sigma reward h0 h1 m0 m1 gate x (fun t => z (0, t)) (fun t => z (1, t))

theorem exact_dual_decomposition (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x : Fin (n + 1) → E) (z : Dual n E) :
    negativeFamily n β lam a sigma reward h0 h1 m0 m1 gate x z =
      firstFunction n β lam h1 m1 x (first n z) +
        (∑ j, pairFunction n β lam a sigma reward h0 h1 m0 m1 gate x j (dualLink n j z)) +
        lastFunction n a sigma x (last n z) := by
  have hpair : ∀ j : Fin n,
      pairFunction n β lam a sigma reward h0 h1 m0 m1 gate x j (dualLink n j z) =
      -endpoint β lam (h0 j.succ) (m0 j.succ) (x j.succ) (z (0, j.succ)) -
        gate j (z (1, j.castSucc)) *
          (delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) (z (0, j.succ)) - reward) +
        sigma / 2 * ‖z (1, j.castSucc) - a • x j.castSucc‖ ^ 2 := by
    intro j
    change base (h0 j.succ) lam (-β / 2 * ‖x j.succ‖ ^ 2 - m0 j.succ) (x j.succ) (z (0, j.succ)) -
      gate j (z (1, j.castSucc)) *
        (delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) (z (0, j.succ)) - reward) +
      sigma / 2 * ‖z (1, j.castSucc) - a • x j.castSucc‖ ^ 2 = _
    rw [base_eq_neg_endpoint]
  have hd : ∀ j : Fin n,
      endpoint β lam (h1 j.succ) (m1 j.succ) (x j.succ) (z (0, j.succ)) -
      endpoint β lam (h0 j.succ) (m0 j.succ) (x j.succ) (z (0, j.succ)) =
      delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) (z (0, j.succ)) := by
    intro j
    dsimp [endpoint, delta]
    ring
  have hs : (∑ t : Fin (n + 1), ‖z (1, t) - a • x t‖ ^ 2) =
      (∑ j : Fin n, ‖z (1, j.castSucc) - a • x j.castSucc‖ ^ 2) +
        ‖z (1, Fin.last n) - a • x (Fin.last n)‖ ^ 2 := Fin.sum_univ_castSucc _
  unfold negativeFamily
  rw [family_eq_paper]
  simp_rw [hd, hpair]
  change _ = base (h1 0) lam (-β / 2 * ‖x 0‖ ^ 2 - m1 0) (x 0) (z (0, 0)) + _ + _
  rw [base_eq_neg_endpoint, hs]
  simp only [lastFunction, last, PiLp.proj_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul,
    mul_sub, mul_add, add_mul, div_eq_mul_inv, mul_assoc]
  ring

theorem dual_strongConvex_from_components (n : ℕ) (β lam a sigma reward mu : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x : Fin (n + 1) → E)
    (hf : StrongConvexOn (Set.univ : Set E) mu (firstFunction n β lam h1 m1 x))
    (hl : StrongConvexOn (Set.univ : Set E) mu (lastFunction n a sigma x))
    (hp : ∀ j, StrongConvexOn (Set.univ : Set (Pair E)) mu
      (pairFunction n β lam a sigma reward h0 h1 m0 m1 gate x j)) :
    StrongConvexOn (Set.univ : Set (Dual n E)) mu
      (negativeFamily n β lam a sigma reward h0 h1 m0 m1 gate x) := by
  have hfun : negativeFamily n β lam a sigma reward h0 h1 m0 m1 gate x =
      fun z => firstFunction n β lam h1 m1 x (first n z) +
        (∑ j, pairFunction n β lam a sigma reward h0 h1 m0 m1 gate x j (dualLink n j z)) +
        lastFunction n a sigma x (last n z) := by
    funext z
    exact exact_dual_decomposition n β lam a sigma reward h0 h1 m0 m1 gate x z
  rw [hfun]
  simpa only [] using! three_group_strongConvex (X := Dual n E) (A := E) (B := E) (C := Pair E) mu
    (firstFunction n β lam h1 m1 x) (lastFunction n a sigma x)
    (pairFunction n β lam a sigma reward h0 h1 m0 m1 gate x)
    (first n) (last n) (dualLink n) hf hl hp (dual_energy n)


theorem first_strongConvex (n : ℕ) (β lam d mu : ℝ) (h1 : Fin (n + 1) → E → ℝ)
    (m1 : Fin (n + 1) → ℝ) (x : Fin (n + 1) → E)
    (hc : ContDiff ℝ 2 (h1 0)) (hsc : StrongConvexOn (Set.univ : Set E) d (h1 0))
    (hmu : mu ≤ d) :
    StrongConvexOn (Set.univ : Set E) mu (firstFunction n β lam h1 m1 x) := by
  apply strongConvex_of_hessian_lower _ mu (base_contDiff _ lam _ (x 0) hc)
  intro y v
  rw [base_hessian _ lam _ (x 0) _ _ _ hc]
  exact (mul_le_mul_of_nonneg_right hmu (sq_nonneg ‖v‖)).trans
    (hessian_lower_of_strongConvex (h1 0) d hc hsc y v)

theorem last_strongConvex (n : ℕ) (a sigma mu : ℝ) (x : Fin (n + 1) → E)
    (hmu : mu ≤ sigma) :
    StrongConvexOn (Set.univ : Set E) mu (lastFunction n a sigma x) := by
  let center := a • x (Fin.last n)
  have hn : ContDiff ℝ 2 (fun s : E => ‖s - center‖ ^ 2) :=
    (contDiff_id.sub contDiff_const).norm_sq ℝ
  have hf : ContDiff ℝ 2 (lastFunction n a sigma x) := contDiff_const.mul hn
  apply strongConvex_of_hessian_lower _ mu hf
  intro s v
  change mu * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun s : E => sigma / 2 * ‖s - center‖ ^ 2)) s v v
  rw [hessian_const_mul _ hn (sigma / 2), norm_sub_sq_hessian, real_inner_self_eq_norm_sq]
  have hh := mul_le_mul_of_nonneg_right hmu (sq_nonneg ‖v‖)
  nlinarith only [hh]

/- This is the actual full dual strong-convexity conclusion, conditional
   only on the explicit local packet/gate budgets and scalar margins.
   No actual Hessian or coupled-block conclusion is a premise. -/
theorem actual_dual_strongConvex (n : ℕ) (β lam a sigma reward d mu M Hbound Pbound Gbound : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x : Fin (n + 1) → E)
    (h0c : ∀ t, ContDiff ℝ 2 (h0 t)) (h1c : ∀ t, ContDiff ℝ 2 (h1 t))
    (hgc : ∀ j, ContDiff ℝ 2 (gate j))
    (h0sc : ∀ t, StrongConvexOn (Set.univ : Set E) d (h0 t))
    (h1sc : ∀ t, StrongConvexOn (Set.univ : Set E) d (h1 t))
    (hrange : ∀ j s, 0 ≤ gate j s ∧ gate j s ≤ 1)
    (hM : 0 ≤ M) (hHbound : 0 ≤ Hbound) (hP : 0 ≤ Pbound) (hG : 0 ≤ Gbound)
    (hB : ∀ (j : Fin n) y, |delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) y - reward| ≤ M)
    (hGateH : ∀ j s v, |fderiv ℝ (fderiv ℝ (gate j)) s v v| ≤ Hbound * ‖v‖ ^ 2)
    (hGateG : ∀ j s v, |fderiv ℝ (gate j) s v| ≤ Pbound * ‖v‖)
    (hDeltaG : ∀ (j : Fin n) y v,
      |fderiv ℝ (delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ)) y v| ≤ Gbound * ‖v‖)
    (hsigma : 0 < sigma) (hmu0 : 0 ≤ mu) (hmu : 4 * mu ≤ sigma)
    (hpure : M * Hbound ≤ sigma / 2)
    (hschur : mu + 4 * Pbound ^ 2 * Gbound ^ 2 / sigma ≤ d) :
    StrongConvexOn (Set.univ : Set (Dual n E)) mu
      (negativeFamily n β lam a sigma reward h0 h1 m0 m1 gate x) := by
  have hdm : mu ≤ d := (le_add_of_nonneg_right (by positivity)).trans hschur
  have hsm : mu ≤ sigma := by linarith only [hmu0, hmu]
  apply dual_strongConvex_from_components n β lam a sigma reward mu h0 h1 m0 m1 gate x
  · exact first_strongConvex n β lam d mu h1 m1 x (h1c 0) (h1sc 0) hdm
  · exact last_strongConvex n a sigma mu x hsm
  · intro j
    exact negativePair_strongConvex (h0 j.succ) (h1 j.succ) (gate j) lam
      (-β / 2 * ‖x j.succ‖ ^ 2 - m0 j.succ) (m0 j.succ) (m1 j.succ) reward sigma
      d mu M Hbound Pbound Gbound (x j.succ) (a • x j.castSucc)
      (h0c j.succ) (h1c j.succ) (hgc j) (h0sc j.succ) (h1sc j.succ) (hrange j)
      hM hHbound hP hG (hB j) (hGateH j) (hGateG j) (hDeltaG j) hsigma hmu hpure hschur

end
end FangqingRelayDualAssembly
end

section
-- Source component: ActualSeedRelayFamily.lean

open scoped ContDiff

namespace FangqingActualSeedRelayFamily

open FangqingRelayAnalyticAssembly FangqingRelayGlobalJointClass FangqingRelayFenchelInterfaces
  FangqingFenchelEndpointClass FangqingActualInactivePacket FangqingRelayStationarity
  FangqingLocalizedSeedJets FangqingActualRelayLink FangqingPublicShellProfiles
  FangqingRadialGateBounds FangqingGateBudgetBridge

noncomputable section

set_option maxHeartbeats 4000000

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_packet_endpoint_jets (H : E → ℝ) (beta c lam m nu LH rhoH : ℝ)
    (hb : 0 ≤ beta) (hc : 0 ≤ c) (hLH : 0 ≤ LH) (hrho : 0 ≤ rhoH)
    (hH : AnalyticClass H nu LH rhoH) :
    let F : FangqingRelayBlockGeometry.Pair E → ℝ := fun p => endpoint beta lam (reduced H c) m p.fst p.snd
    ContDiff ℝ 2 F ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ beta + c + 2 * |lam| + LH) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ rhoH * ‖x - y‖) := by
  intro F
  have heq : F = jointEndpoint H beta c lam m := by
    funext p
    exact endpoint_from_H H beta c lam m p
  rw [heq]
  obtain ⟨hF, hSC, hgrad, hhess⟩ := actual_joint_endpoint_class H beta c lam m nu LH rhoH
    hb hc hLH hrho hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
  exact ⟨hF, second_jet_bound_from_gradient_rate _ _ (by positivity) hgrad, hhess⟩

theorem actual_seed_relay_joint_and_dual_class (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∃ Kg : ℝ, 0 ≤ Kg ∧ ∃ Kh : ℝ, 0 ≤ Kh ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (n : ℕ) (beta c lam a sigma reward nu mu LH rhoH Rp A amp D Rg : ℝ)
      (H0 H1 : Fin (n + 1) → F → ℝ) (z0 z1 handle : Fin (n + 1) → F) (center : Fin n → F),
      0 ≤ beta → 0 ≤ c → 0 ≤ LH → 0 ≤ rhoH → 0 ≤ reward → 0 < D → D ≤ Rp → D ≤ A →
      0 ≤ amp → 0 < Rg → 0 < sigma → 0 ≤ mu →
      (∀ t, AnalyticClass (H0 t) nu LH rhoH) → (∀ t, AnalyticClass (H1 t) nu LH rhoH) →
      (∀ t, ‖handle t‖ ≤ 1) →
      (∀ t y, H1 t y = H0 t y - localizedSeed theta phi Rp A amp (handle t) y) →
      (∀ t y, H0 t (z0 t) ≤ H0 t y) → (∀ t y, H1 t (z1 t) ≤ H1 t y) →
      4 * mu ≤ sigma → (Kd * amp + reward) * (Kh / Rg ^ 2) ≤ sigma / 2 →
      mu + 4 * (Kh / Rg) ^ 2 * (Kd * amp / D) ^ 2 / sigma ≤ nu - c →
      let h0 := fun t => reduced (H0 t) c
      let h1 := fun t => reduced (H1 t) c
      let m0 := fun t => H0 t (z0 t)
      let m1 := fun t => H1 t (z1 t)
      let gate := fun j => scaledGate theta Rg (center j)
      let Ll := Kd * amp / D ^ 2 + 2 * (Kg / Rg) * (Kd * amp / D) + (Kg / Rg ^ 2) * (Kd * amp + reward)
      let Rl := Kd * amp / D ^ 3 + 3 * (Kg / Rg) * (Kd * amp / D ^ 2) +
        3 * (Kg / Rg ^ 2) * (Kd * amp / D) + (Kg / Rg ^ 3) * (Kd * amp + reward)
      let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
      ContDiff ℝ 2 J ∧
      (∀ x y, ‖gradient J x - gradient J y‖ ≤
        (beta + c + 2 * |lam| + LH + sigma * (1 + a ^ 2) + Ll) * ‖x - y‖) ∧
      FangqingRelayGlobalJointClass.HessianRate J (rhoH + Rl) ∧
      (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n F)) mu
        (FangqingRelayDualAssembly.negativeFamily n beta lam a sigma reward h0 h1 m0 m1 gate x)) := by
  obtain ⟨Kd, hKd, Kg, hKg, hLink⟩ := actual_normalized_gate_link.{u} phi B left right hp hl hr
  have ht : ContDiff ℝ 3 theta := theta_smooth.of_le (by decide)
  obtain ⟨Kh, hKh, hGscalar⟩ := universal_gate_scalar_budgets.{u} theta (7 / 4) (by norm_num) ht
    (fun t ht => theta_one t (by linarith only [ht])) (fun t ht => theta_zero t (by nlinarith only [ht]))
  refine ⟨Kd, hKd, Kg, hKg, Kh, hKh, ?_⟩
  intro F inst inst' inst'' n beta c lam a sigma reward nu mu LH rhoH Rp A amp D Rg
    H0 H1 z0 z1 handle center hb hc hLH hrho hrw hD hRp hA hamp hRg hsigma hmu hH0 hH1
    hh hrel hm0 hm1 hsigmamu hpure hschur h0 h1 m0 m1 gate Ll Rl J
  have hLocal : ∀ t,
      ContDiff ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) z‖ ≤ beta + c + 2 * |lam| + LH) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) x -
        iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) y‖ ≤ rhoH * ‖x - y‖) := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · exact actual_packet_endpoint_jets (H1 0) beta c lam (m1 0) nu LH rhoH hb hc hLH hrho (hH1 0)
    · exact actual_packet_endpoint_jets (H0 j.succ) beta c lam (m0 j.succ) nu LH rhoH hb hc hLH hrho (hH0 j.succ)
  have hLinks := fun j : Fin n => hLink F Rp A amp D Rg c reward (handle j.succ) (center j)
    (H0 j.succ) (H1 j.succ) (z0 j.succ) (z1 j.succ) hD hRp hA hamp (hh j.succ)
    hRg hrw (hrel j.succ) (hm0 j.succ) (hm1 j.succ)
  have hLl : 0 ≤ Ll := by dsimp [Ll]; positivity
  have hRl : 0 ≤ Rl := by dsimp [Rl]; positivity
  obtain ⟨hJ, hJgrad, hJhess, hJ2, hJ2lip⟩ := actual_assembled_joint_class n beta lam a sigma reward
    h0 h1 m0 m1 gate (beta + c + 2 * |lam| + LH) rhoH Ll Rl hsigma.le (by positivity) hrho hLl hRl
    (fun t => (hLocal t).1) (fun t => (hLocal t).2.1) (fun t => (hLocal t).2.2)
    (fun j => (hLinks j).2.2.2.2.2.1) (fun j => (hLinks j).2.2.2.2.2.2.1)
    (fun j => (hLinks j).2.2.2.2.2.2.2)
  refine ⟨hJ, hJgrad, hJhess, ?_⟩
  intro x
  apply FangqingRelayDualAssembly.actual_dual_strongConvex n beta lam a sigma reward (nu - c) mu
    (Kd * amp + reward) (Kh / Rg ^ 2) (Kh / Rg) (Kd * amp / D) h0 h1 m0 m1 gate x
  · intro t
    exact ((hH0 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · intro t
    exact ((hH1 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · intro j
    exact (hGscalar F Rg hRg (center j)).1.of_le (by norm_num)
  · intro t
    exact reduced_strongConvex (H0 t) nu c (hH0 t).2.1
  · intro t
    exact reduced_strongConvex (H1 t) nu c (hH1 t).2.1
  · intro j y
    exact (hLinks j).2.1 y
  · positivity
  · positivity
  · positivity
  · positivity
  · intro j y
    exact (abs_sub _ _).trans (by
      simpa only [abs_of_nonneg hrw] using add_le_add ((hLinks j).2.2.2.1 y) (le_refl |reward|))
  · intro j s v
    exact (hGscalar F Rg hRg (center j)).2.2 s v
  · intro j s v
    exact (hGscalar F Rg hRg (center j)).2.1 s v
  · intro j y v
    apply first_scalar_bound _ (Kd * amp / D) y v
    simpa only [pow_one] using (hLinks j).2.2.2.2.1 1 (by norm_num) (by norm_num) y
  · exact hsigma
  · exact hmu
  · exact hsigmamu
  · exact hpure
  · exact hschur

end
end FangqingActualSeedRelayFamily
end

section
-- Source component: ActualRelayScaling.lean

namespace FangqingActualRelayScaling

noncomputable section

def lam (L mu : ℝ) : ℝ := Real.sqrt (L * mu)
def packetD (L mu KD eps : ℝ) : ℝ := KD * eps * Real.sqrt (L / mu) / L
def width (L mu KD eps : ℝ) : ℝ := lam L mu * packetD L mu KD eps / L
def energy (L eps : ℝ) : ℝ := eps ^ 2 / L
def rawBudget (C N L mu KD eps : ℝ) : ℝ := C * (N * mu) * packetD L mu KD eps ^ 2
def rewardCoefficient (C N KD : ℝ) : ℝ := 2 * C * N * KD ^ 2 + 1
def reward (C N L KD eps : ℝ) : ℝ := rewardCoefficient C N KD * energy L eps
def totalBudget (C N L mu KD eps : ℝ) : ℝ := rawBudget C N L mu KD eps + reward C N L KD eps
def sigma (L a csigma : ℝ) : ℝ := csigma * L / a ^ 2

theorem lam_sqrt_kappa (L mu : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    lam L mu * Real.sqrt (L / mu) = L := by
  have hh : L * mu * (L / mu) = L ^ 2 := by field_simp <;> ring
  dsimp [lam]
  rw [← Real.sqrt_mul (by positivity : 0 ≤ L * mu), hh, Real.sqrt_sq hL.le]

theorem width_eq_actual (L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    width L mu KD eps = KD * eps / L := by
  have hh := lam_sqrt_kappa L mu hL hmu
  dsimp [width, packetD]
  calc
    _ = KD * eps / L * (lam L mu * Real.sqrt (L / mu) / L) := by field_simp <;> ring
    _ = _ := by rw [hh, div_self hL.ne', mul_one]

theorem rawBudget_eq (C N L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    rawBudget C N L mu KD eps = C * N * KD ^ 2 * energy L eps := by
  dsimp [rawBudget, packetD, energy]
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : 0 ≤ L / mu)]
  field_simp
  <;> ring

theorem reward_eq_two_raw_plus_energy (C N L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    reward C N L KD eps = 2 * rawBudget C N L mu KD eps + energy L eps := by
  rw [rawBudget_eq C N L mu KD eps hL hmu]
  dsimp [reward, rewardCoefficient]
  ring

theorem totalBudget_eq (C N L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    totalBudget C N L mu KD eps = (3 * C * N * KD ^ 2 + 1) * energy L eps := by
  rw [totalBudget, reward_eq_two_raw_plus_energy C N L mu KD eps hL hmu,
    rawBudget_eq C N L mu KD eps hL hmu]
  ring

theorem actual_coefficient_interval (C N L mu KD eps delta : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hdelta : |delta| ≤ rawBudget C N L mu KD eps) :
    -totalBudget C N L mu KD eps ≤ delta - reward C N L KD eps ∧
      delta - reward C N L KD eps ≤ -energy L eps := by
  have hd := abs_le.mp hdelta
  have hraw : 0 ≤ rawBudget C N L mu KD eps := by unfold rawBudget; positivity
  rw [reward_eq_two_raw_plus_energy C N L mu KD eps hL hmu]
  unfold totalBudget
  rw [reward_eq_two_raw_plus_energy C N L mu KD eps hL hmu]
  constructor <;> linarith only [hd.1, hd.2, hraw]

/- The actual endpoint-difference coefficient has its KD^2 dependence.
   Cancelling that dependence against ell^2 proves the pure-gate budget. -/
theorem actual_pure_gate_margin (C N KH L mu KD eps a csigma : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hKD : 1 ≤ KD) (heps : 0 < eps) (ha : 0 < a)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hKH : 0 ≤ KH)
    (hreserve : 2 * KH * (3 * C * N + 1) ≤ csigma) :
    totalBudget C N L mu KD eps * (KH / (a ^ 2 * width L mu KD eps ^ 2)) ≤
      sigma L a csigma / 2 := by
  have hKDsquare : 1 ≤ KD ^ 2 := by nlinarith [sq_nonneg (KD - 1)]
  have hmain := mul_le_mul_of_nonneg_right hreserve (sq_nonneg KD)
  have hextra := mul_le_mul_of_nonneg_left hKDsquare (by positivity : 0 ≤ 2 * KH)
  have hconst : 2 * KH * (3 * C * N * KD ^ 2 + 1) ≤ csigma * KD ^ 2 := by
    nlinarith only [hmain, hextra]
  have hm := mul_le_mul_of_nonneg_left hconst
    (by positivity : 0 ≤ L / (2 * a ^ 2 * KD ^ 2))
  rw [totalBudget_eq C N L mu KD eps hL hmu, width_eq_actual L mu KD eps hL hmu]
  dsimp [energy, sigma]
  have hKDpos : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  convert! hm using 1 <;> field_simp <;> ring

/- The actual first-derivative seed scale is CG*nu*D with nu=N*mu.
   The full Schur term cancels D and a, leaving a universal coefficient. -/
theorem actual_schur_identity (KP CG N L mu KD eps a csigma : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hKD : 0 < KD) (heps : 0 < eps)
    (ha : 0 < a) (hcsigma : 0 < csigma) :
    4 * (KP / (a * width L mu KD eps)) ^ 2 *
        (CG * (N * mu) * packetD L mu KD eps) ^ 2 / sigma L a csigma =
      (4 * KP ^ 2 * CG ^ 2 * N ^ 2 / csigma) * mu := by
  rw [width_eq_actual L mu KD eps hL hmu]
  dsimp [packetD, sigma]
  simp only [mul_pow, div_pow, Real.sq_sqrt (by positivity : 0 ≤ L / mu)]
  field_simp
  <;> ring

theorem actual_schur_margin (KP CG N L mu KD eps a csigma : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hKD : 0 < KD) (heps : 0 < eps)
    (ha : 0 < a) (hcsigma : 0 < csigma)
    (hreserve : 4 * KP ^ 2 * CG ^ 2 * N ^ 2 ≤ csigma) :
    mu + 4 * (KP / (a * width L mu KD eps)) ^ 2 *
        (CG * (N * mu) * packetD L mu KD eps) ^ 2 / sigma L a csigma ≤ 2 * mu := by
  rw [actual_schur_identity KP CG N L mu KD eps a csigma hL hmu hKD heps ha hcsigma]
  have hh : 4 * KP ^ 2 * CG ^ 2 * N ^ 2 / csigma ≤ 1 := (div_le_one hcsigma).mpr hreserve
  have hm := mul_le_mul_of_nonneg_right hh hmu.le
  nlinarith only [hm]

theorem actual_sigma_lower (L mu a A csigma : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (ha : 0 < a)
    (haUpper : a ^ 2 ≤ A * (L / mu)) (hreserve : 4 * A ≤ csigma) :
    4 * mu ≤ sigma L a csigma := by
  unfold sigma
  apply (le_div_iff₀ (sq_pos_of_pos ha)).mpr
  have hm := mul_le_mul_of_nonneg_left haUpper (by positivity : 0 ≤ 4 * mu)
  have heq : 4 * mu * (A * (L / mu)) = 4 * A * L := by field_simp <;> ring
  rw [heq] at hm
  have hc := mul_le_mul_of_nonneg_right hreserve hL.le
  nlinarith only [hm, hc]

theorem actual_quadratic_budget (L a csigma : ℝ) (hL : 0 ≤ L) (hc : 0 ≤ csigma) (ha : 1 ≤ a) :
    sigma L a csigma * (1 + a ^ 2) ≤ 2 * csigma * L := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha2 : 1 ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 1)]
  unfold sigma
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (sq_pos_of_pos ha0)).mpr
  have hm := mul_le_mul_of_nonneg_left ha2 (mul_nonneg hc hL)
  nlinarith only [hm]

theorem external_quadratic_reserved_budget (Lext cL csigma a : ℝ)
    (hL : 0 ≤ Lext) (hcL : 0 ≤ cL) (hc : 0 ≤ csigma) (ha : 1 ≤ a)
    (hreserve : 16 * csigma * cL ≤ 1) :
    sigma (cL * Lext) a csigma * (1 + a ^ 2) ≤ Lext / 8 := by
  have hh := actual_quadratic_budget (cL * Lext) a csigma (mul_nonneg hcL hL) hc ha
  have hm := mul_le_mul_of_nonneg_right hreserve hL
  nlinarith only [hh, hm]


theorem actual_stationarity_width_margins (L mu KD eps radius b0 : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 ≤ eps)
    (hradius : 2 ≤ KD * radius) (hclose : 1 ≤ KD * b0) :
    2 * eps ≤ L * width L mu KD eps * radius ∧
      eps ≤ L * b0 * width L mu KD eps := by
  rw [width_eq_actual L mu KD eps hL hmu]
  have hw := mul_le_mul_of_nonneg_right hradius heps
  have hc := mul_le_mul_of_nonneg_right hclose heps
  have hwEq : L * (KD * eps / L) * radius = KD * radius * eps := by field_simp <;> ring
  have hcEq : L * b0 * (KD * eps / L) = KD * b0 * eps := by field_simp <;> ring
  constructor
  · rw [hwEq]
    exact hw
  · rw [hcEq]
    simpa only [one_mul] using hc

/- Explicit simultaneous universal choices.  K0 is the closed profile
   expression rewardCoefficient C N KD, retaining its real KD^2 scale.
   Later enlarging a reserved profile lower bound changes KD, K0 and the
   chosen constants together, never treats them as independent. -/
theorem universal_scalar_choices (C N KH KP CG A radius b0 KDlower : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hKH : 0 ≤ KH) (hA : 0 ≤ A)
    (hradius : 0 < radius) (hb0 : 0 < b0) (hKDlower : 0 ≤ KDlower) :
    ∃ KD csigma : ℝ, 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧
      2 ≤ KD * radius ∧ 1 ≤ KD * b0 ∧
      2 * KH * (3 * C * N + 1) ≤ csigma ∧
      4 * KP ^ 2 * CG ^ 2 * N ^ 2 ≤ csigma ∧ 4 * A ≤ csigma := by
  let KD := 1 + 2 / radius + 1 / b0 + KDlower
  let csigma := 1 + 2 * KH * (3 * C * N + 1) + 4 * KP ^ 2 * CG ^ 2 * N ^ 2 + 4 * A
  have hradterm : 0 ≤ 2 / radius := by positivity
  have hbterm : 0 ≤ 1 / b0 := by positivity
  have hpure : 0 ≤ 2 * KH * (3 * C * N + 1) := by positivity
  have hcross : 0 ≤ 4 * KP ^ 2 * CG ^ 2 * N ^ 2 := by positivity
  have hAmul : 0 ≤ 4 * A := by positivity
  refine ⟨KD, csigma, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [KD]
    linarith only [hradterm, hbterm, hKDlower]
  · dsimp [KD]
    linarith only [hradterm, hbterm]
  · dsimp [csigma]
    linarith only [hpure, hcross, hAmul]
  · have hfrac : 2 / radius ≤ KD := by dsimp [KD]; linarith only [hbterm, hKDlower]
    have hm := mul_le_mul_of_nonneg_right hfrac hradius.le
    rw [div_mul_cancel₀ _ hradius.ne'] at hm
    exact hm
  · have hfrac : 1 / b0 ≤ KD := by dsimp [KD]; linarith only [hradterm, hKDlower]
    have hm := mul_le_mul_of_nonneg_right hfrac hb0.le
    rw [div_mul_cancel₀ _ hb0.ne'] at hm
    exact hm
  · dsimp [csigma]
    linarith only [hcross, hAmul]
  · dsimp [csigma]
    linarith only [hpure, hAmul]
  · dsimp [csigma]
    linarith only [hpure, hcross]

theorem external_fraction_choice (csigma : ℝ) (hcsigma : 0 < csigma) :
    0 < (1 / (32 * csigma) : ℝ) ∧ 16 * csigma * (1 / (32 * csigma)) ≤ 1 := by
  constructor
  · positivity
  · have heq : 16 * csigma * (1 / (32 * csigma)) = (1 / 2 : ℝ) := by field_simp <;> ring
    rw [heq]
    norm_num


def relayAmplitude (Ca kappa r : ℝ) : ℝ :=
  Ca * max 1 ((kappa ^ (3 / 2 : ℝ) / r) ^ (1 / 3 : ℝ))

theorem kappa_three_halves (kappa : ℝ) (hk : 0 < kappa) :
    kappa ^ (3 / 2 : ℝ) = kappa * Real.sqrt kappa := by
  rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num, Real.rpow_add_one hk.ne',
    ← Real.sqrt_eq_rpow]
  ring

theorem relayAmplitude_bounds (Ca kappa r : ℝ) (hCa : 0 < Ca) (hk : 1 ≤ kappa) (hr : 1 ≤ r) :
    Ca ≤ relayAmplitude Ca kappa r ∧
      relayAmplitude Ca kappa r ≤ Ca * Real.sqrt kappa ∧
      Ca ^ 3 * kappa * Real.sqrt kappa ≤ relayAmplitude Ca kappa r ^ 3 * r := by
  have hk0 : 0 < kappa := lt_of_lt_of_le zero_lt_one hk
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hbase : 0 ≤ kappa ^ (3 / 2 : ℝ) / r := by positivity
  have hfrac : kappa ^ (3 / 2 : ℝ) / r ≤ kappa ^ (3 / 2 : ℝ) :=
    div_le_self (by positivity) hr
  have hroot := Real.rpow_le_rpow hbase hfrac (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have hroot_eq : (kappa ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) = Real.sqrt kappa := by
    rw [← Real.rpow_mul hk0.le]
    norm_num
    exact (Real.sqrt_eq_rpow kappa).symm
  rw [hroot_eq] at hroot
  have hmax : max 1 ((kappa ^ (3 / 2 : ℝ) / r) ^ (1 / 3 : ℝ)) ≤ Real.sqrt kappa :=
    max_le (by simpa using Real.sqrt_le_sqrt hk) hroot
  refine ⟨?_, ?_, ?_⟩
  · simpa only [relayAmplitude, mul_one] using
      (mul_le_mul_of_nonneg_left (le_max_left (1 : ℝ) ((kappa ^ (3 / 2 : ℝ) / r) ^ (1 / 3 : ℝ))) hCa.le)
  · exact mul_le_mul_of_nonneg_left hmax hCa.le
  · have hcube : ((kappa ^ (3 / 2 : ℝ) / r) ^ (1 / 3 : ℝ)) ^ 3 = kappa ^ (3 / 2 : ℝ) / r := by
      rw [← Real.rpow_mul_natCast hbase]
      norm_num
    have hmono := pow_le_pow_left₀ (Real.rpow_nonneg hbase (1 / 3 : ℝ))
      (le_max_right (1 : ℝ) ((kappa ^ (3 / 2 : ℝ) / r) ^ (1 / 3 : ℝ))) 3
    rw [hcube] at hmono
    have hm := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ Ca ^ 3)
    have hmr := mul_le_mul_of_nonneg_right hm hr0.le
    rw [mul_assoc, div_mul_cancel₀ _ hr0.ne', kappa_three_halves kappa hk0] at hmr
    dsimp [relayAmplitude]
    rw [mul_pow, kappa_three_halves kappa hk0]
    nlinarith only [hmr]

theorem relayAmplitude_ratio_budgets (Ca kappa r : ℝ) (hCa : 0 < Ca) (hk : 1 ≤ kappa) (hr : 1 ≤ r) :
    let a := relayAmplitude Ca kappa r
    kappa * Real.sqrt kappa / (a ^ 3 * r) ≤ 1 / Ca ^ 3 ∧
      kappa / (a ^ 2 * r) ≤ 1 / Ca ^ 2 ∧
      Real.sqrt kappa / (a * r) ≤ 1 / Ca ∧ 1 / r ≤ 1 := by
  let a := relayAmplitude Ca kappa r
  have hh := relayAmplitude_bounds Ca kappa r hCa hk hr
  have ha : 0 < a := hCa.trans_le hh.1
  have hk0 : 0 < kappa := lt_of_lt_of_le zero_lt_one hk
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs : 0 < Real.sqrt kappa := Real.sqrt_pos.mpr hk0
  have hsecond : Ca ^ 2 * kappa ≤ a ^ 2 * r := by
    have hm := mul_le_mul_of_nonneg_right hh.2.1 (by positivity : 0 ≤ a ^ 2 * r)
    have hc : (Ca * Real.sqrt kappa) * (Ca ^ 2 * kappa) ≤
        (Ca * Real.sqrt kappa) * (a ^ 2 * r) := by
      nlinarith only [hm, hh.2.2]
    exact (mul_le_mul_iff_right₀ (mul_pos hCa hs)).mp hc
  have hathird : Ca * Real.sqrt kappa ≤ a * r := by
    have ha2 : a ^ 2 ≤ Ca ^ 2 * kappa := by
      have hm := sq_le_sq₀ ha.le (mul_pos hCa hs).le |>.mpr hh.2.1
      rw [mul_pow, Real.sq_sqrt hk0.le] at hm
      exact hm
    have hm := mul_le_mul_of_nonneg_right ha2 (by positivity : 0 ≤ a * r)
    have hc : (Ca ^ 2 * kappa) * (Ca * Real.sqrt kappa) ≤
        (Ca ^ 2 * kappa) * (a * r) := by nlinarith only [hm, hh.2.2]
    exact (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos hCa) hk0)).mp hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity : 0 < a ^ 3 * r) (pow_pos hCa 3)).mpr
    nlinarith only [hh.2.2]
  · apply (div_le_div_iff₀ (by positivity : 0 < a ^ 2 * r) (pow_pos hCa 2)).mpr
    simpa only [one_mul, mul_one, mul_comm] using hsecond
  · apply (div_le_div_iff₀ (mul_pos ha hr0) hCa).mpr
    nlinarith only [hathird]
  · simpa only [one_div_one] using (one_div_le_one_div_of_le zero_lt_one hr)


theorem actual_amplitude_sigma_lower (Ca L mu r csigma : ℝ)
    (hCa : 1 ≤ Ca) (hmu : 0 < mu) (hLmu : mu ≤ L) (hr : 1 ≤ r)
    (hreserve : 4 * Ca ^ 2 ≤ csigma) :
    let a := relayAmplitude Ca (L / mu) r
    1 ≤ a ∧ sigma L a csigma ≥ 4 * mu := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hCa0 : 0 < Ca := lt_of_lt_of_le zero_lt_one hCa
  have hk : 1 ≤ L / mu := (one_le_div hmu).mpr hLmu
  have hh := relayAmplitude_bounds Ca (L / mu) r hCa0 hk hr
  have ha : 0 < relayAmplitude Ca (L / mu) r := hCa0.trans_le hh.1
  have hupper : relayAmplitude Ca (L / mu) r ^ 2 ≤ Ca ^ 2 * (L / mu) := by
    have hs := sq_le_sq₀ ha.le (by positivity : 0 ≤ Ca * Real.sqrt (L / mu)) |>.mpr hh.2.1
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ L / mu)] at hs
    exact hs
  exact ⟨hCa.trans hh.1, actual_sigma_lower L mu _ (Ca ^ 2) csigma hL hmu ha hupper hreserve⟩

end
end FangqingActualRelayScaling
end

section
-- Source component: ThirdGroupScaling.lean

namespace FangqingThirdGroupScaling

open FangqingActualRelayScaling

noncomputable section

def rho (L mu eps r : ℝ) : ℝ := r * L ^ 2 / ((L / mu) * Real.sqrt (L / mu) * eps)
def group1 (N L mu KD eps a : ℝ) : ℝ := N * mu * packetD L mu KD eps ^ 2 / (a ^ 3 * width L mu KD eps ^ 3)
def group2 (N L mu KD eps a : ℝ) : ℝ := N * mu * packetD L mu KD eps / (a ^ 2 * width L mu KD eps ^ 2)
def group3 (N L mu KD eps a : ℝ) : ℝ := N * mu / (a * width L mu KD eps)
def group4 (N L mu KD eps : ℝ) : ℝ := N * mu / packetD L mu KD eps

theorem actual_third_group_ratio_identities (N L mu KD eps a r : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hKD : 0 < KD) (heps : 0 < eps) (ha : 0 < a) (hr : 0 < r) :
    group1 N L mu KD eps a / rho L mu eps r =
      N / KD * ((L / mu) * Real.sqrt (L / mu) / (a ^ 3 * r)) ∧
    group2 N L mu KD eps a / rho L mu eps r = N / KD * ((L / mu) / (a ^ 2 * r)) ∧
    group3 N L mu KD eps a / rho L mu eps r = N / KD * (Real.sqrt (L / mu) / (a * r)) ∧
    group4 N L mu KD eps / rho L mu eps r = N / KD * (1 / r) := by
  have hk : 0 < L / mu := div_pos hL hmu
  have hs : 0 < Real.sqrt (L / mu) := Real.sqrt_pos.mpr hk
  have hsne : Real.sqrt (L / mu) ≠ 0 := hs.ne'
  have hsq := Real.sq_sqrt hk.le
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    try rw [width_eq_actual L mu KD eps hL hmu]
    dsimp [group1, group2, group3, group4, rho, packetD]
    try rw [width_eq_actual L mu KD eps hL hmu]
    try simp only [mul_pow, div_pow, hsq]
    field_simp
    <;> ring_nf
    <;> (try rw [hsq])
    <;> (try rw [Real.sq_sqrt (by positivity : 0 ≤ L * mu⁻¹)])
    <;> (try field_simp)
    <;> ring

theorem actual_third_group_reserved_budget (K N Ca L mu KD eps r : ℝ)
    (hK : 0 ≤ K) (hN : 0 ≤ N) (hCa : 1 ≤ Ca) (hmu : 0 < mu) (hLmu : mu ≤ L)
    (hKD : 0 < KD) (heps : 0 < eps) (hr : 1 ≤ r) (hreserve : 16 * K * N ≤ KD) :
    let a := relayAmplitude Ca (L / mu) r
    K * (group1 N L mu KD eps a + group2 N L mu KD eps a +
      group3 N L mu KD eps a + group4 N L mu KD eps) ≤ rho L mu eps r / 4 := by
  let a := relayAmplitude Ca (L / mu) r
  have hL : 0 < L := hmu.trans_le hLmu
  have hk : 1 ≤ L / mu := (one_le_div hmu).mpr hLmu
  have hCa0 : 0 < Ca := lt_of_lt_of_le zero_lt_one hCa
  have ha : 0 < a := hCa0.trans_le (relayAmplitude_bounds Ca (L / mu) r hCa0 hk hr).1
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hratio := actual_third_group_ratio_identities N L mu KD eps a r hL hmu hKD heps ha hr0
  have haRatios := relayAmplitude_ratio_budgets Ca (L / mu) r hCa0 hk hr
  have hCa2 : 1 ≤ Ca ^ 2 := by nlinarith [sq_nonneg (Ca - 1)]
  have hCa3 : 1 ≤ Ca ^ 3 := one_le_pow₀ hCa
  have hinv2 : 1 / Ca ^ 2 ≤ 1 := by simpa using (one_div_le_one_div_of_le zero_lt_one hCa2)
  have hinv3 : 1 / Ca ^ 3 ≤ 1 := by simpa using (one_div_le_one_div_of_le zero_lt_one hCa3)
  have hinv1 : 1 / Ca ≤ 1 := by simpa using (one_div_le_one_div_of_le zero_lt_one hCa)
  have hρ : 0 < rho L mu eps r := by unfold rho; positivity
  have hNdiv : 0 ≤ N / KD := div_nonneg hN hKD.le
  have hg1 : group1 N L mu KD eps a ≤ N / KD * rho L mu eps r := by
    apply (div_le_iff₀ hρ).mp
    rw [hratio.1]
    have hm := mul_le_mul_of_nonneg_left (haRatios.1.trans hinv3) hNdiv
    simpa only [mul_one] using hm
  have hg2 : group2 N L mu KD eps a ≤ N / KD * rho L mu eps r := by
    apply (div_le_iff₀ hρ).mp
    rw [hratio.2.1]
    have hm := mul_le_mul_of_nonneg_left (haRatios.2.1.trans hinv2) hNdiv
    simpa only [mul_one] using hm
  have hg3 : group3 N L mu KD eps a ≤ N / KD * rho L mu eps r := by
    apply (div_le_iff₀ hρ).mp
    rw [hratio.2.2.1]
    have hm := mul_le_mul_of_nonneg_left (haRatios.2.2.1.trans hinv1) hNdiv
    simpa only [mul_one] using hm
  have hg4 : group4 N L mu KD eps ≤ N / KD * rho L mu eps r := by
    apply (div_le_iff₀ hρ).mp
    rw [hratio.2.2.2]
    have hm := mul_le_mul_of_nonneg_left haRatios.2.2.2 hNdiv
    simpa only [mul_one] using hm
  have hsum : K * (group1 N L mu KD eps a + group2 N L mu KD eps a +
      group3 N L mu KD eps a + group4 N L mu KD eps) ≤
      4 * K * N / KD * rho L mu eps r := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hg1 hg2) hg3) hg4) hK
    convert! hh using 1 <;> ring
  have hfrac : 4 * K * N / KD ≤ 1 / 4 := by
    apply (div_le_iff₀ hKD).mpr
    nlinarith only [hreserve]
  have hm := mul_le_mul_of_nonneg_right hfrac hρ.le
  nlinarith only [hsum, hm]

end
end FangqingThirdGroupScaling
end

section
-- Source component: ActualRelayLinkBudgets.lean

namespace FangqingActualRelayLinkBudgets

open FangqingActualRelayScaling FangqingThirdGroupScaling

noncomputable section

set_option maxHeartbeats 2000000

def secondBudget (C N K L mu KD eps a : ℝ) : ℝ :=
  let D := packetD L mu KD eps
  let ell := width L mu KD eps
  C * (N * mu) * D ^ 2 / D ^ 2 + 2 * (K / (a * ell)) * (C * (N * mu) * D ^ 2 / D) +
    (K / (a * ell) ^ 2) * totalBudget C N L mu KD eps

def thirdBudget (C N K L mu KD eps a : ℝ) : ℝ :=
  let D := packetD L mu KD eps
  let ell := width L mu KD eps
  C * (N * mu) * D ^ 2 / D ^ 3 + 3 * (K / (a * ell)) * (C * (N * mu) * D ^ 2 / D ^ 2) +
    3 * (K / (a * ell) ^ 2) * (C * (N * mu) * D ^ 2 / D) +
    (K / (a * ell) ^ 3) * totalBudget C N L mu KD eps

theorem actual_mu_distance_over_relay_width (L mu KD eps a : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hKD : 0 < KD) (heps : 0 < eps) (ha : 1 ≤ a) :
    mu * packetD L mu KD eps / (a * width L mu KD eps) ≤ L := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hD : 0 < packetD L mu KD eps := by unfold packetD; positivity
  have he : 0 < width L mu KD eps := by rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  have hlam0 : 0 ≤ lam L mu := Real.sqrt_nonneg _
  have hlam2 : lam L mu ^ 2 = L * mu := Real.sq_sqrt (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hLmu hmu.le
  have hmulam : mu ≤ lam L mu := by nlinarith only [hlam0, hlam2, hmul]
  have hnum := mul_le_mul_of_nonneg_right hmulam hD.le
  have hidentity : lam L mu * packetD L mu KD eps = L * width L mu KD eps := by
    unfold width
    field_simp
  rw [hidentity] at hnum
  have had := mul_le_mul_of_nonneg_left ha (mul_nonneg hL.le he.le)
  apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le zero_lt_one ha) he)).mpr
  nlinarith only [hnum, had]

theorem actual_link_second_budget (C N K L mu KD eps a csigma : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K) (hmu : 0 < mu) (hLmu : mu ≤ L)
    (hKD : 1 ≤ KD) (heps : 0 < eps) (ha : 1 ≤ a)
    (hreserve : 2 * K * (3 * C * N + 1) ≤ csigma) :
    secondBudget C N K L mu KD eps a ≤ (C * N * (1 + 2 * K) + csigma / 2) * L := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hD : 0 < packetD L mu KD eps := by unfold packetD; positivity
  have he : 0 < width L mu KD eps := by rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  have hr := actual_mu_distance_over_relay_width L mu KD eps a hmu hLmu hKD0 heps ha
  have hpure := actual_pure_gate_margin C N K L mu KD eps a csigma hL hmu hKD heps ha0 hC hN hK hreserve
  have hEq : secondBudget C N K L mu KD eps a =
      C * N * mu + (2 * K * C * N) * (mu * packetD L mu KD eps / (a * width L mu KD eps)) +
      totalBudget C N L mu KD eps * (K / (a ^ 2 * width L mu KD eps ^ 2)) := by
    unfold secondBudget
    field_simp [ne_of_gt hD, ne_of_gt he, ne_of_gt ha0]
    <;> ring
  rw [hEq]
  have hfirst := mul_le_mul_of_nonneg_left hLmu (mul_nonneg hC hN)
  have hsecond := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ 2 * K * C * N)
  unfold sigma at hpure
  have hpure' : totalBudget C N L mu KD eps * (K / (a ^ 2 * width L mu KD eps ^ 2)) ≤ csigma * L / (2 * a ^ 2) := by
    convert! hpure using 1 <;> ring
  have ha2 : 1 ≤ a ^ 2 := by nlinarith only [ha, sq_nonneg (a - 1)]
  have hcs : 0 ≤ csigma := (by positivity : 0 ≤ 2 * K * (3 * C * N + 1)).trans hreserve
  have hdiv : csigma * L / (2 * a ^ 2) ≤ csigma * L / 2 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [ha2])
  nlinarith only [hfirst, hsecond, hpure'.trans hdiv]

theorem actual_total_budget_distance (C N L mu KD eps : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hmu : 0 < mu) (hL : 0 < L) (hKD : 1 ≤ KD) :
    totalBudget C N L mu KD eps ≤ (3 * C * N + 1) * mu * packetD L mu KD eps ^ 2 := by
  have hDsq : mu * packetD L mu KD eps ^ 2 = KD ^ 2 * energy L eps := by
    simpa only [rawBudget, one_mul] using rawBudget_eq 1 1 L mu KD eps hL hmu
  have hKD2 : 1 ≤ KD ^ 2 := one_le_pow₀ hKD
  have hE : 0 ≤ energy L eps := by unfold energy; positivity
  have he := mul_le_mul_of_nonneg_right hKD2 hE
  rw [totalBudget_eq _ _ _ _ _ _ hL hmu]
  calc
    _ ≤ (3 * C * N + 1) * (KD ^ 2 * energy L eps) := by nlinarith only [he]
    _ = _ := by rw [← hDsq]; ring
 
theorem actual_third_link_four_group_bound (C N K L mu KD eps a : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K) (hmu : 0 < mu) (hL : 0 < L)
    (hKD : 1 ≤ KD) (heps : 0 < eps) (ha : 0 < a) :
    let Nb := 3 * C * N + 1
    thirdBudget C N K L mu KD eps a ≤ (1 + 3 * K) *
      (group1 Nb L mu KD eps a + group2 Nb L mu KD eps a +
        group3 Nb L mu KD eps a + group4 Nb L mu KD eps) := by
  intro Nb
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hD : 0 < packetD L mu KD eps := by unfold packetD; positivity
  have he : 0 < width L mu KD eps := by rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  have hNb : 0 ≤ Nb := by dsimp [Nb]; positivity
  have hCN : C * N ≤ Nb := by dsimp [Nb]; nlinarith only [mul_nonneg hC hN]
  have htotal := actual_total_budget_distance C N L mu KD eps hC hN hmu hL hKD
  have hfirst : C * (N * mu) * packetD L mu KD eps ^ 2 / packetD L mu KD eps ^ 3 ≤ group4 Nb L mu KD eps := by
    have hh := mul_le_mul_of_nonneg_right hCN (div_nonneg hmu.le hD.le)
    convert! hh using 1 <;> (try unfold group4) <;> field_simp [ne_of_gt hD] <;> ring
  have hsecond : 3 * (K / (a * width L mu KD eps)) *
      (C * (N * mu) * packetD L mu KD eps ^ 2 / packetD L mu KD eps ^ 2) ≤
      3 * K * group3 Nb L mu KD eps a := by
    have hh := mul_le_mul_of_nonneg_right hCN
      (by positivity : 0 ≤ 3 * K * mu / (a * width L mu KD eps))
    convert! hh using 1 <;> (try unfold group3) <;> field_simp [ne_of_gt hD, ne_of_gt he, ne_of_gt ha] <;> ring
  have hthird : 3 * (K / (a * width L mu KD eps) ^ 2) *
      (C * (N * mu) * packetD L mu KD eps ^ 2 / packetD L mu KD eps) ≤
      3 * K * group2 Nb L mu KD eps a := by
    have hh := mul_le_mul_of_nonneg_right hCN
      (by positivity : 0 ≤ 3 * K * mu * packetD L mu KD eps / (a ^ 2 * width L mu KD eps ^ 2))
    convert! hh using 1 <;> (try unfold group2) <;> field_simp [ne_of_gt hD, ne_of_gt he, ne_of_gt ha] <;> ring
  have hfourth : (K / (a * width L mu KD eps) ^ 3) * totalBudget C N L mu KD eps ≤
      K * group1 Nb L mu KD eps a := by
    have hh := mul_le_mul_of_nonneg_left htotal
      (by positivity : 0 ≤ K / (a * width L mu KD eps) ^ 3)
    convert! hh using 1 <;> (try unfold group1) <;> dsimp [Nb] <;> field_simp [ne_of_gt he, ne_of_gt ha] <;> ring
  have hg1 : 0 ≤ group1 Nb L mu KD eps a := by unfold group1; positivity
  have hg2 : 0 ≤ group2 Nb L mu KD eps a := by unfold group2; positivity
  have hg3 : 0 ≤ group3 Nb L mu KD eps a := by unfold group3; positivity
  have hg4 : 0 ≤ group4 Nb L mu KD eps := by unfold group4; positivity
  have hsum := add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth
  have hupper : group4 Nb L mu KD eps + 3 * K * group3 Nb L mu KD eps a +
      3 * K * group2 Nb L mu KD eps a + K * group1 Nb L mu KD eps a ≤
      (1 + 3 * K) * (group1 Nb L mu KD eps a + group2 Nb L mu KD eps a +
        group3 Nb L mu KD eps a + group4 Nb L mu KD eps) := by
    have h1 := mul_le_mul_of_nonneg_right (by linarith only [hK] : K ≤ 1 + 3 * K) hg1
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 3 * K ≤ 1 + 3 * K) hg2
    have h3 := mul_le_mul_of_nonneg_right (by linarith : 3 * K ≤ 1 + 3 * K) hg3
    have h4 := mul_le_mul_of_nonneg_right (by linarith only [hK] : 1 ≤ 1 + 3 * K) hg4
    nlinarith only [h1, h2, h3, h4]
  exact hsum.trans hupper

theorem actual_third_link_reserved_budget (C N K Ca L mu KD eps r : ℝ)
    (hC : 0 ≤ C) (hN : 0 ≤ N) (hK : 0 ≤ K) (hCa : 1 ≤ Ca) (hmu : 0 < mu) (hLmu : mu ≤ L)
    (hKD : 1 ≤ KD) (heps : 0 < eps) (hr : 1 ≤ r)
    (hreserve : 16 * (1 + 3 * K) * (3 * C * N + 1) ≤ KD) :
    thirdBudget C N K L mu KD eps (relayAmplitude Ca (L / mu) r) ≤ rho L mu eps r / 4 := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hk : 1 ≤ L / mu := (one_le_div hmu).mpr hLmu
  have hCa0 : 0 < Ca := lt_of_lt_of_le zero_lt_one hCa
  have ha : 0 < relayAmplitude Ca (L / mu) r :=
    hCa0.trans_le (relayAmplitude_bounds Ca (L / mu) r hCa0 hk hr).1
  apply (actual_third_link_four_group_bound C N K L mu KD eps _ hC hN hK hmu hL hKD heps ha).trans
  exact actual_third_group_reserved_budget (1 + 3 * K) (3 * C * N + 1) Ca L mu KD eps r
    (by positivity) (by positivity) hCa hmu hLmu (lt_of_lt_of_le zero_lt_one hKD) heps hr hreserve

end
end FangqingActualRelayLinkBudgets
end

section
-- Source component: RelayUniversalScalarReserves.lean

namespace FangqingRelayUniversalScalarReserves

open FangqingActualRelayScaling FangqingThirdGroupScaling FangqingActualRelayLinkBudgets

noncomputable section

set_option maxHeartbeats 1800000

theorem actual_universal_scalar_reserves (C Kg Kh KDlower : ℝ)
    (hC : 0 ≤ C) (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKDlower : 0 ≤ KDlower) :
    ∃ KD csigma Clink : ℝ, 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Clink ∧
    ∀ L mu eps r : ℝ, 0 < mu → mu ≤ L → 0 < eps → 1 ≤ r →
      let a := relayAmplitude 1 (L / mu) r
      let D := packetD L mu KD eps
      let ell := width L mu KD eps
      4 * mu ≤ sigma L a csigma ∧
      totalBudget C 8 L mu KD eps * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 2 ∧
      mu + 4 * (Kh / (a * ell)) ^ 2 * (C * (8 * mu) * D) ^ 2 / sigma L a csigma ≤ 4 * mu - mu ∧
      secondBudget C 8 Kg L mu KD eps a ≤ Clink * L ∧
      thirdBudget C 8 Kg L mu KD eps a ≤ rho L mu eps r / 4 := by
  let KD := 1 + KDlower + 16 * (1 + 3 * Kg) * (3 * C * 8 + 1)
  let csigma := 5 + 2 * (Kg + Kh) * (3 * C * 8 + 1) + 4 * Kh ^ 2 * C ^ 2 * 8 ^ 2
  let Clink := C * 8 * (1 + 2 * Kg) + csigma / 2
  have hthird : 0 ≤ 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) := by positivity
  have hKD : 1 ≤ KD := by dsimp [KD]; linarith only [hKDlower, hthird]
  have hKDl : KDlower ≤ KD := by dsimp [KD]; linarith only [hthird]
  have hres3 : 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) ≤ KD := by dsimp [KD]; linarith only [hKDlower]
  have hpureNon : 0 ≤ 2 * (Kg + Kh) * (3 * C * 8 + 1) := by positivity
  have hschurNon : 0 ≤ 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 := by positivity
  have hcs : 0 < csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon]
  have hresSigma : 4 * (1 : ℝ) ^ 2 ≤ csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon]
  have hresSchur : 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 ≤ csigma := by
    dsimp [csigma]; linarith only [hpureNon]
  have hresKh : 2 * Kh * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKg (by positivity : 0 ≤ 2 * (3 * C * 8 + 1))
    dsimp [csigma]
    nlinarith only [hh, hschurNon]
  have hresKg : 2 * Kg * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKh (by positivity : 0 ≤ 2 * (3 * C * 8 + 1))
    dsimp [csigma]
    nlinarith only [hh, hschurNon]
  refine ⟨KD, csigma, Clink, hKD, hKDl, hcs, (by dsimp [Clink]; positivity), ?_⟩
  intro L mu eps r hmu hLmu heps hr a D ell
  have hL : 0 < L := hmu.trans_le hLmu
  obtain ⟨ha, hsigma⟩ := actual_amplitude_sigma_lower 1 L mu r csigma (by norm_num) hmu hLmu hr hresSigma
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hsig0 : 0 < sigma L a csigma := by unfold sigma; positivity
  have hpure := actual_pure_gate_margin C 8 Kh L mu KD eps a csigma hL hmu hKD heps ha0
    hC (by norm_num) hKh hresKh
  have hschur := actual_schur_margin Kh C 8 L mu KD eps a csigma hL hmu hKD0 heps ha0 hcs hresSchur
  refine ⟨hsigma, ?_, ?_, ?_, ?_⟩
  · convert! hpure using 1 <;> ring
  · exact hschur.trans (by linarith only [hmu])
  · exact actual_link_second_budget C 8 Kg L mu KD eps a csigma hC (by norm_num) hKg
      hmu hLmu hKD heps ha hresKg
  · exact actual_third_link_reserved_budget C 8 Kg 1 L mu KD eps r hC (by norm_num) hKg
      (by norm_num) hmu hLmu hKD heps hr hres3

end
end FangqingRelayUniversalScalarReserves
end

section
-- Source component: UniformActualRelayClass.lean

open scoped ContDiff

namespace FangqingUniformActualRelayClass

open FangqingActualSeedRelayFamily FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingActualRelayLinkBudgets FangqingRelayUniversalScalarReserves FangqingRelayAnalyticAssembly
  FangqingRelayFenchelInterfaces FangqingActualInactivePacket FangqingLocalizedSeedJets
  FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 4500000

universe u

theorem actual_uniform_relay_class (phi : ℝ → ℝ) (B left right Camp KDlower : ℝ)
    (hCamp : 0 ≤ Camp) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ KD csigma Cglobal Cdelta : ℝ,
      1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧ 0 ≤ Cdelta ∧
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ (n : ℕ) (L mu eps r LH rhoH Rp A : ℝ)
      (H0 H1 : Fin (n + 1) → E → ℝ) (z0 z1 handle : Fin (n + 1) → E) (center : Fin n → E),
      0 < mu → mu ≤ L → 0 < eps → 1 ≤ r → 0 ≤ LH → 0 ≤ rhoH →
      packetD L mu KD eps ≤ Rp → packetD L mu KD eps ≤ A →
      (∀ t, AnalyticClass (H0 t) (4 * mu) LH rhoH) →
      (∀ t, AnalyticClass (H1 t) (4 * mu) LH rhoH) →
      (∀ t, ‖handle t‖ ≤ 1) →
      (∀ t y, H1 t y = H0 t y - localizedSeed theta phi Rp A
        (Camp * (8 * mu) * packetD L mu KD eps ^ 2) (handle t) y) →
      (∀ t y, H0 t (z0 t) ≤ H0 t y) → (∀ t y, H1 t (z1 t) ≤ H1 t y) →
      let a := relayAmplitude 1 (L / mu) r
      let D := packetD L mu KD eps
      let ell := width L mu KD eps
      let rw := reward Cdelta 8 L KD eps
      let h0 := fun t => reduced (H0 t) mu
      let h1 := fun t => reduced (H1 t) mu
      let m0 := fun t => H0 t (z0 t)
      let m1 := fun t => H1 t (z1 t)
      let gate := fun j => scaledGate theta (a * ell) (center j)
      let J := assembled n L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate
      ContDiff ℝ 2 J ∧
      (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + LH) * ‖x - y‖) ∧
      FangqingRelayGlobalJointClass.HessianRate J (rhoH + rho L mu eps r / 4) ∧
      (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) mu
        (FangqingRelayDualAssembly.negativeFamily n L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) := by
  obtain ⟨Kd, hKd, Kg, hKg, Kh, hKh, hFamily⟩ := actual_seed_relay_joint_and_dual_class.{u} phi B left right hp hl hr
  let Cdelta := Kd * Camp
  have hCdelta : 0 ≤ Cdelta := mul_nonneg hKd hCamp
  obtain ⟨KD, csigma, Clink, hKD, hKDl, hcs, hClink, hReserve⟩ :=
    actual_universal_scalar_reserves Cdelta Kg Kh KDlower hCdelta hKg hKh hKDlower
  let Cglobal := 4 + 2 * csigma + Clink
  refine ⟨KD, csigma, Cglobal, Cdelta, hKD, hKDl, hcs, (by dsimp [Cglobal]; positivity), hCdelta, ?_⟩
  intro E inst inst' inst'' n L mu eps r LH rhoH Rp A H0 H1 z0 z1 handle center
    hmu hLmu heps hr hLH hrho hRp hA hH0 hH1 hh hrel hm0 hm1
    a D ell rw h0 h1 m0 m1 gate J
  have hL : 0 < L := hmu.trans_le hLmu
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hD : 0 < D := by dsimp [D, packetD]; positivity
  have he : 0 < ell := by dsimp [ell]; rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  have hk : 1 ≤ L / mu := (one_le_div hmu).mpr hLmu
  have ha : 1 ≤ a := (relayAmplitude_bounds 1 (L / mu) r (by norm_num) hk hr).1
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hSig : 0 < sigma L a csigma := by unfold sigma; positivity
  have hamp : 0 ≤ Camp * (8 * mu) * D ^ 2 := by positivity
  have hrw : 0 ≤ rw := by dsimp [rw, reward, rewardCoefficient, energy]; positivity
  obtain ⟨hSigma, hPure, hSchur, hSecond, hThird⟩ := hReserve L mu eps r hmu hLmu heps hr
  have hRaw : Kd * (Camp * (8 * mu) * D ^ 2) = rawBudget Cdelta 8 L mu KD eps := by
    dsimp [Cdelta, rawBudget, D]
    ring
  have hTotal : Kd * (Camp * (8 * mu) * D ^ 2) + rw = totalBudget Cdelta 8 L mu KD eps := by
    rw [hRaw]
    rfl
  have hFirst : Kd * (Camp * (8 * mu) * D ^ 2) / D = Cdelta * (8 * mu) * D := by
    dsimp [Cdelta]
    field_simp [ne_of_gt hD]
    <;> ring
  have hPure' : (Kd * (Camp * (8 * mu) * D ^ 2) + rw) * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 2 := by
    rw [hTotal]
    exact hPure
  have hSchur' : mu + 4 * (Kh / (a * ell)) ^ 2 * (Kd * (Camp * (8 * mu) * D ^ 2) / D) ^ 2 /
      sigma L a csigma ≤ 4 * mu - mu := by
    rw [hFirst]
    exact hSchur
  obtain ⟨hJ, hG, hH, hSC⟩ := hFamily E n L mu (lam L mu) a (sigma L a csigma) rw (4 * mu) mu LH rhoH
    Rp A (Camp * (8 * mu) * D ^ 2) D (a * ell) H0 H1 z0 z1 handle center
    hL.le hmu.le hLH hrho hrw hD hRp hA hamp (mul_pos ha0 he) hSig hmu.le
    hH0 hH1 hh hrel hm0 hm1 hSigma hPure' hSchur'
  have hEq2 : Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 2 +
      2 * (Kg / (a * ell)) * (Kd * (Camp * (8 * mu) * D ^ 2) / D) +
      (Kg / (a * ell) ^ 2) * (Kd * (Camp * (8 * mu) * D ^ 2) + rw) =
      secondBudget Cdelta 8 Kg L mu KD eps a := by
    rw [hTotal]
    unfold secondBudget
    dsimp [Cdelta, D, ell]
    ring
  have hEq3 : Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 3 +
      3 * (Kg / (a * ell)) * (Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 2) +
      3 * (Kg / (a * ell) ^ 2) * (Kd * (Camp * (8 * mu) * D ^ 2) / D) +
      (Kg / (a * ell) ^ 3) * (Kd * (Camp * (8 * mu) * D ^ 2) + rw) =
      thirdBudget Cdelta 8 Kg L mu KD eps a := by
    rw [hTotal]
    unfold thirdBudget
    dsimp [Cdelta, D, ell]
    ring
  have hlam0 : 0 ≤ lam L mu := Real.sqrt_nonneg _
  have hlam2 : lam L mu ^ 2 = L * mu := Real.sq_sqrt (by positivity)
  have hLL := mul_le_mul_of_nonneg_left hLmu hL.le
  have hlam : lam L mu ≤ L := by nlinarith only [hL, hlam0, hlam2, hLL]
  have hBase : L + mu + 2 * |lam L mu| ≤ 4 * L := by rw [abs_of_nonneg hlam0]; linarith only [hLmu, hlam]
  have hQuadratic := actual_quadratic_budget L a csigma hL.le hcs.le ha
  refine ⟨hJ, ?_, ?_, hSC⟩
  · intro x y
    apply (hG x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hEq2]
    dsimp [Cglobal]
    nlinarith only [hBase, hQuadratic, hSecond]
  · intro x y
    apply (hH x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hEq3]
    exact add_le_add le_rfl hThird

end
end FangqingUniformActualRelayClass
end

section
-- Source component: ActualSeedRelayFamilyData.lean

open scoped ContDiff

namespace FangqingActualSeedRelayFamilyData

open FangqingRelayAnalyticAssembly FangqingRelayGlobalJointClass FangqingRelayFenchelInterfaces
  FangqingFenchelEndpointClass FangqingActualInactivePacket FangqingRelayStationarity
  FangqingLocalizedSeedJets FangqingActualRelayLink FangqingPublicShellProfiles
  FangqingRadialGateBounds FangqingGateBudgetBridge

noncomputable section

set_option maxHeartbeats 4000000

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_packet_endpoint_jets_data (H : E → ℝ) (beta c lam m nu LH rhoH : ℝ)
    (hb : 0 ≤ beta) (hc : 0 ≤ c) (hLH : 0 ≤ LH) (hrho : 0 ≤ rhoH)
    (hH : AnalyticClass H nu LH rhoH) :
    let F : FangqingRelayBlockGeometry.Pair E → ℝ := fun p => endpoint beta lam (reduced H c) m p.fst p.snd
    ContDiff ℝ 2 F ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ beta + c + 2 * |lam| + LH) ∧
    (∀ x y, ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ rhoH * ‖x - y‖) := by
  intro F
  have heq : F = jointEndpoint H beta c lam m := by
    funext p
    exact endpoint_from_H H beta c lam m p
  rw [heq]
  obtain ⟨hF, hSC, hgrad, hhess⟩ := actual_joint_endpoint_class H beta c lam m nu LH rhoH
    hb hc hLH hrho hH.1 hH.2.1 hH.2.2.1 hH.2.2.2
  exact ⟨hF, second_jet_bound_from_gradient_rate _ _ (by positivity) hgrad, hhess⟩

theorem actual_seed_relay_joint_and_dual_class_data (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∃ Kg : ℝ, 0 ≤ Kg ∧ ∃ Kh : ℝ, 0 ≤ Kh ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (n : ℕ) (beta c lam a sigma reward nu mu LH rhoH Rp A amp D Rg : ℝ)
      (H0 H1 : Fin (n + 1) → F → ℝ) (z0 z1 handle : Fin (n + 1) → F) (center : Fin n → F),
      0 ≤ beta → 0 ≤ c → 0 ≤ LH → 0 ≤ rhoH → 0 ≤ reward → 0 < D → D ≤ Rp → D ≤ A →
      0 ≤ amp → 0 < Rg → 0 < sigma → 0 ≤ mu →
      (∀ t, AnalyticClass (H0 t) nu LH rhoH) → (∀ t, AnalyticClass (H1 t) nu LH rhoH) →
      (∀ t, ‖handle t‖ ≤ 1) →
      (∀ t y, H1 t y = H0 t y - localizedSeed theta phi Rp A amp (handle t) y) →
      (∀ t y, H0 t (z0 t) ≤ H0 t y) → (∀ t y, H1 t (z1 t) ≤ H1 t y) →
      4 * mu ≤ sigma → (Kd * amp + reward) * (Kh / Rg ^ 2) ≤ sigma / 2 →
      mu + 4 * (Kh / Rg) ^ 2 * (Kd * amp / D) ^ 2 / sigma ≤ nu - c →
      let h0 := fun t => reduced (H0 t) c
      let h1 := fun t => reduced (H1 t) c
      let m0 := fun t => H0 t (z0 t)
      let m1 := fun t => H1 t (z1 t)
      let gate := fun j => scaledGate theta Rg (center j)
      let Ll := Kd * amp / D ^ 2 + 2 * (Kg / Rg) * (Kd * amp / D) + (Kg / Rg ^ 2) * (Kd * amp + reward)
      let Rl := Kd * amp / D ^ 3 + 3 * (Kg / Rg) * (Kd * amp / D ^ 2) +
        3 * (Kg / Rg ^ 2) * (Kd * amp / D) + (Kg / Rg ^ 3) * (Kd * amp + reward)
      let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
      (∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ Kd * amp) ∧
      (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
      ContDiff ℝ 2 J ∧
      (∀ x y, ‖gradient J x - gradient J y‖ ≤
        (beta + c + 2 * |lam| + LH + sigma * (1 + a ^ 2) + Ll) * ‖x - y‖) ∧
      FangqingRelayGlobalJointClass.HessianRate J (rhoH + Rl) ∧
      (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n F)) mu
        (FangqingRelayDualAssembly.negativeFamily n beta lam a sigma reward h0 h1 m0 m1 gate x)) := by
  obtain ⟨Kd, hKd, Kg, hKg, hLink⟩ := actual_normalized_gate_link.{u} phi B left right hp hl hr
  have ht : ContDiff ℝ 3 theta := theta_smooth.of_le (by decide)
  obtain ⟨Kh, hKh, hGscalar⟩ := universal_gate_scalar_budgets.{u} theta (7 / 4) (by norm_num) ht
    (fun t ht => theta_one t (by linarith only [ht])) (fun t ht => theta_zero t (by nlinarith only [ht]))
  refine ⟨Kd, hKd, Kg, hKg, Kh, hKh, ?_⟩
  intro F inst inst' inst'' n beta c lam a sigma reward nu mu LH rhoH Rp A amp D Rg
    H0 H1 z0 z1 handle center hb hc hLH hrho hrw hD hRp hA hamp hRg hsigma hmu hH0 hH1
    hh hrel hm0 hm1 hsigmamu hpure hschur h0 h1 m0 m1 gate Ll Rl J
  have hLocal : ∀ t,
      ContDiff ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) z‖ ≤ beta + c + 2 * |lam| + LH) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) x -
        iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) y‖ ≤ rhoH * ‖x - y‖) := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · exact actual_packet_endpoint_jets_data (H1 0) beta c lam (m1 0) nu LH rhoH hb hc hLH hrho (hH1 0)
    · exact actual_packet_endpoint_jets_data (H0 j.succ) beta c lam (m0 j.succ) nu LH rhoH hb hc hLH hrho (hH0 j.succ)
  have hLinks := fun j : Fin n => hLink F Rp A amp D Rg c reward (handle j.succ) (center j)
    (H0 j.succ) (H1 j.succ) (z0 j.succ) (z1 j.succ) hD hRp hA hamp (hh j.succ)
    hRg hrw (hrel j.succ) (hm0 j.succ) (hm1 j.succ)
  have hLl : 0 ≤ Ll := by dsimp [Ll]; positivity
  have hRl : 0 ≤ Rl := by dsimp [Rl]; positivity
  obtain ⟨hJ, hJgrad, hJhess, hJ2, hJ2lip⟩ := actual_assembled_joint_class n beta lam a sigma reward
    h0 h1 m0 m1 gate (beta + c + 2 * |lam| + LH) rhoH Ll Rl hsigma.le (by positivity) hrho hLl hRl
    (fun t => (hLocal t).1) (fun t => (hLocal t).2.1) (fun t => (hLocal t).2.2)
    (fun j => (hLinks j).2.2.2.2.2.1) (fun j => (hLinks j).2.2.2.2.2.2.1)
    (fun j => (hLinks j).2.2.2.2.2.2.2)
  have hDeltaAll : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ Kd * amp := by
    intro t z
    exact (hLink F Rp A amp D Rg c reward (handle t) (0 : F) (H0 t) (H1 t) (z0 t) (z1 t)
      hD hRp hA hamp (hh t) hRg hrw (hrel t) (hm0 t) (hm1 t)).2.2.2.1 z
  refine ⟨hDeltaAll, (fun j z => (hLinks j).2.1 z), hJ, hJgrad, hJhess, ?_⟩
  intro x
  apply FangqingRelayDualAssembly.actual_dual_strongConvex n beta lam a sigma reward (nu - c) mu
    (Kd * amp + reward) (Kh / Rg ^ 2) (Kh / Rg) (Kd * amp / D) h0 h1 m0 m1 gate x
  · intro t
    exact ((hH0 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · intro t
    exact ((hH1 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · intro j
    exact (hGscalar F Rg hRg (center j)).1.of_le (by norm_num)
  · intro t
    exact reduced_strongConvex (H0 t) nu c (hH0 t).2.1
  · intro t
    exact reduced_strongConvex (H1 t) nu c (hH1 t).2.1
  · intro j y
    exact (hLinks j).2.1 y
  · positivity
  · positivity
  · positivity
  · positivity
  · intro j y
    exact (abs_sub _ _).trans (by
      simpa only [abs_of_nonneg hrw] using add_le_add ((hLinks j).2.2.2.1 y) (le_refl |reward|))
  · intro j s v
    exact (hGscalar F Rg hRg (center j)).2.2 s v
  · intro j s v
    exact (hGscalar F Rg hRg (center j)).2.1 s v
  · intro j y v
    apply first_scalar_bound _ (Kd * amp / D) y v
    simpa only [pow_one] using (hLinks j).2.2.2.2.1 1 (by norm_num) (by norm_num) y
  · exact hsigma
  · exact hmu
  · exact hsigmamu
  · exact hpure
  · exact hschur

end
end FangqingActualSeedRelayFamilyData
end

section
-- Source component: RelayUniversalScalarReservesExtra.lean

namespace FangqingRelayUniversalScalarReservesExtra

open FangqingActualRelayScaling FangqingThirdGroupScaling FangqingActualRelayLinkBudgets

noncomputable section

set_option maxHeartbeats 1800000

theorem actual_universal_scalar_reserves_extra (C Kg Kh KDlower csigmaExtra : ℝ)
    (hC : 0 ≤ C) (hKg : 0 ≤ Kg) (hKh : 0 ≤ Kh) (hKDlower : 0 ≤ KDlower) (hExtra : 0 ≤ csigmaExtra) :
    ∃ KD csigma Clink : ℝ, 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ csigmaExtra ≤ csigma ∧ 0 ≤ Clink ∧
    ∀ L mu eps r : ℝ, 0 < mu → mu ≤ L → 0 < eps → 1 ≤ r →
      let a := relayAmplitude 1 (L / mu) r
      let D := packetD L mu KD eps
      let ell := width L mu KD eps
      4 * mu ≤ sigma L a csigma ∧
      totalBudget C 8 L mu KD eps * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 2 ∧
      mu + 4 * (Kh / (a * ell)) ^ 2 * (C * (8 * mu) * D) ^ 2 / sigma L a csigma ≤ 4 * mu - mu ∧
      secondBudget C 8 Kg L mu KD eps a ≤ Clink * L ∧
      thirdBudget C 8 Kg L mu KD eps a ≤ rho L mu eps r / 4 := by
  let KD := 1 + KDlower + 16 * (1 + 3 * Kg) * (3 * C * 8 + 1)
  let csigma := 5 + 2 * (Kg + Kh) * (3 * C * 8 + 1) + 4 * Kh ^ 2 * C ^ 2 * 8 ^ 2 + csigmaExtra
  let Clink := C * 8 * (1 + 2 * Kg) + csigma / 2
  have hthird : 0 ≤ 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) := by positivity
  have hKD : 1 ≤ KD := by dsimp [KD]; linarith only [hKDlower, hthird]
  have hKDl : KDlower ≤ KD := by dsimp [KD]; linarith only [hthird]
  have hres3 : 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) ≤ KD := by dsimp [KD]; linarith only [hKDlower]
  have hpureNon : 0 ≤ 2 * (Kg + Kh) * (3 * C * 8 + 1) := by positivity
  have hschurNon : 0 ≤ 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 := by positivity
  have hcs : 0 < csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon, hExtra]
  have hresSigma : 4 * (1 : ℝ) ^ 2 ≤ csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon, hExtra]
  have hresSchur : 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 ≤ csigma := by
    dsimp [csigma]; linarith only [hpureNon, hExtra]
  have hresKh : 2 * Kh * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKg (by positivity : 0 ≤ 2 * (3 * C * 8 + 1))
    dsimp [csigma]
    nlinarith only [hh, hschurNon, hExtra]
  have hresKg : 2 * Kg * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKh (by positivity : 0 ≤ 2 * (3 * C * 8 + 1))
    dsimp [csigma]
    nlinarith only [hh, hschurNon, hExtra]
  have hExtraReserve : csigmaExtra ≤ csigma := by
    dsimp [csigma]
    linarith only [hpureNon, hschurNon]
  refine ⟨KD, csigma, Clink, hKD, hKDl, hcs, hExtraReserve, (by dsimp [Clink]; positivity), ?_⟩
  intro L mu eps r hmu hLmu heps hr a D ell
  have hL : 0 < L := hmu.trans_le hLmu
  obtain ⟨ha, hsigma⟩ := actual_amplitude_sigma_lower 1 L mu r csigma (by norm_num) hmu hLmu hr hresSigma
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hsig0 : 0 < sigma L a csigma := by unfold sigma; positivity
  have hpure := actual_pure_gate_margin C 8 Kh L mu KD eps a csigma hL hmu hKD heps ha0
    hC (by norm_num) hKh hresKh
  have hschur := actual_schur_margin Kh C 8 L mu KD eps a csigma hL hmu hKD0 heps ha0 hcs hresSchur
  refine ⟨hsigma, ?_, ?_, ?_, ?_⟩
  · convert! hpure using 1 <;> ring
  · exact hschur.trans (by linarith only [hmu])
  · exact actual_link_second_budget C 8 Kg L mu KD eps a csigma hC (by norm_num) hKg
      hmu hLmu hKD heps ha hresKg
  · exact actual_third_link_reserved_budget C 8 Kg 1 L mu KD eps r hC (by norm_num) hKg
      (by norm_num) hmu hLmu hKD heps hr hres3

end
end FangqingRelayUniversalScalarReservesExtra
end

section
-- Source component: UniformActualRelayMaster.lean

open scoped ContDiff

namespace FangqingUniformActualRelayMaster

open FangqingActualSeedRelayFamilyData FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingActualRelayLinkBudgets FangqingRelayUniversalScalarReservesExtra FangqingRelayAnalyticAssembly
  FangqingRelayFenchelInterfaces FangqingActualInactivePacket FangqingLocalizedSeedJets
  FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 4500000

universe u

theorem actual_uniform_relay_master (phi : ℝ → ℝ) (B left right Camp KDlower : ℝ)
    (hCamp : 0 ≤ Camp) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ KD csigma Cglobal Cdelta Ctheta : ℝ,
      1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧ 0 ≤ Cdelta ∧
      0 ≤ Ctheta ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      4 * Ctheta * (3 * Cdelta * 8 + 1) ≤ csigma ∧
    ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ (n : ℕ) (L mu eps r LH rhoH Rp A : ℝ)
      (H0 H1 : Fin (n + 1) → E → ℝ) (z0 z1 handle : Fin (n + 1) → E) (center : Fin n → E),
      0 < mu → mu ≤ L → 0 < eps → 1 ≤ r → 0 ≤ LH → 0 ≤ rhoH →
      packetD L mu KD eps ≤ Rp → packetD L mu KD eps ≤ A →
      (∀ t, AnalyticClass (H0 t) (4 * mu) LH rhoH) →
      (∀ t, AnalyticClass (H1 t) (4 * mu) LH rhoH) →
      (∀ t, ‖handle t‖ ≤ 1) →
      (∀ t y, H1 t y = H0 t y - localizedSeed theta phi Rp A
        (Camp * (8 * mu) * packetD L mu KD eps ^ 2) (handle t) y) →
      (∀ t y, H0 t (z0 t) ≤ H0 t y) → (∀ t y, H1 t (z1 t) ≤ H1 t y) →
      let a := relayAmplitude 1 (L / mu) r
      let D := packetD L mu KD eps
      let ell := width L mu KD eps
      let rw := reward Cdelta 8 L KD eps
      let h0 := fun t => reduced (H0 t) mu
      let h1 := fun t => reduced (H1 t) mu
      let m0 := fun t => H0 t (z0 t)
      let m1 := fun t => H1 t (z1 t)
      let gate := fun j => scaledGate theta (a * ell) (center j)
      let J := assembled n L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate
      (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ rawBudget Cdelta 8 L mu KD eps) ∧
      (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
      ((rw + rawBudget Cdelta 8 L mu KD eps) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma L a csigma / 2) ∧
      ContDiff ℝ 2 J ∧
      (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + LH) * ‖x - y‖) ∧
      FangqingRelayGlobalJointClass.HessianRate J (rhoH + rho L mu eps r / 4) ∧
      (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) mu
        (FangqingRelayDualAssembly.negativeFamily n L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) := by
  obtain ⟨Kd, hKd, Kg, hKg, Kh, hKh, hFamily⟩ := actual_seed_relay_joint_and_dual_class_data.{u} phi B left right hp hl hr
  let Cdelta := Kd * Camp
  have hCdelta : 0 ≤ Cdelta := mul_nonneg hKd hCamp
  have ht : ContDiff ℝ 3 theta := theta_smooth.of_le (by decide)
  obtain ⟨Ctheta, hCt, htjet⟩ := FangqingRadialGateBounds.scalar_profile_derivatives_bounded theta 3 (7 / 4) ht
    (fun u hu => theta_one u (by linarith only [hu])) (fun u hu => theta_zero u (by nlinarith only [hu]))
  have htDeriv : ∀ u : ℝ, |deriv theta u| ≤ Ctheta := by
    intro u
    have hh := FangqingGateBudgetBridge.first_scalar_bound theta Ctheta u (1 : ℝ) (htjet 1 (by norm_num) u)
    simpa only [fderiv_apply_one_eq_deriv, norm_one, mul_one] using hh
  obtain ⟨KD, csigma, Clink, hKD, hKDl, hcs, hExtra, hClink, hReserve⟩ :=
    actual_universal_scalar_reserves_extra Cdelta Kg Kh KDlower (4 * Ctheta * (3 * Cdelta * 8 + 1))
      hCdelta hKg hKh hKDlower (by positivity)
  let Cglobal := 4 + 2 * csigma + Clink
  refine ⟨KD, csigma, Cglobal, Cdelta, Ctheta, hKD, hKDl, hcs, (by dsimp [Cglobal]; positivity), hCdelta,
    hCt, htDeriv, hExtra, ?_⟩
  intro E inst inst' inst'' n L mu eps r LH rhoH Rp A H0 H1 z0 z1 handle center
    hmu hLmu heps hr hLH hrho hRp hA hH0 hH1 hh hrel hm0 hm1
    a D ell rw h0 h1 m0 m1 gate J
  have hL : 0 < L := hmu.trans_le hLmu
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hD : 0 < D := by dsimp [D, packetD]; positivity
  have he : 0 < ell := by dsimp [ell]; rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  have hk : 1 ≤ L / mu := (one_le_div hmu).mpr hLmu
  have ha : 1 ≤ a := (relayAmplitude_bounds 1 (L / mu) r (by norm_num) hk hr).1
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hSig : 0 < sigma L a csigma := by unfold sigma; positivity
  have hamp : 0 ≤ Camp * (8 * mu) * D ^ 2 := by positivity
  have hrw : 0 ≤ rw := by dsimp [rw, reward, rewardCoefficient, energy]; positivity
  obtain ⟨hSigma, hPure, hSchur, hSecond, hThird⟩ := hReserve L mu eps r hmu hLmu heps hr
  have hRaw : Kd * (Camp * (8 * mu) * D ^ 2) = rawBudget Cdelta 8 L mu KD eps := by
    dsimp [Cdelta, rawBudget, D]
    ring
  have hTotal : Kd * (Camp * (8 * mu) * D ^ 2) + rw = totalBudget Cdelta 8 L mu KD eps := by
    rw [hRaw]
    rfl
  have hFirst : Kd * (Camp * (8 * mu) * D ^ 2) / D = Cdelta * (8 * mu) * D := by
    dsimp [Cdelta]
    field_simp [ne_of_gt hD]
    <;> ring
  have hPure' : (Kd * (Camp * (8 * mu) * D ^ 2) + rw) * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 2 := by
    rw [hTotal]
    exact hPure
  have hSchur' : mu + 4 * (Kh / (a * ell)) ^ 2 * (Kd * (Camp * (8 * mu) * D ^ 2) / D) ^ 2 /
      sigma L a csigma ≤ 4 * mu - mu := by
    rw [hFirst]
    exact hSchur
  obtain ⟨hDelta, hRange, hJ, hG, hH, hSC⟩ := hFamily E n L mu (lam L mu) a (sigma L a csigma) rw (4 * mu) mu LH rhoH
    Rp A (Camp * (8 * mu) * D ^ 2) D (a * ell) H0 H1 z0 z1 handle center
    hL.le hmu.le hLH hrho hrw hD hRp hA hamp (mul_pos ha0 he) hSig hmu.le
    hH0 hH1 hh hrel hm0 hm1 hSigma hPure' hSchur'
  have hEq2 : Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 2 +
      2 * (Kg / (a * ell)) * (Kd * (Camp * (8 * mu) * D ^ 2) / D) +
      (Kg / (a * ell) ^ 2) * (Kd * (Camp * (8 * mu) * D ^ 2) + rw) =
      secondBudget Cdelta 8 Kg L mu KD eps a := by
    rw [hTotal]
    unfold secondBudget
    dsimp [Cdelta, D, ell]
    ring
  have hEq3 : Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 3 +
      3 * (Kg / (a * ell)) * (Kd * (Camp * (8 * mu) * D ^ 2) / D ^ 2) +
      3 * (Kg / (a * ell) ^ 2) * (Kd * (Camp * (8 * mu) * D ^ 2) / D) +
      (Kg / (a * ell) ^ 3) * (Kd * (Camp * (8 * mu) * D ^ 2) + rw) =
      thirdBudget Cdelta 8 Kg L mu KD eps a := by
    rw [hTotal]
    unfold thirdBudget
    dsimp [Cdelta, D, ell]
    ring
  have hlam0 : 0 ≤ lam L mu := Real.sqrt_nonneg _
  have hlam2 : lam L mu ^ 2 = L * mu := Real.sq_sqrt (by positivity)
  have hLL := mul_le_mul_of_nonneg_left hLmu hL.le
  have hlam : lam L mu ≤ L := by nlinarith only [hL, hlam0, hlam2, hLL]
  have hBase : L + mu + 2 * |lam L mu| ≤ 4 * L := by rw [abs_of_nonneg hlam0]; linarith only [hLmu, hlam]
  have hQuadratic := actual_quadratic_budget L a csigma hL.le hcs.le ha
  have hStationarityPure := actual_pure_gate_margin Cdelta 8 (2 * Ctheta) L mu KD eps a csigma
    hL hmu hKD heps ha0 hCdelta (by norm_num) (by positivity) (by convert! hExtra using 1 <;> ring)
  refine ⟨?_, hRange, ?_, hJ, ?_, ?_, hSC⟩
  · intro t z
    rw [← hRaw]
    exact hDelta t z
  · convert! hStationarityPure using 1 <;> unfold totalBudget <;> dsimp [rw] <;> ring
  · intro x y
    apply (hG x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hEq2]
    dsimp [Cglobal]
    nlinarith only [hBase, hQuadratic, hSecond]
  · intro x y
    apply (hH x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [hEq3]
    exact add_le_add le_rfl hThird

end
end FangqingUniformActualRelayMaster
end

section
-- Source component: PhysicalRelayMasterData.lean

open scoped ContDiff

namespace FangqingPhysicalRelayMasterData

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingPairedShellAnalyticItems FangqingUniformActualRelayMaster FangqingActualRelayScaling
  FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 5500000

universe u

theorem actual_physical_relay_master_data
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw KDlower : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      4 * Ctheta * (3 * Cdelta * 8 + 1) ≤ csigma ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
      (tail : Fin (outer + 1) → Fin (nt + 2) → W)
      (L mu eps r delta omega q scale lam0 : ℝ),
      (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
      0 < mu → mu ≤ L → 0 < eps → 1 ≤ r → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam0 → omega = Cw * lam0 * q ^ 2 → ((nt + 2 : ℕ) : ℝ) ≤ Cm * q →
      scale * lam0 = 8 * mu → distanceScale q omega = packetD L mu KD eps →
      let nu := scale * lam0
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
      let A := CA * D
      let R := 2 * A
      let s := Cs * nu * D
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let H0 := fun t => inactiveShell (QPhysical q nu C)
        (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
      let H1 := fun t z => H0 t z - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) z
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
        (∀ t, AnalyticClass (H0 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
        (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
        (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
        (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
          3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
        ∀ center : Fin outer → PhysicalSpace A0 B0 W,
        let a := relayAmplitude 1 (L / mu) r
        let ell := width L mu KD eps
        let rw := reward Cdelta 8 L KD eps
        let h0 := fun t => reduced (H0 t) mu
        let h1 := fun t => reduced (H1 t) mu
        let m0 := fun t => H0 t 0
        let m1 := fun t => H1 t (Z t)
        let gate := fun j => scaledGate theta (a * ell) (center j)
        let J := assembled outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate
        (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ rawBudget Cdelta 8 L mu KD eps) ∧
        (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
        ((rw + rawBudget Cdelta 8 L mu KD eps) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma L a csigma / 2) ∧
        ContDiff ℝ 2 J ∧
        (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + CL * nu * q ^ 2) * ‖x - y‖) ∧
        FangqingRelayGlobalJointClass.HessianRate J (Crho * scale + rho L mu eps r / 4) ∧
        (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual outer (PhysicalSpace A0 B0 W))) mu
          (FangqingRelayDualAssembly.negativeFamily outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  obtain ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, hPacket⟩ :=
    actual_paired_shell_analytic_items.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  let Cs := 2 * Cw
  let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
  let Camp := Cs * CA
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCA : 1 ≤ CA := by
    have h1 : 0 ≤ 2 * Ks * Cs := by positivity
    have h2 : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
    dsimp [CA]
    linarith only [h1, h2]
  have hCamp : 0 ≤ Camp := mul_nonneg hCs (zero_le_one.trans hCA)
  obtain ⟨KD, csigma, Cglobal, Cdelta, Ctheta, hKD, hKDl, hcs, hCG, hCD, hCt, hDeriv, hExtra, hUniform⟩ :=
    actual_uniform_relay_master.{u} phi Bp left right Camp KDlower hCamp hKDlower hp hl hr
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
    hCD, hCt, hDeriv, hExtra, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r delta omega q scale lam0 hh ht hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
    nu D Cs' CA' A R s M gain H0 H1 CL Crho
  have hData := fun t : Fin (outer + 1) => hPacket A0 B0 W C (h t) nt (tail t) delta omega q scale lam0
    (hh t) (ht t) hd hdw hq hscale hlam0 homega hn
  choose Z hZmin hZunique hZnorm hZgap hZbulk using fun t => (hData t).2.2.2.2.2.2
  have hL : 0 < L := hmu.trans_le hLmu
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hA : D ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hCA hD.le
    simpa only [one_mul] using hh
  have hR : A ≤ R := by dsimp [R]; linarith only [hD.trans_le hA]
  have hdpA : packetD L mu KD eps ≤ A := by rw [← hDistance]; exact hA
  have hdpR : packetD L mu KD eps ≤ R := hdpA.trans hR
  have hLH : 0 ≤ CL * nu * q ^ 2 := by dsimp [CL, nu]; positivity
  have hrho : 0 ≤ Crho * scale := by dsimp [Crho]; positivity
  have hH0 : ∀ t, AnalyticClass (H0 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale) := by
    intro t
    have hh := (hData t).1
    have hmod : nu / 2 = 4 * mu := by dsimp [nu]; rw [hnu]; ring
    change AnalyticClass _ (nu / 2) (CL * nu * q ^ 2) (Crho * scale) at hh
    rw [hmod] at hh
    exact hh
  have hH1 : ∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale) := by
    intro t
    have hh := (hData t).2.1
    have hmod : nu / 2 = 4 * mu := by dsimp [nu]; rw [hnu]; ring
    change AnalyticClass _ (nu / 2) (CL * nu * q ^ 2) (Crho * scale) at hh
    rw [hmod] at hh
    exact hh
  have hHandle : ∀ t, ‖mkPhysical (h t) (0 : B0) (0 : W)‖ ≤ 1 := by
    intro t
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical (h t) (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h t, (0 : B0)))
    change ‖mkPhysical (h t) (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h t, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h t, (0 : B0))‖ ^ 2 = ‖h t‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh t, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical (h t) (0 : B0) (0 : W))]
  have hAmp : s * A = Camp * (8 * mu) * packetD L mu KD eps ^ 2 := by
    rw [← hDistance, ← hnu]
    dsimp [s, A, Camp, CA, Cs, CA', Cs', D, nu]
    ring
  refine ⟨Z, hH0, hH1, (fun t => (hData t).2.2.2.2.2.1), hZmin, hZnorm, hZgap, hZbulk, ?_⟩
  intro center
  exact hUniform (PhysicalSpace A0 B0 W) outer L mu eps r (CL * nu * q ^ 2) (Crho * scale) R A
    H0 H1 (fun _ => 0) Z (fun t => mkPhysical (h t) 0 0) center
    hmu hLmu heps hr hLH hrho hdpR hdpA hH0 hH1 hHandle
    (fun t y => by change H0 t y - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) y = _; rw [hAmp])
    (fun t => (hData t).2.2.2.2.2.1) hZmin

end
end FangqingPhysicalRelayMasterData
end

section
-- Source component: FlatRelayValueInterfaces.lean

namespace FangqingFlatRelayValueInterfaces

open FangqingRelayAnalyticAssembly FangqingRelayStationarity FangqingRelayValueBridge
  FangqingRelayValueJointClass FangqingFenchelEndpointClass FangqingHessianTensorIsometry

noncomputable section

set_option maxHeartbeats 2500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem actual_flat_class_supplies_exact_value (n : ℕ) (beta lam a sigma reward L mu rho : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (hrho : 0 ≤ rho)
    (hJ : ContDiff ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate))
    (hGrad : ∀ x y, ‖gradient (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) x -
      gradient (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) y‖ ≤ L * ‖x - y‖)
    (hHess : FangqingFenchelEndpointClass.HessianRate
      (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) rho)
    (hSC : ∀ X : Blocks n E, StrongConvexOn
      (Set.univ : Set (FangqingRelayValueBridge.Dual n E)) mu
      (fun Z => -curryF n beta lam a sigma reward h0 h1 m0 m1 gate X Z)) :
    ∃ Y S : Blocks n E → (Fin (n + 1) → E),
      (∀ (X : Blocks n E) (yy ss : Fin (n + 1) → E),
        family n beta lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
          family n beta lam a sigma reward h0 h1 m0 m1 gate X.ofLp (Y X) (S X)) ∧
      Differentiable ℝ (exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S) ∧
      (∀ X, exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X =
        sSup (Set.range (curryF n beta lam a sigma reward h0 h1 m0 m1 gate X))) := by
  have h2 := second_jet_bound_from_gradient_rate (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) L hL.le hGrad
  have h2Lip : ∀ x y,
      ‖iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) x -
        iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) y‖ ≤ rho * ‖x - y‖ := by
    intro x y
    rw [second_jet_difference_eq_hessian]
    exact hHess x y
  obtain ⟨hF, hFG, hFH⟩ := actual_flat_class_gives_value_layout n beta lam a sigma reward L rho
    h0 h1 m0 m1 gate hL.le hrho hJ h2 h2Lip
  obtain ⟨Y, S, hMax, hDiff⟩ := actual_joint_class_supplies_value_interfaces n beta lam a sigma reward L mu
    h0 h1 m0 m1 gate hL hmu hF hFG hSC
  exact ⟨Y, S, hMax, hDiff, exactValue_eq_actual_sSup n beta lam a sigma reward h0 h1 m0 m1 gate Y S hMax⟩

end
end FangqingFlatRelayValueInterfaces
end

section
-- Source component: ActualShellOriginJets.lean

open scoped Topology ContDiff

namespace FangqingActualShellOriginJets

open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  FangqingShellMinimizerTransfer

noncomputable section

set_option maxHeartbeats 2100000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem subtract_norm_quad_origin_gradient
    (H : E → ℝ) (g : E) (hH : HasGradientAt H g 0) (c : ℝ) :
    HasGradientAt (fun z => H z - c / 2 * ‖z‖ ^ 2) g 0 := by
  have hn : HasFDerivAt (𝕜 := ℝ) (fun z : E => c / 2 * ‖z‖ ^ 2) (0 : E →L[ℝ] ℝ) (0 : E) := by
    convert! ((hasFDerivAt_id (𝕜 := ℝ) (0 : E)).norm_sq.const_mul (c / 2)) using 1 <;> ext v <;> simp
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hH.hasFDerivAt.sub hn using 1 <;> simp

theorem actual_paired_shell_origin_gradients (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain c : ℝ) (handle : E)
    (hR : 0 < R) (hA : 0 < A) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t)
    (hC0 : ContDiff ℝ 2 (inactiveShell Q g R gain))
    (hMin0 : ∀ y, inactiveShell Q g R gain 0 ≤ inactiveShell Q g R gain y) :
    let H0 := inactiveShell Q g R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A (s * A) handle z
    HasGradientAt H0 0 0 ∧ HasGradientAt (fun z => H0 z - c / 2 * ‖z‖ ^ 2) 0 0 ∧
    HasGradientAt H1 ((-s) • handle) 0 ∧
      HasGradientAt (fun z => H1 z - c / 2 * ‖z‖ ^ 2) ((-s) • handle) 0 := by
  intro H0 H1
  have hH0 : HasGradientAt H0 0 0 := by
    have hh := (hC0.differentiable (by norm_num) 0).hasGradientAt
    rw [PacketCore.gradient_eq_zero_at_global_min H0 0 hMin0] at hh
    exact hh
  have hr1 := actual_active_shell_eventually_eq_raw Q g phi R A s gain hR hA handle 0 hh hphi
    (by simpa using hR) (by simpa using hA)
  have hr0 := actual_active_shell_eventually_eq_raw Q g phi R A 0 gain hR hA handle 0 hh hphi
    (by simpa using hR) (by simpa using hA)
  have heq : H1 =ᶠ[𝓝 (0 : E)] (fun z => H0 z - s * inner ℝ handle z) := by
    filter_upwards [hr1, hr0] with z hz1 hz0
    have hz0' : H0 z = Q z + g z := by
      simpa only [H0, zero_mul, localizedSeed, mul_zero, zero_mul, sub_zero] using hz0
    change inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z = _
    rw [hz1, hz0']
  have hlinear : HasGradientAt (fun z : E => s * inner ℝ handle z) (s • handle) 0 := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert! (s • innerSL ℝ handle).hasFDerivAt (x := (0 : E)) using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply, inner_smul_left, RCLike.conj_to_real]
  have hH1 : HasGradientAt H1 ((-s) • handle) 0 := by
    have hh' : HasGradientAt (fun z : E => H0 z - s * inner ℝ handle z) ((-s) • handle) 0 := by
      rw [hasGradientAt_iff_hasFDerivAt]
      convert! hH0.hasFDerivAt.sub hlinear.hasFDerivAt using 1 <;> simp
    exact hh'.congr_of_eventuallyEq heq
  exact ⟨hH0, subtract_norm_quad_origin_gradient H0 0 hH0 c,
    hH1, subtract_norm_quad_origin_gradient H1 ((-s) • handle) hH1 c⟩

end
end FangqingActualShellOriginJets
end

section
-- Source component: EndpointInitializationBounds.lean

namespace FangqingEndpointInitializationBounds

open FangqingRelayStationarity

noncomputable section

set_option maxHeartbeats 2200000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inactive_endpoint_origin_max (h : E → ℝ) (d beta lam : ℝ)
    (hd : 0 ≤ d) (hsc : StrongConvexOn (Set.univ : Set E) d h)
    (hc : Differentiable ℝ h) (hg : gradient h 0 = 0) (y : E) :
    endpoint beta lam h (h 0) 0 y ≤ 0 := by
  have hs := PacketCore.strongConvex_support h d hsc hc 0 y
  simp only [sub_zero, hg, inner_zero_left, zero_add] at hs
  have hn : 0 ≤ d / 2 * ‖y‖ ^ 2 := by positivity
  simp only [endpoint, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero,
    inner_zero_left, zero_sub, zero_add]
  linarith only [hs, hn]

theorem active_endpoint_initial_upper (h : E → ℝ) (d beta lam m seed : ℝ) (handle : E)
    (hd : 0 ≤ d) (hb : 0 ≤ beta) (hlam : lam ≠ 0) (hh : ‖handle‖ ≤ 1)
    (hsc : StrongConvexOn (Set.univ : Set E) d h) (hc : Differentiable ℝ h)
    (hg : gradient h 0 = (-seed) • handle) (hm : m ≤ h 0) (y : E) :
    endpoint beta lam h m ((-(seed / lam)) • handle) y ≤ beta / (2 * lam ^ 2) * seed ^ 2 := by
  let x : E := (-(seed / lam)) • handle
  have hi : lam * inner ℝ x y = inner ℝ (gradient h 0) y := by
    rw [hg]
    dsimp [x]
    simp only [real_inner_smul_left]
    field_simp
    <;> ring
  have hs := PacketCore.strongConvex_support h d hsc hc 0 y
  simp only [sub_zero] at hs
  have hn : 0 ≤ d / 2 * ‖y‖ ^ 2 := by positivity
  have hUpper : endpoint beta lam h m x y ≤ beta / 2 * ‖x‖ ^ 2 := by
    unfold endpoint
    rw [hi]
    linarith only [hs, hm, hn]
  have hh2 : ‖handle‖ ^ 2 ≤ 1 := by nlinarith only [hh, norm_nonneg handle]
  have hx2 : ‖x‖ ^ 2 ≤ (seed / lam) ^ 2 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, neg_sq]
    nlinarith only [mul_le_mul_of_nonneg_left hh2 (sq_nonneg (seed / lam))]
  have hscale := mul_le_mul_of_nonneg_left hx2 (by positivity : 0 ≤ beta / 2)
  apply hUpper.trans
  convert! hscale using 1 <;> field_simp [hlam] <;> ring

variable [FiniteDimensional ℝ E]

theorem actual_endpoint_local_values (n : ℕ) (d beta lam seed : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (handle : E)
    (hd : 0 < d) (hb : 0 ≤ beta) (hlam : lam ≠ 0) (hh : ‖handle‖ ≤ 1)
    (hc0 : ∀ t, Differentiable ℝ (h0 t)) (hc1 : ∀ t, Differentiable ℝ (h1 t))
    (hs0 : ∀ t, StrongConvexOn (Set.univ : Set E) d (h0 t))
    (hs1 : ∀ t, StrongConvexOn (Set.univ : Set E) d (h1 t))
    (hg0 : ∀ t, gradient (h0 t) 0 = 0)
    (hm0 : ∀ t, m0 t = h0 t 0)
    (hg1 : gradient (h1 0) 0 = (-seed) • handle) (hm1 : m1 0 ≤ h1 0 0) :
    ∃ (Y0 Y1 : Fin (n + 1) → E → E) (P0 P1 : Fin (n + 1) → E → ℝ),
      (∀ t x y, endpoint beta lam (h0 t) (m0 t) x y ≤ P0 t x) ∧
      (∀ t x y, endpoint beta lam (h1 t) (m1 t) x y ≤ P1 t x) ∧
      (∀ t x, endpoint beta lam (h0 t) (m0 t) x (Y0 t x) = P0 t x) ∧
      (∀ t x, endpoint beta lam (h1 t) (m1 t) x (Y1 t x) = P1 t x) ∧
      (∀ t x, 0 ≤ P0 t x) ∧ (∀ t, P0 t 0 = 0) ∧
      P1 0 ((-(seed / lam)) • handle) ≤ beta / (2 * lam ^ 2) * seed ^ 2 := by
  have hex0 : ∀ t x, ∃ y : E, ∀ z : E,
      endpoint beta lam (h0 t) (m0 t) x z ≤ endpoint beta lam (h0 t) (m0 t) x y := by
    intro t x
    simpa only [PacketCore.saddleValue, endpoint, zero_div, zero_mul, sub_zero, add_zero]
      using PacketCore.exists_inner_maximizer_finiteDimensional (h0 t) d beta 0 lam (m0 t) hd
        (by simpa using hs0 t) (hc0 t) x
  have hex1 : ∀ t x, ∃ y : E, ∀ z : E,
      endpoint beta lam (h1 t) (m1 t) x z ≤ endpoint beta lam (h1 t) (m1 t) x y := by
    intro t x
    simpa only [PacketCore.saddleValue, endpoint, zero_div, zero_mul, sub_zero, add_zero]
      using PacketCore.exists_inner_maximizer_finiteDimensional (h1 t) d beta 0 lam (m1 t) hd
        (by simpa using hs1 t) (hc1 t) x
  choose Y0 hY0 using hex0
  choose Y1 hY1 using hex1
  let P0 := fun t x => endpoint beta lam (h0 t) (m0 t) x (Y0 t x)
  let P1 := fun t x => endpoint beta lam (h1 t) (m1 t) x (Y1 t x)
  refine ⟨Y0, Y1, P0, P1, hY0, hY1, (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro t x
    have hh := hY0 t x 0
    have hbase : 0 ≤ endpoint beta lam (h0 t) (m0 t) x 0 := by
      simp only [endpoint, inner_zero_right, mul_zero, hm0 t]
      have hn : 0 ≤ beta / 2 * ‖x‖ ^ 2 := by positivity
      nlinarith only [hn]
    exact hbase.trans hh
  · intro t
    apply le_antisymm
    · change endpoint beta lam (h0 t) (m0 t) 0 (Y0 t 0) ≤ 0
      rw [hm0 t]
      exact inactive_endpoint_origin_max (h0 t) d beta lam hd.le (hs0 t) (hc0 t) (hg0 t) _
    · have hh := hY0 t 0 0
      change 0 ≤ endpoint beta lam (h0 t) (m0 t) 0 (Y0 t 0)
      have he0 : endpoint beta lam (h0 t) (m0 t) 0 0 = 0 := by
        simp [endpoint, hm0 t]
      rw [he0] at hh
      exact hh
  · exact active_endpoint_initial_upper (h1 0) d beta lam (m1 0) seed handle hd.le hb hlam hh
      (hs1 0) (hc1 0) hg1 hm1 _

end
end FangqingEndpointInitializationBounds
end

section
-- Source component: RelayGap.lean

open scoped BigOperators

namespace FangqingRelayGap

open FangqingRelayStationarity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem family_base_eq (n : ℕ) (β lam : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (x y : Fin (n + 1) → E) :
    (∑ t, endpoint β lam (h0 t) (m0 t) (x t) (y t)) +
      delta (h0 0) (h1 0) (m0 0) (m1 0) (y 0) =
    endpoint β lam (h1 0) (m1 0) (x 0) (y 0) +
      ∑ j : Fin n, endpoint β lam (h0 j.succ) (m0 j.succ) (x j.succ) (y j.succ) := by
  rw [Fin.sum_univ_succ]
  dsimp only [endpoint, delta]
  ring

theorem family_upper_by_endpoints (n : ℕ) (β lam a sigma reward M : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (hsigma : 0 ≤ sigma) (hM : 0 ≤ M) (hreward : M ≤ reward)
    (hgate : ∀ j z, 0 ≤ gate j z)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M) :
    family n β lam a sigma reward h0 h1 m0 m1 gate x y s ≤
      endpoint β lam (h1 0) (m1 0) (x 0) (y 0) +
        ∑ j : Fin n, endpoint β lam (h0 j.succ) (m0 j.succ) (x j.succ) (y j.succ) := by
  have hg : (∑ t, gateExt n gate t (s t) * coefficient n reward h0 h1 m0 m1 y t) ≤ 0 := by
    apply Finset.sum_nonpos
    intro t ht
    have htgate : 0 ≤ gateExt n gate t (s t) := by
      refine Fin.lastCases ?_ (fun j => ?_) t
      · simp [gateExt]
      · simpa [gateExt] using hgate j (s j.castSucc)
    exact mul_nonpos_of_nonneg_of_nonpos htgate
      (coefficient_bounds n reward M h0 h1 m0 m1 y hM hreward hdelta t).2
  have hq : 0 ≤ sigma / 2 * (∑ t, ‖s t - a • x t‖ ^ 2) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  rw [family_gate_sum, family_base_eq]
  linarith only [hg, hq]

theorem incoming_bounds (n : ℕ) (gate : Fin n → E → ℝ)
    (hgate : ∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1)
    (s : Fin (n + 1) → E) (t : Fin (n + 1)) :
    0 ≤ incoming n gate s t ∧ incoming n gate s t ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) t
  · norm_num [incoming]
  · simpa [incoming] using hgate j (s j.castSucc)

theorem family_lower_at_zero_relay (n : ℕ) (β lam a sigma reward M : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y : Fin (n + 1) → E)
    (hM : 0 ≤ M) (hreward : 0 ≤ reward)
    (hgate : ∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (hlocal : ∀ t, 0 ≤ endpoint β lam (h0 t) (m0 t) (x t) (y t)) :
    -((n + 1 : ℕ) : ℝ) * (M + reward) ≤
      family n β lam a sigma reward h0 h1 m0 m1 gate x y (fun t => a • x t) := by
  have hterm : ∀ t : Fin (n + 1), -M ≤
      endpoint β lam (h0 t) (m0 t) (x t) (y t) +
      incoming n gate (fun j => a • x j) t *
        delta (h0 t) (h1 t) (m0 t) (m1 t) (y t) := by
    intro t
    have hin := incoming_bounds n gate hgate (fun j => a • x j) t
    have hd := (abs_le.mp (hdelta t (y t))).1
    have hmul := mul_le_mul_of_nonneg_left hd hin.1
    have hMterm := mul_le_mul_of_nonneg_left hin.2 hM
    nlinarith only [hmul, hMterm, hlocal t]
  have hsum := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Fin (n + 1)))) => hterm t)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hgsum : (∑ j : Fin n, gate j (a • x j.castSucc)) ≤ n := by
    have h := Finset.sum_le_sum
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => (hgate j (a • x j.castSucc)).2)
    simpa using h
  have hrewardSum := mul_le_mul_of_nonneg_left hgsum hreward
  unfold family
  simp only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, sub_zero]
  push_cast at *
  nlinarith only [hsum, hrewardSum, hreward]

theorem exact_relay_gap (n : ℕ) (β lam a sigma reward M firstGap : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ)
    (Y S : Blocks n E → (Fin (n + 1) → E))
    (Y0 : Fin (n + 1) → E → E) (P0 P1 : Fin (n + 1) → E → ℝ)
    (hsigma : 0 ≤ sigma) (hM : 0 ≤ M) (hreward : M ≤ reward)
    (hgate : ∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (hP0 : ∀ t x y, endpoint β lam (h0 t) (m0 t) x y ≤ P0 t x)
    (hP1 : ∀ t x y, endpoint β lam (h1 t) (m1 t) x y ≤ P1 t x)
    (hY0 : ∀ t x, endpoint β lam (h0 t) (m0 t) x (Y0 t x) = P0 t x)
    (hPnonneg : ∀ t x, 0 ≤ P0 t x)
    (hmax : ∀ (Z : Blocks n E) (yy ss : Fin (n + 1) → E),
      family n β lam a sigma reward h0 h1 m0 m1 gate Z.ofLp yy ss ≤
        exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S Z)
    (X0 : Blocks n E)
    (hinitInactive : ∀ j : Fin n, P0 j.succ (X0 j.succ) = 0)
    (hinitFirst : P1 0 (X0 0) ≤ firstGap) :
    let Phi := exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S
    (∀ Z, -((n + 1 : ℕ) : ℝ) * (M + reward) ≤ Phi Z) ∧
      Phi X0 ≤ firstGap ∧
      Phi X0 - sInf (Set.range Phi) ≤ firstGap + ((n + 1 : ℕ) : ℝ) * (M + reward) := by
  let Phi := exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S
  have hlower : ∀ Z : Blocks n E, -((n + 1 : ℕ) : ℝ) * (M + reward) ≤ Phi Z := by
    intro Z
    have h := family_lower_at_zero_relay n β lam a sigma reward M h0 h1 m0 m1 gate Z.ofLp
      (fun t => Y0 t (Z t)) hM (hM.trans hreward) hgate hdelta
      (fun t => by rw [hY0]; exact hPnonneg t (Z t))
    exact h.trans (hmax Z (fun t => Y0 t (Z t)) (fun t => a • Z t))
  have hupper : Phi X0 ≤ firstGap := by
    have h := family_upper_by_endpoints n β lam a sigma reward M h0 h1 m0 m1 gate
      X0.ofLp (Y X0) (S X0) hsigma hM hreward (fun j z => (hgate j z).1) hdelta
    have hi : (∑ j : Fin n,
        endpoint β lam (h0 j.succ) (m0 j.succ) (X0 j.succ) (Y X0 j.succ)) ≤ 0 := by
      apply Finset.sum_nonpos
      intro j hj
      exact (hP0 j.succ (X0 j.succ) (Y X0 j.succ)).trans (hinitInactive j).le
    have hf := (hP1 0 (X0 0) (Y X0 0)).trans hinitFirst
    change family n β lam a sigma reward h0 h1 m0 m1 gate X0.ofLp (Y X0) (S X0) ≤ firstGap
    linarith only [h, hi, hf]
  refine ⟨hlower, hupper, ?_⟩
  have hnonempty : (Set.range Phi).Nonempty := ⟨Phi X0, Set.mem_range_self X0⟩
  have hinf : -((n + 1 : ℕ) : ℝ) * (M + reward) ≤ sInf (Set.range Phi) := by
    apply le_csInf hnonempty
    intro v hv
    rcases hv with ⟨Z, rfl⟩
    exact hlower Z
  linarith only [hupper, hinf]

end
end FangqingRelayGap
end

section
-- Source component: RelayInitialGapScalars.lean

namespace FangqingRelayInitialGapScalars

open FangqingActualRelayScaling

noncomputable section

set_option maxHeartbeats 1500000

def firstGap (Cs L mu KD eps : ℝ) : ℝ :=
  L / (2 * lam L mu ^ 2) * (Cs * (8 * mu) * packetD L mu KD eps) ^ 2

theorem actual_first_gap_identity (Cs L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu) :
    firstGap Cs L mu KD eps = 32 * Cs ^ 2 * KD ^ 2 * energy L eps := by
  have hlam : lam L mu ^ 2 = L * mu := Real.sq_sqrt (by positivity)
  have hraw := rawBudget_eq (32 * Cs ^ 2) 1 L mu KD eps hL hmu
  have heq : firstGap Cs L mu KD eps = rawBudget (32 * Cs ^ 2) 1 L mu KD eps := by
    unfold firstGap rawBudget
    rw [hlam]
    field_simp
    <;> ring
  rw [heq, hraw]
  ring

theorem actual_total_relay_gap_budget (Cs C L mu KD eps : ℝ) (n : ℕ)
    (hL : 0 < L) (hmu : 0 < mu) (hC : 0 ≤ C) :
    firstGap Cs L mu KD eps + ((n + 1 : ℕ) : ℝ) * totalBudget C 8 L mu KD eps ≤
      (32 * Cs ^ 2 * KD ^ 2 + 24 * C * KD ^ 2 + 1) * ((n + 1 : ℕ) : ℝ) * energy L eps := by
  rw [actual_first_gap_identity Cs L mu KD eps hL hmu, totalBudget_eq C 8 L mu KD eps hL hmu]
  have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hfirst : 0 ≤ 32 * Cs ^ 2 * KD ^ 2 * energy L eps := by unfold energy; positivity
  have hh := mul_le_mul_of_nonneg_right hn hfirst
  nlinarith only [hh]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem actual_initial_displacement (Cs L mu KD eps : ℝ) (handle : E)
    (hCs : 0 ≤ Cs) (hL : 0 < L) (hmu : 0 < mu) (hKD : 0 < KD) (heps : 0 < eps) (hh : ‖handle‖ ≤ 1) :
    ‖(-(Cs * (8 * mu) * packetD L mu KD eps / lam L mu)) • handle‖ ≤
      8 * Cs * width L mu KD eps := by
  have hlam : 0 < lam L mu := by unfold lam; positivity
  have hD : 0 < packetD L mu KD eps := by unfold packetD; positivity
  have hcoef : Cs * (8 * mu) * packetD L mu KD eps / lam L mu = 8 * Cs * width L mu KD eps := by
    unfold width
    have hsq : lam L mu ^ 2 = L * mu := Real.sq_sqrt (by positivity)
    field_simp [hlam.ne', hL.ne']
    rw [hsq]
    ring
  have he : 0 < width L mu KD eps := by rw [width_eq_actual _ _ _ _ hL hmu]; positivity
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), hcoef]
  exact mul_le_of_le_one_right (by positivity) hh

end
end FangqingRelayInitialGapScalars
end

section
-- Source component: PhysicalRelayValueGap.lean

open scoped ContDiff

namespace FangqingPhysicalRelayValueGap

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingPhysicalRelayMasterData FangqingActualShellOriginJets
  FangqingEndpointInitializationBounds FangqingFlatRelayValueInterfaces FangqingRelayInitialGapScalars
  FangqingRelayStationarity

noncomputable section

set_option maxHeartbeats 7000000

universe u

theorem actual_physical_relay_value_gap
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw KDlower : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      4 * Ctheta * (3 * Cdelta * 8 + 1) ≤ csigma ∧ 0 ≤ Cgap ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
      (tail : Fin (outer + 1) → Fin (nt + 2) → W)
      (L mu eps r delta omega q scale lam0 : ℝ),
      (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
      0 < mu → mu ≤ L → 0 < eps → 1 ≤ r → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam0 → omega = Cw * lam0 * q ^ 2 → ((nt + 2 : ℕ) : ℝ) ≤ Cm * q →
      scale * lam0 = 8 * mu → distanceScale q omega = packetD L mu KD eps →
      let nu := scale * lam0
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
      let A := CA * D
      let R := 2 * A
      let s := Cs * nu * D
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let H0 := fun t => inactiveShell (QPhysical q nu C)
        (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
      let H1 := fun t z => H0 t z - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) z
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
        (∀ t, AnalyticClass (H0 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
        (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
        (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
        (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
          3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
        ∀ center : Fin outer → PhysicalSpace A0 B0 W,
        let a := relayAmplitude 1 (L / mu) r
        let ell := width L mu KD eps
        let rw := reward Cdelta 8 L KD eps
        let h0 := fun t => reduced (H0 t) mu
        let h1 := fun t => reduced (H1 t) mu
        let m0 := fun t => H0 t 0
        let m1 := fun t => H1 t (Z t)
        let gate := fun j => scaledGate theta (a * ell) (center j)
        let J := assembled outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate
        (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ rawBudget Cdelta 8 L mu KD eps) ∧
        (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
        ((rw + rawBudget Cdelta 8 L mu KD eps) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma L a csigma / 2) ∧
        ContDiff ℝ 2 J ∧
        (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + CL * nu * q ^ 2) * ‖x - y‖) ∧
        FangqingRelayGlobalJointClass.HessianRate J (Crho * scale + rho L mu eps r / 4) ∧
        (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual outer (PhysicalSpace A0 B0 W))) mu
          (FangqingRelayDualAssembly.negativeFamily outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) ∧
        ∃ Y S : FangqingRelayStationarity.Blocks outer (PhysicalSpace A0 B0 W) → (Fin (outer + 1) → PhysicalSpace A0 B0 W),
          (∀ (X : FangqingRelayStationarity.Blocks outer (PhysicalSpace A0 B0 W)) yy ss,
            FangqingRelayStationarity.family outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate X.ofLp yy ss ≤
              FangqingRelayStationarity.exactValue outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate Y S X) ∧
          Differentiable ℝ (FangqingRelayStationarity.exactValue outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate Y S) ∧
          (∀ X, FangqingRelayStationarity.exactValue outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate Y S X =
            sSup (Set.range (FangqingRelayValueBridge.curryF outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate X))) ∧
          let X0 : FangqingRelayStationarity.Blocks outer (PhysicalSpace A0 B0 W) :=
            WithLp.toLp 2 (Fin.cons ((-(s / lam L mu)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
          let Phi := FangqingRelayStationarity.exactValue outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate Y S
          Phi X0 - sInf (Set.range Phi) ≤ Cgap * ((outer + 1 : ℕ) : ℝ) * energy L eps := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
      hCD, hCt, hThetaDeriv, hExtra, hBuilder⟩ :=
    actual_physical_relay_master_data.{u} P phi Bp left right Cm Cw KDlower hCm hCw hKDlower hp hl hr hcore
  let Cgap := 32 * (2 * Cw) ^ 2 * KD ^ 2 + 24 * Cdelta * KD ^ 2 + 1
  have hGap : 0 ≤ Cgap := by dsimp [Cgap]; positivity
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hThetaDeriv, hExtra, hGap, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r delta omega q scale lam0 hh ht hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
    nu D Cs CA A R s M gain H0 H1 CL Crho
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail L mu eps r delta omega q scale lam0 hh ht
      hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
  refine ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, ?_⟩
  intro center a ell rw h0 h1 m0 m1 gate J
  obtain ⟨hDelta, hRange, hSmall, hJ, hGrad, hHess, hSC⟩ := hCenters center
  refine ⟨hDelta, hRange, hSmall, hJ, hGrad, hHess, hSC, ?_⟩
  have hL : 0 < L := hmu.trans_le hLmu
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hNu : 0 < nu := mul_pos hscale hlam0
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCA : 1 ≤ CA := by
    have h1 : 0 ≤ 2 * Ks * Cs := by positivity
    have h2 : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
    dsimp [CA]
    linarith only [h1, h2]
  have hDA : D ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hCA hD.le
    simpa only [one_mul] using hh
  have hA : 0 < A := hD.trans_le hDA
  have hR : 0 < R := by dsimp [R]; positivity
  have hCL : 0 < CL := by dsimp [CL]; positivity
  have hCrho : 0 ≤ Crho := by dsimp [Crho]; positivity
  have hLg : 0 < Cglobal * L + CL * nu * q ^ 2 := by positivity
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hRho : 0 ≤ Crho * scale + rho L mu eps r / 4 := by unfold rho; positivity
  have hSCcurry : ∀ X : Blocks outer (PhysicalSpace A0 B0 W), StrongConvexOn
      (Set.univ : Set (FangqingRelayValueBridge.Dual outer (PhysicalSpace A0 B0 W))) mu
      (fun z => -FangqingRelayValueBridge.curryF outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate X z) := by
    intro X
    exact hSC X.ofLp
  obtain ⟨Y, S, hMax, hDiff, hSup⟩ := actual_flat_class_supplies_exact_value outer L (lam L mu) a
    (sigma L a csigma) rw (Cglobal * L + CL * nu * q ^ 2) mu (Crho * scale + rho L mu eps r / 4)
    h0 h1 m0 m1 gate hLg hmu hRho hJ hGrad hHess hSCcurry
  refine ⟨Y, S, hMax, hDiff, hSup, ?_⟩
  intro X0 Phi
  have hHandle : ∀ t, ‖mkPhysical (h t) (0 : B0) (0 : W)‖ ≤ 1 := by
    intro t
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical (h t) (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h t, (0 : B0)))
    change ‖mkPhysical (h t) (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h t, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h t, (0 : B0))‖ ^ 2 = ‖h t‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh t, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical (h t) (0 : B0) (0 : W))]
  have hOrig := fun t => actual_paired_shell_origin_gradients (QPhysical q nu C)
    (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z)
    phi R A s gain mu (mkPhysical (h t) 0 0) hR hA (hHandle t) hcore (hH0 t).1 (hMin0 t)
  have h0diff : ∀ t, Differentiable ℝ (h0 t) := by
    intro t
    exact ((hH0 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ))).differentiable (by norm_num)
  have h1diff : ∀ t, Differentiable ℝ (h1 t) := by
    intro t
    exact ((hH1 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ))).differentiable (by norm_num)
  have h0sc : ∀ t, StrongConvexOn (Set.univ : Set (PhysicalSpace A0 B0 W)) (3 * mu) (h0 t) := by
    intro t
    convert! reduced_strongConvex (H0 t) (4 * mu) mu (hH0 t).2.1 using 1 <;> ring
  have h1sc : ∀ t, StrongConvexOn (Set.univ : Set (PhysicalSpace A0 B0 W)) (3 * mu) (h1 t) := by
    intro t
    convert! reduced_strongConvex (H1 t) (4 * mu) mu (hH1 t).2.1 using 1 <;> ring
  have hm0 : ∀ t, m0 t = h0 t 0 := by intro t; simp only [m0, h0, reduced, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
  have hm1 : m1 0 ≤ h1 0 0 := by
    have hh := hMin1 0 0
    simpa only [m1, h1, reduced, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero] using hh
  have hlam : 0 < lam L mu := by unfold lam; positivity
  obtain ⟨Y0, Y1, P0, P1, hP0, hP1, hY0, hY1, hNonneg, hPzero, hFirst⟩ :=
    actual_endpoint_local_values outer (3 * mu) L (lam L mu) s h0 h1 m0 m1 (mkPhysical (h 0) 0 0)
      (by positivity) hL.le hlam.ne' (hHandle 0) h0diff h1diff h0sc h1sc
      (fun t => (hOrig t).2.1.gradient) hm0 (hOrig 0).2.2.2.gradient hm1
  let Md := rawBudget Cdelta 8 L mu KD eps
  let first := L / (2 * lam L mu ^ 2) * s ^ 2
  have hMd : 0 ≤ Md := by dsimp [Md, rawBudget]; positivity
  have hRw : Md ≤ rw := by
    have heq := reward_eq_two_raw_plus_energy Cdelta 8 L mu KD eps hL hmu
    change Md ≤ reward Cdelta 8 L KD eps
    rw [heq]
    have he : 0 ≤ energy L eps := by unfold energy; positivity
    linarith only [he, hMd]
  have hInit0 : ∀ j : Fin outer, P0 j.succ (X0 j.succ) = 0 := by
    intro j
    simpa only [X0, PiLp.toLp_apply, Fin.cons_succ] using hPzero j.succ
  have hInit1 : P1 0 (X0 0) ≤ first := by
    simpa only [X0, PiLp.toLp_apply, Fin.cons_zero, first] using hFirst
  have hSig : 0 ≤ sigma L a csigma := by unfold sigma; positivity
  have hgap := FangqingRelayGap.exact_relay_gap outer L (lam L mu) a (sigma L a csigma) rw Md first
    h0 h1 m0 m1 gate Y S Y0 P0 P1 hSig hMd hRw hRange hDelta hP0 hP1 hY0 hNonneg hMax X0 hInit0 hInit1
  have hFirstEq : first = firstGap Cs L mu KD eps := by
    dsimp [first, firstGap]
    change L / (2 * lam L mu ^ 2) * (Cs * nu * D) ^ 2 = _
    rw [show nu = 8 * mu from hnu, show D = packetD L mu KD eps from hDistance]
  calc
    Phi X0 - sInf (Set.range Phi) ≤ first + ((outer + 1 : ℕ) : ℝ) * (Md + rw) := hgap.2.2
    _ = firstGap Cs L mu KD eps + ((outer + 1 : ℕ) : ℝ) * totalBudget Cdelta 8 L mu KD eps := by
      rw [hFirstEq]
      rfl
    _ ≤ (32 * Cs ^ 2 * KD ^ 2 + 24 * Cdelta * KD ^ 2 + 1) * ((outer + 1 : ℕ) : ℝ) * energy L eps :=
      actual_total_relay_gap_budget Cs Cdelta L mu KD eps outer hL hmu hCD
    _ = _ := rfl

end
end FangqingPhysicalRelayValueGap
end

section
-- Source component: RelayExternalSlackBudgets.lean

namespace FangqingRelayExternalSlackBudgets

open FangqingThirdGroupScaling

noncomputable section

set_option maxHeartbeats 2200000

theorem universal_external_reserves (Cglobal Cp Crho : ℝ)
    (hG : 0 ≤ Cglobal) (hP : 0 ≤ Cp) (hR : 0 ≤ Crho) :
    ∃ cL cq cg : ℝ, 0 < cL ∧ cL ≤ 1 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧
      (∀ L mu q : ℝ, 0 < mu → 0 < L → 1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) →
        mu ≤ cL * L ∧ Cp * (8 * mu) * q ^ 2 ≤ cL * L ∧
        Cglobal * (cL * L) + Cp * (8 * mu) * q ^ 2 ≤ L / 2) ∧
      (∀ rhop rho : ℝ, 0 ≤ rhop → rhop ≤ rho →
        Crho * (cg * rhop) + rho / 4 ≤ rho / 2) := by
  let cL := 1 / (2 * (Cglobal + 1))
  let cq := Real.sqrt (cL / (8 * Cp + 1))
  let cg := 1 / (4 * (Crho + 1))
  have hcL : 0 < cL := by dsimp [cL]; positivity
  have hcL1 : cL ≤ 1 := by
    dsimp [cL]
    apply (div_le_iff₀ (by positivity : 0 < 2 * (Cglobal + 1))).mpr
    linarith only [hG]
  have hden : 0 < 8 * Cp + 1 := by positivity
  have hcq : 0 < cq := Real.sqrt_pos.mpr (div_pos hcL hden)
  have hcq2 : cq ^ 2 = cL / (8 * Cp + 1) := Real.sq_sqrt (by positivity)
  have hq2L : cq ^ 2 ≤ cL := by
    rw [hcq2]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [mul_nonneg hcL.le hP]
  have hcq1 : cq ≤ 1 := by nlinarith only [hcq.le, hq2L.trans hcL1]
  have hCpq : 8 * Cp * cq ^ 2 ≤ cL := by
    rw [hcq2, ← mul_div_assoc]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hcL.le]
  have hcg : 0 < cg := by dsimp [cg]; positivity
  have hcg1 : cg ≤ 1 := by
    dsimp [cg]
    apply (div_le_iff₀ (by positivity : 0 < 4 * (Crho + 1))).mpr
    linarith only [hR]
  have hCrho : Crho * cg ≤ 1 / 4 := by
    dsimp [cg]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
    field_simp
    linarith
  refine ⟨cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_, ?_⟩
  · intro L mu q hmu hL hq hqb
    have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
    have hscale := mul_le_mul_of_nonneg_left hqb hmu.le
    have hmq : mu * q ^ 2 ≤ cq ^ 2 * L := by
      convert! hscale using 1 <;> field_simp <;> ring
    have hbase := mul_le_mul_of_nonneg_left hq2 hmu.le
    have hCL := mul_le_mul_of_nonneg_right hq2L hL.le
    have hCp1 := mul_le_mul_of_nonneg_left hmq (by positivity : 0 ≤ 8 * Cp)
    have hCp2 := mul_le_mul_of_nonneg_right hCpq hL.le
    have hPacket : Cp * (8 * mu) * q ^ 2 ≤ cL * L := by nlinarith only [hCp1, hCp2]
    have hidentity : (Cglobal + 1) * cL = 1 / 2 := by dsimp [cL]; field_simp; try ring
    refine ⟨by nlinarith only [hbase, hmq, hCL], hPacket, ?_⟩
    have hsum := add_le_add (le_refl (Cglobal * (cL * L))) hPacket
    have heq : Cglobal * (cL * L) + cL * L = L / 2 := by nlinarith only [congrArg (fun t : ℝ => t * L) hidentity]
    exact hsum.trans heq.le
  · intro rhop rho hrhop hr
    have hrho : 0 ≤ rho := hrhop.trans hr
    have h1 := mul_le_mul_of_nonneg_left hr (mul_nonneg hR hcg.le)
    have h2 := mul_le_mul_of_nonneg_right hCrho hrho
    nlinarith only [h1, h2]

theorem internal_rho_matches_external (cL L mu eps r : ℝ)
    (hcL : 0 < cL) (hcL1 : cL ≤ 1) (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) (hr : 1 ≤ r) :
    1 ≤ r / Real.sqrt cL ∧
      rho (cL * L) mu eps (r / Real.sqrt cL) = rho L mu eps r := by
  have hs : 0 < Real.sqrt cL := Real.sqrt_pos.mpr hcL
  have hs1 : Real.sqrt cL ≤ 1 := by simpa using Real.sqrt_le_sqrt hcL1
  have hsq : Real.sqrt cL ^ 2 = cL := Real.sq_sqrt hcL.le
  have hkap : 0 < L / mu := div_pos hL hmu
  have hks : 0 < Real.sqrt (L / mu) := Real.sqrt_pos.mpr hkap
  refine ⟨(one_le_div hs).mpr (hs1.trans hr), ?_⟩
  have hkEq : cL * L / mu = cL * (L / mu) := by ring
  calc
    _ = rho L mu eps r * (cL / Real.sqrt cL ^ 2) := by
      unfold rho
      rw [hkEq, Real.sqrt_mul hcL.le]
      field_simp [ne_of_gt hcL, ne_of_gt hs, ne_of_gt hL, ne_of_gt hmu, ne_of_gt heps, ne_of_gt hks]
      <;> ring
    _ = _ := by rw [hsq, div_self hcL.ne', mul_one]

end
end FangqingRelayExternalSlackBudgets
end

section
-- Source component: ExternalPhysicalRelayValidity.lean

open scoped ContDiff

namespace FangqingExternalPhysicalRelayValidity

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingPhysicalRelayValueGap FangqingRelayExternalSlackBudgets
  FangqingRelayStationarity

noncomputable section

set_option maxHeartbeats 7500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def Validity (n : ℕ) (beta lam a sigma reward L mu rho M Ctheta ell Cgap Egap : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (X0 : Blocks n E) : Prop :=
  let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
  (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M) ∧
  (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
  ((reward + M) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma / 2) ∧
  ContDiff ℝ 2 J ∧
  (∀ x y, ‖gradient J x - gradient J y‖ ≤ L * ‖x - y‖) ∧
  FangqingRelayGlobalJointClass.HessianRate J rho ∧
  (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) mu
    (FangqingRelayDualAssembly.negativeFamily n beta lam a sigma reward h0 h1 m0 m1 gate x)) ∧
  ∃ Y S : Blocks n E → (Fin (n + 1) → E),
    (∀ (X : Blocks n E) yy ss,
      family n beta lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
        exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X) ∧
    Differentiable ℝ (exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S) ∧
    (∀ X, exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X =
      sSup (Set.range (FangqingRelayValueBridge.curryF n beta lam a sigma reward h0 h1 m0 m1 gate X))) ∧
    let Phi := exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S
    Phi X0 - sInf (Set.range Phi) ≤ Cgap * ((n + 1 : ℕ) : ℝ) * Egap

universe u

theorem actual_external_physical_relay_validity
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw KDlower : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Cgap ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      let Cs := 2 * Cw
      let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
      let Cp := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      ∃ cL cq cg : ℝ, 0 < cL ∧ cL ≤ 1 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧
      ∀ (A0 B0 W : Type u)
        [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
        [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
        (tail : Fin (outer + 1) → Fin (nt + 2) → W)
        (L mu eps r rhop q delta omega : ℝ),
        (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
        0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
        1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) → 0 < delta → delta ≤ omega →
        ((nt + 2 : ℕ) : ℝ) ≤ Cm * q →
        let Li := cL * L
        let ri := r / Real.sqrt cL
        let scale := cg * rhop
        let barlam := (8 * mu) / scale
        omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mu KD eps →
        let nu := scale * barlam
        let D := distanceScale q omega
        let A := CA * D
        let R := 2 * A
        let seed := Cs * nu * D
        let Mpath : ℝ := (4 * Ce : ℝ) * scale * omega
        let gain := (16 * K + 1) * Mpath
        let H0 := fun t => inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
        let H1 := fun t z => H0 t z - localizedSeed theta phi R A (seed * A) (mkPhysical (h t) 0 0) z
        ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
          (∀ t, AnalyticClass (H0 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t, AnalyticClass (H1 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
          (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
          (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
          (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
            3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
          ∀ center : Fin outer → PhysicalSpace A0 B0 W,
          let a := relayAmplitude 1 (Li / mu) ri
          let ell := width Li mu KD eps
          let rw := reward Cdelta 8 Li KD eps
          let h0 := fun t => reduced (H0 t) mu
          let h1 := fun t => reduced (H1 t) mu
          let m0 := fun t => H0 t 0
          let m1 := fun t => H1 t (Z t)
          let gate := fun j => scaledGate theta (a * ell) (center j)
          let X0 : Blocks outer (PhysicalSpace A0 B0 W) :=
            WithLp.toLp 2 (Fin.cons ((-(seed / lam Li mu)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
          Validity outer Li (lam Li mu) a (sigma Li a csigma) rw L mu (rho L mu eps r)
            (rawBudget Cdelta 8 Li mu KD eps) Ctheta ell Cgap (energy L eps) h0 h1 m0 m1 gate X0 := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap0, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
      hCD, hCt, hThetaDeriv, hExtra, hGap0, hBuilder⟩ :=
    actual_physical_relay_value_gap.{u} P phi Bp left right Cm Cw KDlower hCm hCw hKDlower hp hl hr hcore
  let Cs := 2 * Cw
  let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
  let Cp := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
  let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCrho : 0 ≤ Crho := by dsimp [Crho]; positivity
  obtain ⟨cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, hBudget, hHessianBudget⟩ :=
    universal_external_reserves Cglobal Cp Crho hCG hCp hCrho
  let Cgap := Cgap0 / cL
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, (by dsimp [Cgap]; positivity), hThetaDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r rhop q delta omega hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn
    Li ri scale barlam homega hDistance nu D A R seed Mpath gain H0 H1
  obtain ⟨hMuLi, hPacket, hTotalGrad⟩ := hBudget L mu q hmu hL hq hqBound
  have hLi : 0 < Li := mul_pos hcL hL
  have hs : 0 < scale := mul_pos hcg hrhop
  have hb : 0 < barlam := div_pos (by positivity) hs
  have hnuEq : scale * barlam = 8 * mu := by dsimp [barlam]; exact mul_div_cancel₀ _ hs.ne'
  obtain ⟨hri, hRhoEq⟩ := internal_rho_matches_external cL L mu eps r hcL hcL1 hL hmu heps hr
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail Li mu eps ri delta omega q scale barlam hh ht
      hmu hMuLi heps hri hd hdw hq hs hb homega hn hnuEq hDistance
  refine ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, ?_⟩
  intro center a ell rw h0 h1 m0 m1 gate X0
  obtain ⟨hDelta, hRange, hSmall, hJ, hGrad, hHess, hSC, Y, S, hMax, hDiff, hSup, hGap⟩ := hCenters center
  have hGradBudget : Cglobal * Li + Cp * nu * q ^ 2 ≤ L := by
    have hh : Cglobal * Li + Cp * nu * q ^ 2 ≤ L / 2 := by simpa only [nu, hnuEq] using hTotalGrad
    linarith only [hh, hL]
  have hHessBudget : Crho * scale + rho Li mu eps ri / 4 ≤ rho L mu eps r := by
    rw [hRhoEq]
    exact (hHessianBudget rhop (rho L mu eps r) hrhop.le hrhopBound).trans
      (by have hh := hrhop.le.trans hrhopBound; linarith only [hh])
  refine ⟨hDelta, hRange, hSmall, hJ, ?_, ?_, hSC, Y, S, hMax, hDiff, hSup, ?_⟩
  · intro x y
    exact (hGrad x y).trans (mul_le_mul_of_nonneg_right hGradBudget (norm_nonneg _))
  · intro x y
    exact (hHess x y).trans (mul_le_mul_of_nonneg_right hHessBudget (norm_nonneg _))
  · intro Phi
    have hg := hGap
    apply hg.trans
    have heq : Cgap0 * ((outer + 1 : ℕ) : ℝ) * energy Li eps =
        Cgap * ((outer + 1 : ℕ) : ℝ) * energy L eps := by
      dsimp [Cgap, energy, Li]
      field_simp
      <;> ring
    exact heq.le

theorem rho_matches_paper_ratio (L mu eps rhoExternal : ℝ)
    (hL : 0 < L) (hmu : 0 < mu) (heps : 0 < eps) :
    rho L mu eps (rhoExternal * (L / mu) * Real.sqrt (L / mu) * eps / L ^ 2) = rhoExternal := by
  have hks : 0 < Real.sqrt (L / mu) := Real.sqrt_pos.mpr (div_pos hL hmu)
  unfold rho
  field_simp [hL.ne', hmu.ne', heps.ne', hks.ne']
  <;> try ring

end
end FangqingExternalPhysicalRelayValidity
end

section
-- Source component: HandleAlignment.lean

namespace HandleAlignment

noncomputable def smallConstant (a Cw cg KD : ℝ) : ℝ :=
  min 1 (min (1 / (16 * a)) (cg * KD / (8 * Cw * a)))

noncomputable def regime (L rho eps kappa : ℝ) : ℝ :=
  rho * kappa ^ (3 / 2 : ℝ) * eps / L ^ 2

noncomputable def packetLength (cq r kappa : ℝ) : ℕ :=
  Nat.floor (cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa))

noncomputable def curvature (a L kappa : ℝ) : ℝ := a * L / kappa
noncomputable def distance (KD L eps kappa : ℝ) : ℝ := KD * eps * Real.sqrt kappa / L
noncomputable def packetBudget (Cw cg nu D : ℝ) (q : ℕ) : ℝ :=
  Cw * nu * (q : ℝ) ^ (7 / 2 : ℝ) / (cg * D)
noncomputable def edgeWidth (Cw cg nu rhoq : ℝ) (q : ℕ) : ℝ :=
  Cw * (q : ℝ) ^ 2 * nu / (cg * rhoq)

theorem smallConstant_bounds (a Cw cg KD : ℝ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) :
    0 < smallConstant a Cw cg KD ∧ smallConstant a Cw cg KD ≤ 1 ∧
    smallConstant a Cw cg KD ≤ 1 / (16 * a) ∧
    smallConstant a Cw cg KD ≤ cg * KD / (8 * Cw * a) := by
  unfold smallConstant
  refine ⟨lt_min (by norm_num) (lt_min (by positivity) (by positivity)),
    min_le_left _ _, ?_, ?_⟩
  · exact le_trans (min_le_right _ _) (min_le_left _ _)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)

theorem length_bounds (cq r kappa : ℝ) (q0 : ℕ)
    (hcq : 0 < cq) (hcq1 : cq ≤ 1) (hr : 0 < r) (hk : 0 < kappa)
    (hq0 : 1 ≤ q0)
    (hnd : (q0 : ℝ) ≤ cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa)) :
    q0 ≤ packetLength cq r kappa ∧
    cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa) / 2 ≤
      (packetLength cq r kappa : ℝ) ∧
    (packetLength cq r kappa : ℝ) ≤ cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa) ∧
    (packetLength cq r kappa : ℝ) ^ (7 / 2 : ℝ) ≤ cq * r ∧
    (packetLength cq r kappa : ℝ) ^ 2 ≤ cq * kappa := by
  let q := packetLength cq r kappa
  have hq0q : q0 ≤ q := Nat.le_floor hnd
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast le_trans hq0 hq0q
  have hqn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  have hm : 0 ≤ cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa) := by positivity
  have hqle : (q : ℝ) ≤ cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa) :=
    Nat.floor_le hm
  have hqnear : cq * min (r ^ (2 / 7 : ℝ)) (Real.sqrt kappa) < (q : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  refine ⟨hq0q, by linarith only [hq1, hqnear], hqle, ?_, ?_⟩
  · have hqr : (q : ℝ) ≤ cq * r ^ (2 / 7 : ℝ) :=
      le_trans hqle (mul_le_mul_of_nonneg_left (min_le_left _ _) hcq.le)
    have hp := Real.rpow_le_rpow hqn hqr (by norm_num : (0 : ℝ) ≤ 7 / 2)
    have hrroot : (r ^ (2 / 7 : ℝ)) ^ (7 / 2 : ℝ) = r := by
      rw [← Real.rpow_mul hr.le]
      norm_num
    rw [Real.mul_rpow hcq.le (Real.rpow_nonneg hr.le _), hrroot] at hp
    have hcqp : cq ^ (7 / 2 : ℝ) ≤ cq := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge hcq hcq1 (by norm_num : (1 : ℝ) ≤ 7 / 2))
    exact le_trans hp (mul_le_mul_of_nonneg_right hcqp hr.le)
  · have hqk : (q : ℝ) ≤ cq * Real.sqrt kappa :=
      le_trans hqle (mul_le_mul_of_nonneg_left (min_le_right _ _) hcq.le)
    have hs : (q : ℝ) ^ 2 ≤ (cq * Real.sqrt kappa) ^ 2 :=
      (sq_le_sq₀ hqn (by positivity)).mpr hqk
    have hsq : (Real.sqrt kappa) ^ 2 = kappa := Real.sq_sqrt hk.le
    have hcqsq : cq ^ 2 ≤ cq := by nlinarith only [hcq.le, hcq1]
    have hprod := mul_le_mul_of_nonneg_right hcqsq hk.le
    nlinarith only [hs, hsq, hprod]

theorem rpow_three_halves (kappa : ℝ) (hk : 0 < kappa) :
    kappa ^ (3 / 2 : ℝ) = kappa * Real.sqrt kappa := by
  calc
    kappa ^ (3 / 2 : ℝ) = kappa ^ ((1 : ℝ) + 1 / 2) := by norm_num
    _ = kappa ^ (1 : ℝ) * kappa ^ (1 / 2 : ℝ) := Real.rpow_add hk _ _
    _ = kappa * Real.sqrt kappa := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem rpow_seven_halves (q : ℝ) (hq : 0 < q) :
    q ^ (7 / 2 : ℝ) = q ^ (3 / 2 : ℝ) * q ^ 2 := by
  calc
    q ^ (7 / 2 : ℝ) = q ^ ((3 / 2 : ℝ) + (2 : ℕ)) := by norm_num
    _ = q ^ (3 / 2 : ℝ) * q ^ (2 : ℝ) := Real.rpow_add hq _ _
    _ = q ^ (3 / 2 : ℝ) * q ^ 2 := by norm_num

theorem aligned_budget_identity (a Cw cg KD L eps kappa : ℝ) (q : ℕ)
    (hL : 0 < L) (hk : 0 < kappa) (he : 0 < eps) (hcg : 0 < cg)
    (hKD : 0 < KD) :
    packetBudget Cw cg (curvature a L kappa) (distance KD L eps kappa) q =
      (Cw * a / (cg * KD)) *
        (L ^ 2 * (q : ℝ) ^ (7 / 2 : ℝ) / (kappa ^ (3 / 2 : ℝ) * eps)) := by
  rw [rpow_three_halves kappa hk]
  unfold packetBudget curvature distance
  have hsk : Real.sqrt kappa ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hk)
  field_simp
  <;> ring

theorem aligned_gap_identity (a KD L eps kappa : ℝ)
    (hL : 0 < L) (hk : 0 < kappa) :
    curvature a L kappa * (distance KD L eps kappa) ^ 2 =
      (a * KD ^ 2) * (eps ^ 2 / L) := by
  unfold curvature distance
  have hsk := Real.sq_sqrt hk.le
  field_simp
  rw [hsk]
  ring

theorem aligned_distance_identity (a Cw cg KD L eps kappa : ℝ) (q : ℕ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD)
    (hL : 0 < L) (he : 0 < eps) (hk : 0 < kappa) (hq : 0 < q) :
    distance KD L eps kappa = (q : ℝ) ^ (3 / 2 : ℝ) *
      edgeWidth Cw cg (curvature a L kappa)
        (packetBudget Cw cg (curvature a L kappa) (distance KD L eps kappa) q) q := by
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnu : curvature a L kappa ≠ 0 := by unfold curvature; positivity
  have hD : distance KD L eps kappa ≠ 0 := by unfold distance; positivity
  have hp : (q : ℝ) ^ (7 / 2 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hqr _)
  unfold edgeWidth packetBudget
  field_simp
  rw [rpow_seven_halves (q : ℝ) hqr]
  <;> ring

theorem coefficient_budget_bounds (a Cw cg KD : ℝ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) :
    (Cw * a / (cg * KD)) * smallConstant a Cw cg KD ≤ 1 / 8 ∧
    a * smallConstant a Cw cg KD ≤ 1 / 16 := by
  have hb := smallConstant_bounds a Cw cg KD ha hCw hcg hKD
  constructor
  · rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (mul_pos hcg hKD)).mpr
    have hh := (le_div_iff₀ (by positivity : 0 < 8 * Cw * a)).mp hb.2.2.2
    nlinarith only [hh]
  · have hh := (le_div_iff₀ (by positivity : 0 < 16 * a)).mp hb.2.2.1
    nlinarith only [hh]

theorem aligned_budget_upper_bound (a Cw cg KD L rho eps kappa : ℝ) (q : ℕ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD)
    (hL : 0 < L) (hrho : 0 < rho) (he : 0 < eps) (hk : 0 < kappa)
    (hq : (q : ℝ) ^ (7 / 2 : ℝ) ≤
      smallConstant a Cw cg KD * regime L rho eps kappa) :
    packetBudget Cw cg (curvature a L kappa) (distance KD L eps kappa) q ≤ rho / 8 := by
  have hkp : 0 < kappa ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hk _
  rw [aligned_budget_identity a Cw cg KD L eps kappa q hL hk he hcg hKD]
  calc
    (Cw * a / (cg * KD)) *
        (L ^ 2 * (q : ℝ) ^ (7 / 2 : ℝ) / (kappa ^ (3 / 2 : ℝ) * eps))
      ≤ (Cw * a / (cg * KD)) *
        (L ^ 2 * (smallConstant a Cw cg KD * regime L rho eps kappa) /
          (kappa ^ (3 / 2 : ℝ) * eps)) := by
          gcongr
    _ = ((Cw * a / (cg * KD)) * smallConstant a Cw cg KD) * rho := by
      unfold regime
      field_simp
      <;> ring
    _ ≤ (1 / 8) * rho :=
      mul_le_mul_of_nonneg_right (coefficient_budget_bounds a Cw cg KD ha hCw hcg hKD).1 hrho.le
    _ = rho / 8 := by ring

theorem aligned_curvature_upper_bound (a Cw cg KD L kappa : ℝ) (q : ℕ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD)
    (hL : 0 < L) (hk : 0 < kappa)
    (hq : (q : ℝ) ^ 2 ≤ smallConstant a Cw cg KD * kappa) :
    curvature a L kappa * (q : ℝ) ^ 2 ≤ L / 16 := by
  calc
    curvature a L kappa * (q : ℝ) ^ 2
      ≤ curvature a L kappa * (smallConstant a Cw cg KD * kappa) := by
        apply mul_le_mul_of_nonneg_left hq
        unfold curvature
        positivity
    _ = (a * smallConstant a Cw cg KD) * L := by
      unfold curvature
      field_simp
      <;> ring
    _ ≤ (1 / 16) * L :=
      mul_le_mul_of_nonneg_right (coefficient_budget_bounds a Cw cg KD ha hCw hcg hKD).2 hL.le
    _ = L / 16 := by ring

theorem private_handle_parameter_alignment (a Cw cg KD : ℝ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) :
    ∃ cq : ℝ, 0 < cq ∧ cq ≤ 1 ∧
      ∀ (L rho eps kappa : ℝ) (q0 : ℕ),
        0 < L → 0 < rho → 0 < eps → 0 < kappa → 1 ≤ q0 →
        (q0 : ℝ) ≤ cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) →
        let q := packetLength cq (regime L rho eps kappa) kappa
        let nu := curvature a L kappa
        let D := distance KD L eps kappa
        let rhoq := packetBudget Cw cg nu D q
        let omega := edgeWidth Cw cg nu rhoq q
        q0 ≤ q ∧
        cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) / 2 ≤ (q : ℝ) ∧
        (q : ℝ) ≤ cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) ∧
        0 < nu ∧ 0 < D ∧ 0 < rhoq ∧ 0 < omega ∧
        D = (q : ℝ) ^ (3 / 2 : ℝ) * omega ∧
        rhoq = (Cw * a / (cg * KD)) *
          (L ^ 2 * (q : ℝ) ^ (7 / 2 : ℝ) / (kappa ^ (3 / 2 : ℝ) * eps)) ∧
        rhoq ≤ rho / 8 ∧
        nu * D ^ 2 = (a * KD ^ 2) * (eps ^ 2 / L) ∧
        nu * (q : ℝ) ^ 2 ≤ L / 16 := by
  let cq := smallConstant a Cw cg KD
  have hcq := smallConstant_bounds a Cw cg KD ha hCw hcg hKD
  refine ⟨cq, hcq.1, hcq.2.1, ?_⟩
  intro L rho eps kappa q0 hL hrho he hk hq0 hnd
  dsimp only
  have hr : 0 < regime L rho eps kappa := by unfold regime; positivity
  have hqb := length_bounds cq (regime L rho eps kappa) kappa q0 hcq.1 hcq.2.1 hr hk hq0 hnd
  let q := packetLength cq (regime L rho eps kappa) kappa
  have hq : 0 < q := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hq0) hqb.1
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnu : 0 < curvature a L kappa := by unfold curvature; positivity
  have hD : 0 < distance KD L eps kappa := by unfold distance; positivity
  have hrhoq : 0 < packetBudget Cw cg (curvature a L kappa) (distance KD L eps kappa) q := by
    unfold packetBudget
    positivity
  have homega : 0 < edgeWidth Cw cg (curvature a L kappa)
      (packetBudget Cw cg (curvature a L kappa) (distance KD L eps kappa) q) q := by
    unfold edgeWidth
    positivity
  exact ⟨hqb.1, hqb.2.1, hqb.2.2.1, hnu, hD, hrhoq, homega,
    aligned_distance_identity a Cw cg KD L eps kappa q ha hCw hcg hKD hL he hk hq,
    aligned_budget_identity a Cw cg KD L eps kappa q hL hk he hcg hKD,
    aligned_budget_upper_bound a Cw cg KD L rho eps kappa q ha hCw hcg hKD hL hrho he hk hqb.2.2.2.1,
    aligned_gap_identity a KD L eps kappa hL hk,
    aligned_curvature_upper_bound a Cw cg KD L kappa q ha hCw hcg hKD hL hk hqb.2.2.2.2⟩

end HandleAlignment
end

section
-- Source component: ReservedAlignment.lean

namespace FangqingReservedAlignment

open HandleAlignment FangqingActualRelayScaling OriginalPacketDistanceGapBounds

noncomputable section

set_option maxHeartbeats 2300000

theorem reserved_parameter_alignment (a Cw cg KD cqcap : ℝ)
    (ha : 0 < a) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) (hcap : 0 < cqcap) :
    ∃ cq : ℝ, 0 < cq ∧ cq ≤ 1 ∧ cq ≤ cqcap ∧
    ∀ (L rho eps kappa : ℝ) (q0 : ℕ),
      0 < L → 0 < rho → 0 < eps → 0 < kappa → 1 ≤ q0 →
      (q0 : ℝ) ≤ cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) →
      let q := packetLength cq (regime L rho eps kappa) kappa
      let nu := curvature a L kappa
      let D := distance KD L eps kappa
      let rhoq := packetBudget Cw cg nu D q
      let omega := edgeWidth Cw cg nu rhoq q
      q0 ≤ q ∧
      cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) / 2 ≤ (q : ℝ) ∧
      (q : ℝ) ≤ cq * min ((regime L rho eps kappa) ^ (2 / 7 : ℝ)) (Real.sqrt kappa) ∧
      (q : ℝ) ^ 2 ≤ cqcap ^ 2 * kappa ∧
      0 < nu ∧ 0 < D ∧ 0 < rhoq ∧ 0 < omega ∧
      D = (q : ℝ) ^ (3 / 2 : ℝ) * omega ∧ rhoq ≤ rho / 8 ∧
      nu * D ^ 2 = (a * KD ^ 2) * (eps ^ 2 / L) := by
  let cq := min (smallConstant a Cw cg KD) cqcap
  have hsmall := smallConstant_bounds a Cw cg KD ha hCw hcg hKD
  have hcq : 0 < cq := lt_min hsmall.1 hcap
  have hqsmall : cq ≤ smallConstant a Cw cg KD := min_le_left _ _
  have hcq1 : cq ≤ 1 := hqsmall.trans hsmall.2.1
  have hqcap : cq ≤ cqcap := min_le_right _ _
  refine ⟨cq, hcq, hcq1, hqcap, ?_⟩
  intro L rho eps kappa q0 hL hrho he hk hq0 hnd q nu D rhoq omega
  have hr : 0 < regime L rho eps kappa := by unfold regime; positivity
  have hqb := length_bounds cq (regime L rho eps kappa) kappa q0 hcq hcq1 hr hk hq0 hnd
  have hqn : 0 < q := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hq0) hqb.1
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqn
  have hnu : 0 < nu := by dsimp [nu, curvature]; positivity
  have hD : 0 < D := by dsimp [D, distance]; positivity
  have hrhoq : 0 < rhoq := by dsimp [rhoq, packetBudget]; positivity
  have homega : 0 < omega := by dsimp [omega, edgeWidth]; positivity
  have hqk : (q : ℝ) ≤ cqcap * Real.sqrt kappa :=
    hqb.2.2.1.trans ((mul_le_mul_of_nonneg_left (min_le_right _ _) hcq.le).trans
      (mul_le_mul_of_nonneg_right hqcap (Real.sqrt_nonneg _)))
  have hqk2 : (q : ℝ) ^ 2 ≤ cqcap ^ 2 * kappa := by
    have hh := (sq_le_sq₀ hqr.le (by positivity : 0 ≤ cqcap * Real.sqrt kappa)).mpr hqk
    simpa only [mul_pow, Real.sq_sqrt hk.le] using hh
  have hqseven : (q : ℝ) ^ (7 / 2 : ℝ) ≤ smallConstant a Cw cg KD * regime L rho eps kappa :=
    hqb.2.2.2.1.trans (mul_le_mul_of_nonneg_right hqsmall hr.le)
  exact ⟨hqb.1, hqb.2.1, hqb.2.2.1, hqk2, hnu, hD, hrhoq, homega,
    aligned_distance_identity a Cw cg KD L eps kappa q ha hCw hcg hKD hL he hk hqn,
    aligned_budget_upper_bound a Cw cg KD L rho eps kappa q ha hCw hcg hKD hL hrho he hk hqseven,
    aligned_gap_identity a KD L eps kappa hL hk⟩

theorem actual_physical_scale_bridge (Cw cg KD L mu eps : ℝ) (q : ℕ)
    (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) (hL : 0 < L) (hmu : 0 < mu)
    (heps : 0 < eps) (hq : 0 < q) :
    let kappa := L / mu
    let nu := curvature 8 L kappa
    let D := distance KD L eps kappa
    let rhoq := packetBudget Cw cg nu D q
    let scale := cg * rhoq
    let lam0 := nu / scale
    let omega := edgeWidth Cw cg nu rhoq q
    0 < scale ∧ 0 < lam0 ∧ 0 < omega ∧ scale * lam0 = 8 * mu ∧
      omega = Cw * lam0 * (q : ℝ) ^ 2 ∧
      distanceScale (q : ℝ) omega = packetD L mu KD eps := by
  intro kappa nu D rhoq scale lam0 omega
  have hk : 0 < kappa := div_pos hL hmu
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnu : 0 < nu := by dsimp [nu, curvature]; positivity
  have hD : 0 < D := by dsimp [D, distance]; positivity
  have hrho : 0 < rhoq := by dsimp [rhoq, packetBudget]; positivity
  have hs : 0 < scale := mul_pos hcg hrho
  have hl : 0 < lam0 := div_pos hnu hs
  have hw : 0 < omega := by dsimp [omega, edgeWidth]; positivity
  have hnuEq : nu = 8 * mu := by dsimp [nu, curvature, kappa]; field_simp; try ring
  refine ⟨hs, hl, hw, ?_, ?_, ?_⟩
  · dsimp [lam0]
    rw [mul_div_cancel₀ _ hs.ne', hnuEq]
  · dsimp [omega, edgeWidth, lam0, scale]
    field_simp
    <;> ring
  · have hid := aligned_distance_identity 8 Cw cg KD L eps kappa q (by norm_num) hCw hcg hKD hL heps hk hq
    have hrpow := HandleAlignment.rpow_three_halves (q : ℝ) hqr
    change D = (q : ℝ) ^ (3 / 2 : ℝ) * omega at hid
    rw [hrpow] at hid
    change (q : ℝ) * Real.sqrt (q : ℝ) * omega = _
    rw [← hid]
    rfl

end
end FangqingReservedAlignment
end

section
-- Source component: InitialGateGeometry.lean

open scoped BigOperators Topology

namespace FangqingInitialGateGeometry

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalPacketDistanceGapBounds OriginalPacketBulkIndexing FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 3500000

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

theorem distance_from_zero_bulk_coordinates (v : I → E) (hv : Orthonormal ℝ v)
    (J : Finset I) (Z w : E) (q omega : ℝ) (hq : 0 ≤ q) (hw : 0 ≤ omega)
    (hcard : (J.card : ℝ) = q)
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z)
    (hzero : ∀ i ∈ J, inner ℝ (v i) w = 0) :
    3 * distanceScale q omega ≤ ‖Z - w‖ := by
  have hcoef : ∀ i ∈ J, (3 * q * omega) ^ 2 ≤ (inner ℝ (v i) (Z - w)) ^ 2 := by
    intro i hi
    have hh : 3 * q * omega ≤ inner ℝ (v i) (Z - w) := by
      rw [inner_sub_right, hzero i hi, sub_zero]
      exact hbulk i hi
    exact (sq_le_sq₀ (by positivity) ((by positivity : 0 ≤ 3 * q * omega).trans hh)).mpr hh
  have hsum : (J.card : ℝ) * (3 * q * omega) ^ 2 ≤ ∑ i ∈ J, (inner ℝ (v i) (Z - w)) ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcoef
  rw [hcard] at hsum
  have hb := hv.sum_inner_products_le (Z - w) (s := J)
  simp only [Real.norm_eq_abs, sq_abs] at hb
  have hd := distanceScale_sq q omega hq
  have hn : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  have hsq : (3 * distanceScale q omega) ^ 2 ≤ ‖Z - w‖ ^ 2 := by
    nlinarith only [hsum, hb, hd]
  nlinarith only [hsq, hn, norm_nonneg (Z - w)]

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

theorem physical_columns_orthogonal_public_A (C : A ≃ₗᵢ[ℝ] B) (h x : A)
    (n : ℕ) (tail : Fin (n + 2) → W) (j : Fin (n + 3)) :
    inner ℝ (physicalFrame C h n tail j) (mkPhysical x (0 : B) (0 : W)) = 0 := by
  refine Fin.cases ?_ (fun i => ?_) j
  · change (inner ℝ (0 : A) x + inner ℝ (C h) (0 : B)) + inner ℝ (0 : W) 0 = 0
    simp
  · change (inner ℝ (0 : A) x + inner ℝ (0 : B) 0) + inner ℝ (tail i) (0 : W) = 0
    simp

theorem scaled_gate_zero_near (R : ℝ) (center z : E) (hR : 0 < R)
    (hz : 3 * R ≤ ‖z - center‖) :
    scaledGate theta R center =ᶠ[𝓝 z] (fun _ => 0) := by
  have hd : 2 * R < ‖z - center‖ := by linarith only [hR, hz]
  have hn : {u : E | 2 * R < ‖u - center‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hd
  filter_upwards [hn] with u hu
  unfold scaledGate
  apply theta_zero
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hs : (2 * R) ^ 2 ≤ ‖u - center‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hu.le
  nlinarith only [hs, sq_nonneg R]

theorem flat_gate_zero_jets (R : ℝ) (center z : E) (hR : 0 < R)
    (hz : 3 * R ≤ ‖z - center‖) :
    scaledGate theta R center z = 0 ∧ fderiv ℝ (scaledGate theta R center) z = 0 ∧
      fderiv ℝ (fderiv ℝ (scaledGate theta R center)) z = 0 := by
  have heq := scaled_gate_zero_near R center z hR hz
  refine ⟨heq.eq_of_nhds, ?_, ?_⟩
  · have hh := heq.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (scaledGate theta R center) z = fderiv ℝ (0 : E → ℝ) z at hh
    simpa only [fderiv_zero, Pi.zero_apply] using hh
  · have hh := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fderiv ℝ (scaledGate theta R center)) z =
      fderiv ℝ (fderiv ℝ (0 : E → ℝ)) z at hh
    simpa only [fderiv_zero, Pi.zero_apply] using hh

theorem scaled_gate_is_original_radial_gate (a ell : ℝ) (xstar : E) :
    scaledGate theta (a * ell) (a • xstar) = FangqingRelayStationarity.radialGate theta a ell xstar := by
  funext z
  simp only [scaledGate, FangqingRelayStationarity.radialGate, mul_pow]

variable [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] [FiniteDimensional ℝ W]

theorem actual_initial_private_gate_flat (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n q : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (hq : 1 ≤ q) (hfit : q ≤ n + 2) (omega beta lam a ell : ℝ)
    (hw : 0 ≤ omega) (hb : 0 < beta) (hl : 0 < lam) (ha : 0 < a) (he : 0 < ell)
    (hell : ell = lam / beta * distanceScale q omega) (Z : PhysicalSpace A B W)
    (hbulk : ∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * (q : ℝ) * omega ≤ inner ℝ (physicalFrame C h n tail j) Z)
    (x : A) :
    let xinit := mkPhysical x (0 : B) (0 : W)
    let xstar := (-lam / beta) • Z
    scaledGate theta (a * ell) (a • xstar) =ᶠ[𝓝 (a • xinit)] (fun _ => 0) := by
  intro xinit xstar
  let J := unrevealedFirstTail n q 0 hfit
  have hidx := actual_unrevealed_index_properties n q 0 hfit (by omega)
  have hcard : (J.card : ℝ) = q := by
    exact_mod_cast unrevealedFirstTail_card n q 0 hfit (by omega)
  have hzero : ∀ j, inner ℝ (physicalFrame C h n tail j) ((-beta / lam) • xinit) = 0 := by
    intro j
    rw [real_inner_smul_right, physical_columns_orthogonal_public_A C h x n tail j, mul_zero]
  have hSep := distance_from_zero_bulk_coordinates (physicalFrame C h n tail)
    (physicalFrame_orthonormal C h hh n tail ht) J Z ((-beta / lam) • xinit) q omega
    (by exact_mod_cast Nat.zero_le q) hw hcard
    (fun j hj => hbulk j (hidx.1 j hj).1) (fun j _ => hzero j)
  have hcoef : (lam / beta) * (-beta / lam) = -1 := by field_simp; try ring
  have halg : xinit - xstar = (lam / beta) • (Z - (-beta / lam) • xinit) := by
    rw [smul_sub, smul_smul, hcoef, neg_one_smul, sub_neg_eq_add]
    dsimp [xstar]
    rw [neg_div, neg_smul, sub_neg_eq_add]
    abel
  have hPrimal : 3 * ell ≤ ‖xinit - xstar‖ := by
    rw [halg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hb), hell]
    convert! mul_le_mul_of_nonneg_left hSep (div_pos hl hb).le using 1 <;> ring
  apply scaled_gate_zero_near (a * ell) (a • xstar) (a • xinit) (mul_pos ha he)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  convert! mul_le_mul_of_nonneg_left hPrimal ha.le using 1 <;> ring

end
end FangqingInitialGateGeometry
end

section
-- Source component: RelayExactInitialMaximum.lean

open scoped BigOperators

namespace FangqingRelayExactInitialMaximum

open FangqingRelayStationarity FangqingEndpointInitializationBounds

noncomputable section

set_option maxHeartbeats 2000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem active_endpoint_initial_exact_max (h : E → ℝ) (d beta lam m seed : ℝ) (handle : E)
    (hd : 0 ≤ d) (hlam : lam ≠ 0) (hsc : StrongConvexOn (Set.univ : Set E) d h)
    (hc : Differentiable ℝ h) (hg : gradient h 0 = (-seed) • handle) (y : E) :
    endpoint beta lam h m ((-(seed / lam)) • handle) y ≤
      endpoint beta lam h m ((-(seed / lam)) • handle) 0 := by
  let x : E := (-(seed / lam)) • handle
  have hi : lam * inner ℝ x y = inner ℝ (gradient h 0) y := by
    rw [hg]
    dsimp [x]
    simp only [real_inner_smul_left]
    field_simp
    <;> ring
  have hs := PacketCore.strongConvex_support h d hsc hc 0 y
  simp only [sub_zero] at hs
  have hn : 0 ≤ d / 2 * ‖y‖ ^ 2 := by positivity
  change endpoint beta lam h m x y ≤ endpoint beta lam h m x 0
  unfold endpoint
  rw [hi]
  simp only [inner_zero_right, mul_zero, add_zero]
  linarith only [hs, hn]

theorem displayed_dual_initial_point_is_exact_max
    (n : ℕ) (d beta lam a sigma reward M seed : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (X : Fin (n + 1) → E) (handle : E)
    (hd : 0 ≤ d) (hlam : lam ≠ 0) (hsigma : 0 ≤ sigma) (hM : 0 ≤ M) (hreward : M ≤ reward)
    (h0c : ∀ t, Differentiable ℝ (h0 t)) (h1c : Differentiable ℝ (h1 0))
    (h0sc : ∀ t, StrongConvexOn (Set.univ : Set E) d (h0 t))
    (h1sc : StrongConvexOn (Set.univ : Set E) d (h1 0))
    (h0grad : ∀ t, gradient (h0 t) 0 = 0) (h1grad : gradient (h1 0) 0 = (-seed) • handle)
    (hm0 : ∀ t, m0 t = h0 t 0)
    (hX0 : X 0 = (-(seed / lam)) • handle) (hXtail : ∀ j : Fin n, X j.succ = 0)
    (hGate : ∀ j z, 0 ≤ gate j z)
    (hDelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (hGateInit : ∀ j, gate j (a • X j.castSucc) = 0) :
    ∀ yy ss : Fin (n + 1) → E,
      family n beta lam a sigma reward h0 h1 m0 m1 gate X yy ss ≤
        family n beta lam a sigma reward h0 h1 m0 m1 gate X 0 (fun t => a • X t) := by
  have hInactiveVal : ∀ j : Fin n, endpoint beta lam (h0 j.succ) (m0 j.succ) (X j.succ) 0 = 0 := by
    intro j
    rw [hXtail]
    simp [endpoint, hm0 j.succ]
  have hAt : family n beta lam a sigma reward h0 h1 m0 m1 gate X 0 (fun t => a • X t) =
      endpoint beta lam (h1 0) (m1 0) (X 0) 0 := by
    rw [family_eq_paper]
    simp_rw [hGateInit]
    simp only [Pi.zero_apply, sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      Finset.sum_const_zero, mul_zero, sub_zero, zero_mul, add_zero]
    simp_rw [hInactiveVal]
    simp
  intro yy ss
  rw [hAt]
  have hUpper := FangqingRelayGap.family_upper_by_endpoints n beta lam a sigma reward M
    h0 h1 m0 m1 gate X yy ss hsigma hM hreward hGate hDelta
  have hi : (∑ j : Fin n, endpoint beta lam (h0 j.succ) (m0 j.succ) (X j.succ) (yy j.succ)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    rw [hXtail, hm0]
    exact inactive_endpoint_origin_max (h0 j.succ) d beta lam hd (h0sc j.succ) (h0c j.succ) (h0grad j.succ) _
  have hf : endpoint beta lam (h1 0) (m1 0) (X 0) (yy 0) ≤
      endpoint beta lam (h1 0) (m1 0) (X 0) 0 := by
    rw [hX0]
    exact active_endpoint_initial_exact_max (h1 0) d beta lam (m1 0) seed handle hd hlam h1sc h1c h1grad _
  linarith only [hUpper, hi, hf]

end
end FangqingRelayExactInitialMaximum
end

section
-- Source component: PhysicalRelayExactInitialPoint.lean

open scoped ContDiff Topology

namespace FangqingPhysicalRelayExactInitialPoint

open FangqingAmplifier FangqingActualInactivePacket FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingPathEdgeRegularity OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds
  FangqingRelayFenchelInterfaces FangqingRelayStationarity FangqingPublicShellProfiles FangqingRadialGateBounds
  FangqingActualShellOriginJets FangqingInitialGateGeometry FangqingRelayExactInitialMaximum

noncomputable section

set_option maxHeartbeats 5500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem displayed_physical_initial_point_exact
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (hphi : ∀ t, |t| < 1 → phi t = t)
    (outer nt q : ℕ) (C : A ≃ₗᵢ[ℝ] B) (h : Fin (outer + 1) → A)
    (tail : Fin (outer + 1) → Fin (nt + 2) → W) (Z : Fin (outer + 1) → PhysicalSpace A B W)
    (hh : ∀ t, ‖h t‖ = 1) (ht : ∀ t, Orthonormal ℝ (tail t))
    (hq : 1 ≤ q) (hfit : q ≤ nt + 2)
    (delta omega nu scale R seedWidth seed gain c nu0 LH rhoH beta lam a ell sigma reward M : ℝ)
    (hR : 0 < R) (hA : 0 < seedWidth) (hw : 0 ≤ omega)
    (hb : 0 < beta) (hl : 0 < lam) (ha : 0 < a) (he : 0 < ell)
    (hell : ell = lam / beta * distanceScale q omega) (hmod : 0 ≤ nu0 - c)
    (hsigma : 0 ≤ sigma) (hM : 0 ≤ M) (hreward : M ≤ reward) :
    let H0 := fun t => inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
    let H1 := fun t z => H0 t z - localizedSeed theta phi R seedWidth (seed * seedWidth) (mkPhysical (h t) 0 0) z
    let h0 := fun t => reduced (H0 t) c
    let h1 := fun t => reduced (H1 t) c
    let m0 := fun t => H0 t 0
    let m1 := fun t => H1 t (Z t)
    let X0 : Fin (outer + 1) → PhysicalSpace A B W :=
      Fin.cons ((-(seed / lam)) • mkPhysical (h 0) (0 : B) (0 : W)) (fun _ => 0)
    let gate := fun j : Fin outer => scaledGate theta (a * ell) (a • ((-lam / beta) • Z j.castSucc))
    (∀ t, AnalyticClass (H0 t) nu0 LH rhoH) →
    (∀ t, AnalyticClass (H1 t) nu0 LH rhoH) →
    (∀ t y, H0 t 0 ≤ H0 t y) →
    (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
      3 * (q : ℝ) * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) →
    (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M) →
      (∀ j, gate j =ᶠ[𝓝 (a • X0 j.castSucc)] (fun _ => 0)) ∧
      (∀ yy ss : Fin (outer + 1) → PhysicalSpace A B W,
        family outer beta lam a sigma reward h0 h1 m0 m1 gate X0 yy ss ≤
          family outer beta lam a sigma reward h0 h1 m0 m1 gate X0 0 (fun t => a • X0 t)) := by
  intro H0 H1 h0 h1 m0 m1 X0 gate hH0 hH1 hMin0 hBulk hDelta
  have hHandle : ∀ t, ‖mkPhysical (h t) (0 : B) (0 : W)‖ ≤ 1 := by
    intro t
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical (h t) (0 : B) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h t, (0 : B)))
    change ‖mkPhysical (h t) (0 : B) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h t, (0 : B))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h t, (0 : B))‖ ^ 2 = ‖h t‖ ^ 2 + ‖(0 : B)‖ ^ 2 at hn2
    rw [hh t, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical (h t) (0 : B) (0 : W))]
  let xA : Fin (outer + 1) → A := Fin.cons ((-(seed / lam)) • h 0) (fun _ => 0)
  have hxA : ∀ t, X0 t = mkPhysical (xA t) (0 : B) (0 : W) := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · change (-(seed / lam)) • mkPhysical (h 0) (0 : B) (0 : W) =
        mkPhysical ((-(seed / lam)) • h 0) (0 : B) (0 : W)
      rw [smul_mkPhysical, smul_zero, smul_zero]
    · simp only [X0, xA, Fin.cons_succ]
      rfl
  have hFlat : ∀ j, gate j =ᶠ[𝓝 (a • X0 j.castSucc)] (fun _ => 0) := by
    intro j
    have hh := actual_initial_private_gate_flat C (h j.castSucc) (hh j.castSucc) nt q (tail j.castSucc)
      (ht j.castSucc) hq hfit omega beta lam a ell hw hb hl ha he hell (Z j.castSucc) (hBulk j.castSucc) (xA j.castSucc)
    rw [hxA]
    exact hh
  refine ⟨hFlat, ?_⟩
  have hOrig := fun t => actual_paired_shell_origin_gradients (QPhysical q nu C)
    (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z)
    phi R seedWidth seed gain c (mkPhysical (h t) 0 0) hR hA (hHandle t) hphi (hH0 t).1 (hMin0 t)
  have hc0 : ∀ t, Differentiable ℝ (h0 t) := by
    intro t
    exact ((hH0 t).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ))).differentiable (by norm_num)
  have hc1 : Differentiable ℝ (h1 0) :=
    ((hH1 0).1.sub (contDiff_const.mul (contDiff_norm_sq ℝ))).differentiable (by norm_num)
  have hsc0 : ∀ t, StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) (nu0 - c) (h0 t) :=
    fun t => reduced_strongConvex (H0 t) nu0 c (hH0 t).2.1
  have hsc1 : StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) (nu0 - c) (h1 0) :=
    reduced_strongConvex (H1 0) nu0 c (hH1 0).2.1
  have hm0 : ∀ t, m0 t = h0 t 0 := by
    intro t
    simp only [m0, h0, reduced, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, sub_zero]
  exact displayed_dual_initial_point_is_exact_max outer (nu0 - c) beta lam a sigma reward M seed
    h0 h1 m0 m1 gate X0 (mkPhysical (h 0) 0 0) hmod hl.ne' hsigma hM hreward hc0 hc1 hsc0 hsc1
    (fun t => (hOrig t).2.1.gradient) (hOrig 0).2.2.2.gradient hm0 rfl
    (fun _ => rfl) (fun j z => (theta_range _).1) hDelta (fun j => (hFlat j).eq_of_nhds)

end
end FangqingPhysicalRelayExactInitialPoint
end

section
-- Source component: RelayRegularityComplete.lean

open scoped ContDiff Topology

namespace FangqingRelayRegularityComplete

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingExternalPhysicalRelayValidity FangqingPhysicalRelayExactInitialPoint
  FangqingInitialGateGeometry FangqingRelayStationarity

noncomputable section

set_option maxHeartbeats 8500000

universe u

theorem actual_relay_regularity_stationarity_initialization
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw b0 : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hb0 : 0 < b0)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 2 + 1 / b0 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Cgap ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      let Cs := 2 * Cw
      let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
      let Cp := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      ∃ cL cq cg : ℝ, 0 < cL ∧ cL ≤ 1 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧
      ∀ (A0 B0 W : Type u)
        [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
        [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
        (tail : Fin (outer + 1) → Fin (nt + 2) → W)
        (L mu eps r rhop q delta omega : ℝ),
        (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
        0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
        1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) →
        (∃ qn : ℕ, q = (qn : ℝ) ∧ 1 ≤ qn ∧ qn ≤ nt + 2) → 0 < delta → delta ≤ omega →
        ((nt + 2 : ℕ) : ℝ) ≤ Cm * q →
        let Li := cL * L
        let ri := r / Real.sqrt cL
        let scale := cg * rhop
        let barlam := (8 * mu) / scale
        omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mu KD eps →
        let nu := scale * barlam
        let D := distanceScale q omega
        let A := CA * D
        let R := 2 * A
        let seed := Cs * nu * D
        let Mpath : ℝ := (4 * Ce : ℝ) * scale * omega
        let gain := (16 * K + 1) * Mpath
        let H0 := fun t => inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
        let H1 := fun t z => H0 t z - localizedSeed theta phi R A (seed * A) (mkPhysical (h t) 0 0) z
        ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
          (∀ t, AnalyticClass (H0 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t, AnalyticClass (H1 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
          (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
          (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
          (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
            3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
          let a := relayAmplitude 1 (Li / mu) ri
          let ell := width Li mu KD eps
          let rw := reward Cdelta 8 Li KD eps
          let h0 := fun t => reduced (H0 t) mu
          let h1 := fun t => reduced (H1 t) mu
          let m0 := fun t => H0 t 0
          let m1 := fun t => H1 t (Z t)
          let center := fun j : Fin outer => a • ((-lam Li mu / Li) • Z j.castSucc)
          let gate := fun j => scaledGate theta (a * ell) (center j)
          let X0 : Blocks outer (PhysicalSpace A0 B0 W) :=
            WithLp.toLp 2 (Fin.cons ((-(seed / lam Li mu)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
          Validity outer Li (lam Li mu) a (sigma Li a csigma) rw L mu (rho L mu eps r)
            (rawBudget Cdelta 8 Li mu KD eps) Ctheta ell Cgap (energy L eps) h0 h1 m0 m1 gate X0 ∧
          (∀ j, gate j =ᶠ[𝓝 (a • X0 j.castSucc)] (fun _ => 0)) ∧
          (∀ yy ss : Fin (outer + 1) → PhysicalSpace A0 B0 W,
            family outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate X0.ofLp yy ss ≤
              family outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate X0.ofLp 0 (fun t => a • X0 t)) ∧
          (∀ (Y S : Blocks outer (PhysicalSpace A0 B0 W) → (Fin (outer + 1) → PhysicalSpace A0 B0 W)),
            (∀ (X : Blocks outer (PhysicalSpace A0 B0 W)) yy ss,
              family outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate X.ofLp yy ss ≤
                exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate Y S X) →
            Differentiable ℝ (exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate Y S) →
            ∀ X : Blocks outer (PhysicalSpace A0 B0 W),
              ‖gradient (exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate Y S) X‖ ≤ eps →
              (∀ j : Fin outer, gate j (S X j.castSucc) = 1) ∧
              (∀ t, ‖X t - (-lam Li mu / Li) • Z t‖ ≤ b0 * ell)) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  let KDlower := 2 + 1 / b0
  have hKDlower : 0 ≤ KDlower := by dsimp [KDlower]; positivity
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
      hCD, hCt, hGap, hThetaDeriv, cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, hBuilder⟩ :=
    actual_external_physical_relay_validity.{u} P phi Bp left right Cm Cw KDlower hCm hCw hKDlower hp hl hr hcore
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap, hK, hKc, hKs, hKD, hKDl,
    hcs, hCG, hCD, hCt, hGap, hThetaDeriv, cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r rhop q delta omega hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn
    Li ri scale barlam homega hDistance nu D A R seed Mpath gain H0 H1
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail L mu eps r rhop q delta omega hh ht
      hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn homega hDistance
  refine ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, ?_⟩
  intro a ell rw h0 h1 m0 m1 center gate X0
  have hV := hCenters center
  have hVkeep := hV
  obtain ⟨hDelta, hRange, hSmall, hJ, hGrad, hHess, hSC, hValue⟩ := hV
  have hLi : 0 < Li := mul_pos hcL hL
  have hs : 0 < scale := mul_pos hcg hrhop
  have hb : 0 < barlam := div_pos (by positivity) hs
  have hNu : 0 < nu := mul_pos hs hb
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hCs : 0 ≤ (2 * Cw) := by positivity
  have hCA : 1 ≤ (1 + 2 * Ks * (2 * Cw) + 2 * Cw * (Cm + 2)) := by
    have h1 : 0 ≤ 2 * Ks * (2 * Cw) := by positivity
    have h2 : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
    linarith only [h1, h2]
  have hA : 0 < A := by dsimp [A]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hlam : 0 < lam Li mu := by unfold lam; positivity
  have he : 0 < ell := by dsimp [ell]; rw [width_eq_actual _ _ _ _ hLi hmu]; positivity
  have hell : ell = lam Li mu / Li * distanceScale q omega := by
    dsimp [ell, width]
    rw [← hDistance]
    ring
  have hMd : 0 ≤ rawBudget Cdelta 8 Li mu KD eps := by unfold rawBudget; positivity
  have hRw : rawBudget Cdelta 8 Li mu KD eps ≤ rw := by
    have hEq := reward_eq_two_raw_plus_energy Cdelta 8 Li mu KD eps hLi hmu
    change rawBudget Cdelta 8 Li mu KD eps ≤ reward Cdelta 8 Li KD eps
    rw [hEq]
    have he : 0 ≤ energy Li eps := by unfold energy; positivity
    linarith only [he, hMd]
  have ha : 0 < a := by
    change 0 < 1 * max 1 (((Li / mu) ^ (3 / 2 : ℝ) / ri) ^ (1 / 3 : ℝ))
    simpa only [one_mul] using zero_lt_one.trans_le (le_max_left 1 (((Li / mu) ^ (3 / 2 : ℝ) / ri) ^ (1 / 3 : ℝ)))
  have hSig : 0 < sigma Li a csigma := by unfold sigma; positivity
  have hInit : (∀ j, gate j =ᶠ[𝓝 (a • X0 j.castSucc)] (fun _ => 0)) ∧
      (∀ yy ss : Fin (outer + 1) → PhysicalSpace A0 B0 W,
        family outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate X0.ofLp yy ss ≤
          family outer Li (lam Li mu) a (sigma Li a csigma) rw h0 h1 m0 m1 gate X0.ofLp 0 (fun t => a • X0 t)) := by
    obtain ⟨qn, hqCast, hqn, hfit⟩ := hInteger
    subst q
    exact displayed_physical_initial_point_exact P phi hcore outer nt qn C h tail Z hh ht hqn hfit
      delta omega nu scale R A seed gain mu (4 * mu) _ _ Li (lam Li mu) a ell
      (sigma Li a csigma) rw (rawBudget Cdelta 8 Li mu KD eps) hR hA hw.le hLi hlam ha he hell
      (by linarith only [hmu]) hSig.le hMd hRw hH0 hH1 hMin0 hBulk hDelta
  refine ⟨hVkeep, hInit.1, hInit.2, ?_⟩
  intro Y S hMax hDiff X hStationary
  have hrel : lam Li mu ^ 2 = Li * mu := Real.sq_sqrt (by positivity)
  have hscH : ∀ t, StrongConvexOn (Set.univ : Set (PhysicalSpace A0 B0 W)) (3 * mu + mu) (H1 t) := by
    intro t
    convert! (hH1 t).2.1 using 1 <;> ring
  have hdiffH : ∀ t, Differentiable ℝ (H1 t) := fun t => (hH1 t).1.differentiable (by norm_num)
  have hDeltaH : ∀ t z, |H0 t z - H1 t z + m1 t - m0 t| ≤ rawBudget Cdelta 8 Li mu KD eps := by
    intro t z
    have hh := hDelta t z
    rw [FangqingRelayFenchelInterfaces.delta_from_H] at hh
    exact hh
  have hKDfrac : 1 / b0 ≤ KD := by dsimp [KDlower] at hKDl; linarith only [hKDl]
  have hKDb : 1 ≤ KD * b0 := (div_le_iff₀ hb0).mp hKDfrac
  have hKDtwo : 2 ≤ KD := by
    have hn : 0 ≤ 1 / b0 := by positivity
    dsimp [KDlower] at hKDl
    linarith only [hKDl, hn]
  have hKDradius : 2 ≤ KD * (3 / 2) := by linarith only [hKDtwo]
  obtain ⟨hWidth, hClose⟩ := actual_stationarity_width_margins Li mu KD eps (3 / 2) b0
    hLi hmu heps.le hKDradius hKDb
  have hGateEq : ∀ j z, gate j z = radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc) z := by
    intro j z
    exact congrFun (scaled_gate_is_original_radial_gate a ell ((-lam Li mu / Li) • Z j.castSucc)) z
  have hGateFun : gate = (fun j => radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc)) := by
    funext j z
    exact hGateEq j z
  have hMax' : ∀ (U : Blocks outer (PhysicalSpace A0 B0 W)) yy ss,
      family outer Li (lam Li mu) a (sigma Li a csigma) rw
        (fun t => fenchelPotential (H0 t) mu) (fun t => fenchelPotential (H1 t) mu) m0 m1
        (fun j => radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc)) U.ofLp yy ss ≤
      exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw
        (fun t => fenchelPotential (H0 t) mu) (fun t => fenchelPotential (H1 t) mu) m0 m1
        (fun j => radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc)) Y S U := by
    simpa only [hGateFun, h0, h1, reduced, fenchelPotential] using! hMax
  have hDiff' : Differentiable ℝ (exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw
      (fun t => fenchelPotential (H0 t) mu) (fun t => fenchelPotential (H1 t) mu) m0 m1
      (fun j => radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc)) Y S) := by
    simpa only [hGateFun, h0, h1, reduced, fenchelPotential] using! hDiff
  have hStationary' : ‖gradient (exactValue outer Li (lam Li mu) a (sigma Li a csigma) rw
      (fun t => fenchelPotential (H0 t) mu) (fun t => fenchelPotential (H1 t) mu) m0 m1
      (fun j => radialGate theta a ell ((-lam Li mu / Li) • Z j.castSucc)) Y S) X‖ ≤ eps := by
    simpa only [hGateFun, h0, h1, reduced, fenchelPotential] using! hStationary
  have hout := original_packet_relay_stationarity outer Li mu (lam Li mu) (3 * mu) a (sigma Li a csigma) rw
    (rawBudget Cdelta 8 Li mu KD eps) Ctheta ell (3 / 2) b0 eps H0 H1 m0 m1 Z theta
    hLi hrel ha hSig he (by positivity) hMd hCt (by norm_num) hscH hdiffH hMin1
    ((theta_smooth.of_le (by decide) : ContDiff ℝ 3 theta).differentiable (by norm_num)) theta_antitone hThetaDeriv
    (fun u _ hu => theta_one u (by nlinarith only [hu])) hRw hDeltaH hSmall hWidth hClose Y S hMax'
    X (hDiff' X) hStationary'
  simpa only [← hGateEq] using hout

end
end FangqingRelayRegularityComplete
end

section
-- Source component: OriginalF2PrefixAcquisitionV2.lean

namespace FangqingOriginalF2PrefixAcquisition

open FangqingRelayJointReindexing FangqingLateGateRelaySlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev Query (E : Type*) := FlatJoint 1 E
abbrev Response (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  ℝ × Query E × (Query E →L[ℝ] Query E)
abbrev History (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := ℕ → Response E

noncomputable def queryOf (omega : ℝ) (known : E) : Query E :=
  coordinateIsometry ((1 : Fin 3), (0 : Fin 2)) ((omega / 2) • known)

noncomputable def correction (publicPart : E →L[ℝ] E) (c invGamma : ℝ)
    (known : E) (answer : Response E) : E :=
  invGamma • (-(answer.2.2 (coordinateIsometry ((1 : Fin 3), (0 : Fin 2)) known)) (1, 0) +
    c • known - publicPart known)

noncomputable def nextVector (publicPart : E →L[ℝ] E) (c invGamma : ℝ)
    (r : ℕ) (previous known : E) (answer : Response E) : E :=
  if r = 0 then known - correction publicPart c invGamma known answer else
    (2 : ℝ) • known - previous - correction publicPart c invGamma known answer

noncomputable def guesses (n : ℕ) (publicPart : E →L[ℝ] E) (c invGamma : ℝ) (initial : E) :
    ℕ → History E → (Fin (n + 3) → E)
  | 0, _ => Function.update 0 0 initial
  | r + 1, history =>
      let old := guesses n publicPart c invGamma initial r history
      if hr : r + 1 < n + 3 then
        Function.update old ⟨r + 1, hr⟩
          (nextVector publicPart c invGamma r
            (old ⟨r - 1, by omega⟩) (old ⟨r, by omega⟩) (history r))
      else old

noncomputable def query (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ) (initial : E)
    (r : ℕ) (history : History E) : Query E :=
  if hr : r < n + 3 then queryOf omega (guesses n publicPart c invGamma initial r history ⟨r, hr⟩) else 0

noncomputable def execution (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ) (initial : E)
    (oracle : Query E → Response E) : ℕ → History E × List (Query E)
  | 0 => (0, [])
  | r + 1 =>
      let old := execution n publicPart omega c invGamma initial oracle r
      let z := query n publicPart omega c invGamma initial r old.1
      (Function.update old.1 r (oracle z), old.2 ++ [z])

theorem actual_bundled_query_trace_length
    (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ) (initial : E)
    (oracle : Query E → Response E) (r : ℕ) :
    (execution n publicPart omega c invGamma initial oracle r).2.length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [execution, List.length_append, List.length_singleton] using congrArg Nat.succ ih

theorem guesses_depend_only_on_previous_responses
    (n : ℕ) (publicPart : E →L[ℝ] E) (c invGamma : ℝ) (initial : E)
    (r : ℕ) (hist0 hist1 : History E) (h : ∀ j < r, hist0 j = hist1 j) :
    guesses n publicPart c invGamma initial r hist0 =
      guesses n publicPart c invGamma initial r hist1 := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hold := ih (fun j hj => h j (by omega))
      simp only [guesses, hold, h r (by omega)]

theorem guesses_after_appending_response
    (n : ℕ) (publicPart : E →L[ℝ] E) (c invGamma : ℝ) (initial : E)
    (r : ℕ) (history : History E) (answer : Response E) :
    guesses n publicPart c invGamma initial r (Function.update history r answer) =
      guesses n publicPart c invGamma initial r history := by
  apply guesses_depend_only_on_previous_responses
  intro j hj
  simp only [Function.update_apply, if_neg (ne_of_lt hj)]

theorem continuous_correction (publicPart : E →L[ℝ] E) (c invGamma : ℝ) :
    Continuous (fun z : E × Response E => correction publicPart c invGamma z.1 z.2) := by
  have hH : Continuous (fun z : E × Response E => z.2.2.2) := continuous_snd.snd.snd
  have haxis : Continuous (fun z : E × Response E => coordinateIsometry ((1 : Fin 3), (0 : Fin 2)) z.1) :=
    (coordinateIsometry (E := E) ((1 : Fin 3), (0 : Fin 2))).continuous.comp continuous_fst
  have hp : Continuous (fun z : E × Response E =>
      (z.2.2.2 (coordinateIsometry ((1 : Fin 3), (0 : Fin 2)) z.1)) (1, 0)) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 × Fin 2 => E) (1, 0)).continuous.comp (hH.clm_apply haxis)
  have hc : Continuous (fun z : E × Response E => c • z.1) := continuous_const.smul continuous_fst
  exact ((hp.neg.add hc).sub (publicPart.continuous.comp continuous_fst)).const_smul invGamma

theorem continuous_guesses
    (n : ℕ) (publicPart : E →L[ℝ] E) (c invGamma : ℝ) (initial : E) (r : ℕ) :
    Continuous (guesses n publicPart c invGamma initial r) := by
  induction r with
  | zero => exact continuous_const
  | succ r ih =>
      simp only [guesses]
      split_ifs with hr
      · have hprev := (continuous_apply (⟨r - 1, by omega⟩ : Fin (n + 3))).comp ih
        have hcur := (continuous_apply (⟨r, by omega⟩ : Fin (n + 3))).comp ih
        have hcorr := (continuous_correction publicPart c invGamma).comp
          (hcur.prodMk (continuous_apply r))
        have hnew : Continuous (fun history : History E => nextVector publicPart c invGamma r
            (guesses n publicPart c invGamma initial r history ⟨r - 1, by omega⟩)
            (guesses n publicPart c invGamma initial r history ⟨r, by omega⟩) (history r)) := by
          by_cases hzero : r = 0
          · simp only [nextVector, if_pos hzero]
            convert! hcur.sub hcorr using 1
          · simp only [nextVector, if_neg hzero]
            convert! ((hcur.const_smul (2 : ℝ)).sub hprev).sub hcorr using 1
        apply continuous_pi
        intro i
        by_cases hi : i = (⟨r + 1, hr⟩ : Fin (n + 3))
        · simpa only [Function.update_apply, if_pos hi] using hnew
        · simpa only [Function.update_of_ne hi, Function.comp_def] using (continuous_apply i).comp ih
      · exact ih

theorem actual_borel_query_rule
    (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ) (initial : E) (r : ℕ) :
    Continuous (query n publicPart omega c invGamma initial r) := by
  unfold query
  split_ifs with hr
  · exact (coordinateIsometry (E := E) ((1 : Fin 3), (0 : Fin 2))).continuous.comp
      (((continuous_apply (⟨r, hr⟩ : Fin (n + 3))).comp
        (continuous_guesses n publicPart c invGamma initial r)).const_smul (omega / 2))
  · exact continuous_const

theorem actual_prefix_recovery_from_response_identities
    (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ)
    (V : Fin (n + 3) → E) (oracle : Query E → Response E)
    (hphysics : ∀ (r : ℕ) (hr : r + 1 < n + 3),
      nextVector publicPart c invGamma r (V ⟨r - 1, by omega⟩) (V ⟨r, by omega⟩)
        (oracle (queryOf omega (V ⟨r, by omega⟩))) = V ⟨r + 1, hr⟩)
    (r : ℕ) :
    ∀ i : Fin (n + 3), i.val ≤ r →
      guesses n publicPart c invGamma (V 0) r
        (execution n publicPart omega c invGamma (V 0) oracle r).1 i = V i := by
  induction r with
  | zero =>
      intro i hi
      have he : i = 0 := Fin.ext (by simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hi)
      subst i
      simp [guesses]
  | succ r ih =>
      intro i hi
      change guesses n publicPart c invGamma (V 0) (r + 1)
        (Function.update (execution n publicPart omega c invGamma (V 0) oracle r).1 r
          (oracle (query n publicPart omega c invGamma (V 0) r
            (execution n publicPart omega c invGamma (V 0) oracle r).1))) i = V i
      simp only [guesses, guesses_after_appending_response, Function.update_self]
      split_ifs with hr
      · by_cases hiNext : i = (⟨r + 1, hr⟩ : Fin (n + 3))
        · subst i
          rw [Function.update_self]
          have hcur := ih (⟨r, by omega⟩ : Fin (n + 3)) (by simp)
          have hprev := ih (⟨r - 1, by omega⟩ : Fin (n + 3)) (by simp)
          have hquery : query n publicPart omega c invGamma (V 0) r
              (execution n publicPart omega c invGamma (V 0) oracle r).1 =
              queryOf omega (V ⟨r, by omega⟩) := by
            rw [query, dif_pos (by omega), hcur]
          rw [hcur, hprev, hquery]
          exact hphysics r hr
        · rw [Function.update_of_ne hiNext]
          apply ih i
          have hne : i.val ≠ r + 1 := by
            intro he
            exact hiNext (Fin.ext he)
          omega
      · apply ih i
        omega

theorem actual_queries_use_recovered_known_column
    (n : ℕ) (publicPart : E →L[ℝ] E) (omega c invGamma : ℝ)
    (V : Fin (n + 3) → E) (oracle : Query E → Response E)
    (hphysics : ∀ (r : ℕ) (hr : r + 1 < n + 3),
      nextVector publicPart c invGamma r (V ⟨r - 1, by omega⟩) (V ⟨r, by omega⟩)
        (oracle (queryOf omega (V ⟨r, by omega⟩))) = V ⟨r + 1, hr⟩)
    (r : ℕ) (hr : r < n + 3) :
    query n publicPart omega c invGamma (V 0) r
      (execution n publicPart omega c invGamma (V 0) oracle r).1 = queryOf omega (V ⟨r, hr⟩) := by
  rw [query, dif_pos hr]
  rw [actual_prefix_recovery_from_response_identities n publicPart omega c invGamma V oracle hphysics r
    ⟨r, hr⟩ (by simp)]

end FangqingOriginalF2PrefixAcquisition
end

section
-- Source component: LateQueryFromHistory.lean

open scoped BigOperators

namespace FangqingLateQueryFromHistory

open FangqingOriginalF2PrefixAcquisition FangqingLateGateRelaySlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def prefixPoint (n cutoff : ℕ) (alpha : ℝ) (handle : E)
    (coeff : Fin (n + 3) → ℝ) (frame : Fin (n + 3) → E) : E :=
  alpha • handle + ∑ i, if i.val < cutoff then coeff i • frame i else 0

noncomputable def latePoint (n cutoff : ℕ) (current : Fin (n + 3))
    (alpha omega tau a offset : ℝ) (handle : E)
    (coeff : Fin (n + 3) → ℝ) (frame : Fin (n + 3) → E) : Query E :=
  coordinateIsometry ((1 : Fin 3), (0 : Fin 2)) ((omega / 2) • frame current) +
    coordinateIsometry ((2 : Fin 3), (0 : Fin 2))
      (a • (-(tau • prefixPoint n cutoff alpha handle coeff frame) + offset • handle))

noncomputable def actualHistoryLateQuery
    (n cutoff r : ℕ) (current : Fin (n + 3)) (publicPart : E →L[ℝ] E)
    (alpha omega tau a offset c invGamma : ℝ) (handle initial : E)
    (coeff : Fin (n + 3) → ℝ) (history : History E) : Query E :=
  latePoint n cutoff current alpha omega tau a offset handle coeff
    (guesses n publicPart c invGamma initial r history)

theorem prefixPoint_respects_known_columns
    (n cutoff : ℕ) (alpha : ℝ) (handle : E) (coeff : Fin (n + 3) → ℝ)
    (V U : Fin (n + 3) → E) (h : ∀ i, i.val < cutoff → V i = U i) :
    prefixPoint n cutoff alpha handle coeff V = prefixPoint n cutoff alpha handle coeff U := by
  unfold prefixPoint
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < cutoff
  · rw [if_pos hi, if_pos hi, h i hi]
  · rw [if_neg hi, if_neg hi]

theorem latePoint_respects_known_columns
    (n cutoff : ℕ) (current : Fin (n + 3)) (hcurrent : current.val < cutoff)
    (alpha omega tau a offset : ℝ) (handle : E) (coeff : Fin (n + 3) → ℝ)
    (V U : Fin (n + 3) → E) (h : ∀ i, i.val < cutoff → V i = U i) :
    latePoint n cutoff current alpha omega tau a offset handle coeff V =
      latePoint n cutoff current alpha omega tau a offset handle coeff U := by
  unfold latePoint
  rw [h current hcurrent, prefixPoint_respects_known_columns n cutoff alpha handle coeff V U h]

theorem continuous_prefixPoint
    (n cutoff : ℕ) (alpha : ℝ) (handle : E) (coeff : Fin (n + 3) → ℝ) :
    Continuous (prefixPoint n cutoff alpha handle coeff) := by
  apply Continuous.add continuous_const
  apply continuous_finset_sum
  intro i _
  by_cases hi : i.val < cutoff
  · simp only [if_pos hi]
    convert! (continuous_apply i).const_smul (coeff i) using 1 <;> infer_instance
  · simpa only [if_neg hi] using (continuous_const (y := (0 : E)))

theorem continuous_latePoint
    (n cutoff : ℕ) (current : Fin (n + 3)) (alpha omega tau a offset : ℝ)
    (handle : E) (coeff : Fin (n + 3) → ℝ) :
    Continuous (latePoint n cutoff current alpha omega tau a offset handle coeff) := by
  have hc : Continuous (fun frame : Fin (n + 3) → E => (omega / 2) • frame current) := by
    convert! (continuous_apply current).const_smul (omega / 2) using 1 <;> infer_instance
  have hp : Continuous (fun frame : Fin (n + 3) → E =>
      a • (-(tau • prefixPoint n cutoff alpha handle coeff frame) + offset • handle)) := by
    convert! ((((continuous_prefixPoint n cutoff alpha handle coeff).const_smul tau).neg.add
      (continuous_const (y := offset • handle))).const_smul a) using 1
  have hy := (coordinateIsometry (E := E) ((1 : Fin 3), (0 : Fin 2))).continuous.comp hc
  have hs := (coordinateIsometry (E := E) ((2 : Fin 3), (0 : Fin 2))).continuous.comp hp
  convert! hy.add hs using 1

theorem actual_history_late_query_continuous
    (n cutoff r : ℕ) (current : Fin (n + 3)) (publicPart : E →L[ℝ] E)
    (alpha omega tau a offset c invGamma : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ) :
    Continuous (actualHistoryLateQuery n cutoff r current publicPart
      alpha omega tau a offset c invGamma handle initial coeff) := by
  exact (continuous_latePoint n cutoff current alpha omega tau a offset handle coeff).comp
    (continuous_guesses n publicPart c invGamma initial r)

theorem prefixPoint_has_zero_unrevealed_projection
    (n cutoff : ℕ) (alpha : ℝ) (handle : E) (coeff : Fin (n + 3) → ℝ)
    (V : Fin (n + 3) → E) (hV : Orthonormal ℝ V) (j : Fin (n + 3))
    (hj : cutoff ≤ j.val) (hhandle : inner ℝ (V j) handle = 0) :
    inner ℝ (V j) (prefixPoint n cutoff alpha handle coeff V) = 0 := by
  unfold prefixPoint
  rw [inner_add_right, real_inner_smul_right, hhandle, mul_zero, zero_add, inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < cutoff
  · have hji : j ≠ i := by intro he; subst i; omega
    simp only [if_pos hi, real_inner_smul_right, orthonormal_iff_ite.mp hV, if_neg hji, mul_zero]
  · simp only [if_neg hi, inner_zero_right]

theorem latePoint_has_zero_unrevealed_projections
    (n cutoff : ℕ) (current : Fin (n + 3)) (hcurrent : current.val < cutoff)
    (alpha omega tau a offset : ℝ) (handle : E) (coeff : Fin (n + 3) → ℝ)
    (V : Fin (n + 3) → E) (hV : Orthonormal ℝ V) (j : Fin (n + 3))
    (hj : cutoff ≤ j.val) (hhandle : inner ℝ (V j) handle = 0) :
    inner ℝ (V j) (latePoint n cutoff current alpha omega tau a offset handle coeff V (1, 0)) = 0 ∧
    inner ℝ (V j) (latePoint n cutoff current alpha omega tau a offset handle coeff V (2, 0)) = 0 := by
  have hji : j ≠ current := by intro he; subst j; omega
  have hp := prefixPoint_has_zero_unrevealed_projection n cutoff alpha handle coeff V hV j hj hhandle
  constructor
  · simp [latePoint, coordinateIsometry, real_inner_smul_right, orthonormal_iff_ite.mp hV, hji]
  · simp [latePoint, coordinateIsometry, real_inner_smul_right, inner_add_right,
      inner_neg_right, hhandle, hp]

end FangqingLateQueryFromHistory
end

section
-- Source component: ActualShellMinimizerPublicCoefficients.lean

open scoped Topology

namespace FangqingActualShellMinimizerPublicCoefficients

open FangqingAmplifier FangqingPacketLeakage FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalPacketDistanceGapBounds FangqingShellMinimizerTransfer OriginalCanonicalPacketTailSupport
  OriginalPhysicalPacketExistence

universe u
variable {A0 B0 W : Type u}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem actual_inner_shell_minimizer_is_actual_raw_minimizer
    (P : FlatCubic.Profile) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cw scale lam R A gain : ℝ) (phi : ℝ → ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 < q)
    (hscale : 0 < scale) (hlam : 0 < lam) (homega : omega = Cw * lam * q ^ 2)
    (hR : 0 < R) (hA : 0 < A) (hcore : ∀ t, |t| < 1 → phi t = t)
    (Z : PhysicalSpace A0 B0 W) (hzR : ‖Z‖ < R) (hzA : ‖Z‖ < A)
    (hmin : ∀ Y,
      inactiveShell (QPhysical q (scale * lam) C)
        (fun z => scale * edgeSum (FlatCubic.edge P delta omega)
          (pathDirection n (physicalFrame C h n tail)) z) R gain Z -
          localizedSeed theta phi R A ((2 * Cw * (scale * lam) * distanceScale q omega) * A)
            (mkPhysical h 0 0) Z ≤
      inactiveShell (QPhysical q (scale * lam) C)
        (fun z => scale * edgeSum (FlatCubic.edge P delta omega)
          (pathDirection n (physicalFrame C h n tail)) z) R gain Y -
          localizedSeed theta phi R A ((2 * Cw * (scale * lam) * distanceScale q omega) * A)
            (mkPhysical h 0 0) Y) :
    ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
      (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
      rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
        (scale * (2 * omega ^ 2 / Real.sqrt q)) Y := by
  let s := 2 * Cw * (scale * lam) * distanceScale q omega
  let Q : PhysicalSpace A0 B0 W → ℝ := QPhysical q (scale * lam) C
  let g : PhysicalSpace A0 B0 W → ℝ := fun z => scale * edgeSum (FlatCubic.edge P delta omega)
    (pathDirection n (physicalFrame C h n tail)) z
  let raw := rawPacket C h n tail (FlatCubic.edge P delta omega) q (scale * lam) scale
    (scale * (2 * omega ^ 2 / Real.sqrt q))
  let shell := fun z => inactiveShell Q g R gain z -
    localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
  have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
    have h1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
    have h2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
    change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 =
      ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at h1
    change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at h2
    rw [hh, norm_zero] at h2
    rw [norm_zero] at h1
    nlinarith only [h1, h2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
  have hlit : raw = (fun y => Q y + g y - s * inner ℝ (mkPhysical h 0 0) y) := by
    funext Y
    have hi : inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y = inner ℝ h Y.fst.fst := by
      change (inner ℝ h Y.fst.fst + inner ℝ (0 : B0) Y.fst.snd) + inner ℝ (0 : W) Y.snd = _
      simp only [inner_zero_left, add_zero]
    dsimp only [raw]
    rw [rawPacket_literal, actual_seed_ratio q omega Cw lam scale hq homega, hi]
  have heq := actual_active_shell_eventually_eq_raw Q g phi R A s gain hR hA
    (mkPhysical h 0 0) Z hhandle hcore hzR hzA
  have hloc : raw =ᶠ[𝓝 Z] shell := by
    rw [hlit]
    exact heq.symm
  have hc := actual_raw_packet_contDiff_strongConvex P C h hh n tail ht delta omega q
    (scale * lam) scale (scale * (2 * omega ^ 2 / Real.sqrt q)) hd hdw hq.le
      (mul_pos hscale hlam).le hscale.le
  exact (global_minimum_of_actual_local_eq raw shell (scale * lam) (mul_pos hscale hlam)
    hc.1 hc.2 Z hmin hloc).1

theorem actual_shell_minimizer_has_orientation_independent_public_coefficients
    (P : FlatCubic.Profile) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (hh : ‖h‖ = 1)
    (n : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (delta omega q Cw scale lam R A gain : ℝ) (phi : ℝ → ℝ)
    (hd : 0 < delta) (hdw : delta ≤ omega) (hq : 0 < q)
    (hscale : 0 < scale) (hlam : 0 < lam) (homega : omega = Cw * lam * q ^ 2)
    (hR : 0 < R) (hA : 0 < A) (hcore : ∀ t, |t| < 1 → phi t = t)
    (Z : PhysicalSpace A0 B0 W) (hzR : ‖Z‖ < R) (hzA : ‖Z‖ < A)
    (hmin : ∀ Y,
      inactiveShell (QPhysical q (scale * lam) C)
        (fun z => scale * edgeSum (FlatCubic.edge P delta omega)
          (pathDirection n (physicalFrame C h n tail)) z) R gain Z -
          localizedSeed theta phi R A ((2 * Cw * (scale * lam) * distanceScale q omega) * A)
            (mkPhysical h 0 0) Z ≤
      inactiveShell (QPhysical q (scale * lam) C)
        (fun z => scale * edgeSum (FlatCubic.edge P delta omega)
          (pathDirection n (physicalFrame C h n tail)) z) R gain Y -
          localizedSeed theta phi R A ((2 * Cw * (scale * lam) * distanceScale q omega) * A)
            (mkPhysical h 0 0) Y) :
    Z = coordinatePoint C h n tail (canonicalScalarPair P delta omega n q lam).1
      (canonicalScalarPair P delta omega n q lam).2 := by
  exact actual_raw_minimizer_uses_public_coefficients P C h hh n tail ht delta omega q scale lam
    hd hdw hq.le hscale hlam Z
    (actual_inner_shell_minimizer_is_actual_raw_minimizer P C h hh n tail ht delta omega q Cw
      scale lam R A gain phi hd hdw hq hscale hlam homega hR hA hcore Z hzR hzA hmin)

end FangqingActualShellMinimizerPublicCoefficients
end

section
-- Source component: CanonicalExternalRelayWorlds.lean

open scoped ContDiff NNReal

namespace FangqingCanonicalExternalRelayWorlds

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingPhysicalRelayValueGap FangqingRelayExternalSlackBudgets
  FangqingRelayStationarity FangqingExternalPhysicalRelayValidity
  FangqingActualShellMinimizerPublicCoefficients OriginalCanonicalPacketTailSupport

noncomputable section

set_option maxHeartbeats 7500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def Validity (n : ℕ) (beta lam a sigma reward L mu rho M Ctheta ell Cgap Egap : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (X0 : Blocks n E) : Prop :=
  let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
  (∀ t z, |FangqingRelayStationarity.delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M) ∧
  (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
  ((reward + M) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma / 2) ∧
  ContDiff ℝ 2 J ∧
  (∀ x y, ‖gradient J x - gradient J y‖ ≤ L * ‖x - y‖) ∧
  FangqingRelayGlobalJointClass.HessianRate J rho ∧
  (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) mu
    (FangqingRelayDualAssembly.negativeFamily n beta lam a sigma reward h0 h1 m0 m1 gate x)) ∧
  ∃ Y S : Blocks n E → (Fin (n + 1) → E),
    (∀ (X : Blocks n E) yy ss,
      family n beta lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
        exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X) ∧
    Differentiable ℝ (exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S) ∧
    (∀ X, exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X =
      sSup (Set.range (FangqingRelayValueBridge.curryF n beta lam a sigma reward h0 h1 m0 m1 gate X))) ∧
    let Phi := exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S
    Phi X0 - sInf (Set.range Phi) ≤ Cgap * ((n + 1 : ℕ) : ℝ) * Egap

universe u

theorem actual_external_worlds_have_public_canonical_centers
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw KDlower : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Cgap ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      let Cs := 2 * Cw
      let CA := 1 + 2 * Ks * Cs + 2 * Cw * (Cm + 2)
      let Cp := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      ∃ cL cq cg : ℝ, 0 < cL ∧ cL ≤ 1 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧
      ∀ (A0 B0 W : Type u)
        [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
        [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
        (tail : Fin (outer + 1) → Fin (nt + 2) → W)
        (L mu eps r rhop q delta omega : ℝ),
        (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
        0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
        1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) → 0 < delta → delta ≤ omega →
        ((nt + 2 : ℕ) : ℝ) ≤ Cm * q →
        let Li := cL * L
        let ri := r / Real.sqrt cL
        let scale := cg * rhop
        let barlam := (8 * mu) / scale
        omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mu KD eps →
        let nu := scale * barlam
        let D := distanceScale q omega
        let A := CA * D
        let R := 2 * A
        let seed := Cs * nu * D
        let Mpath : ℝ := (4 * Ce : ℝ) * scale * omega
        let gain := (16 * K + 1) * Mpath
        let H0 := fun t => inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
        let H1 := fun t z => H0 t z - localizedSeed theta phi R A (seed * A) (mkPhysical (h t) 0 0) z
        let Z : Fin (outer + 1) → PhysicalSpace A0 B0 W := fun t =>
          coordinatePoint C (h t) nt (tail t) (canonicalScalarPair P delta omega nt q barlam).1
            (canonicalScalarPair P delta omega nt q barlam).2
        (∀ t, AnalyticClass (H0 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t, AnalyticClass (H1 t) (4 * mu) (Cp * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
        (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
        (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
        (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
          3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
        ∀ center : Fin outer → PhysicalSpace A0 B0 W,
        let a := relayAmplitude 1 (Li / mu) ri
        let ell := width Li mu KD eps
        let rw := reward Cdelta 8 Li KD eps
        let h0 := fun t => reduced (H0 t) mu
        let h1 := fun t => reduced (H1 t) mu
        let m0 := fun t => H0 t 0
        let m1 := fun t => H1 t (Z t)
        let gate := fun j => scaledGate theta (a * ell) (center j)
        let X0 : Blocks outer (PhysicalSpace A0 B0 W) :=
          WithLp.toLp 2 (Fin.cons ((-(seed / lam Li mu)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
        Validity outer Li (lam Li mu) a (sigma Li a csigma) rw L mu (rho L mu eps r)
          (rawBudget Cdelta 8 Li mu KD eps) Ctheta ell Cgap (energy L eps) h0 h1 m0 m1 gate X0 := by
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, hBuilder⟩ :=
    actual_external_physical_relay_validity.{u} P phi Bp left right Cm Cw KDlower
      hCm hCw hKDlower hp hl hr hcore
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r rhop q delta omega hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn
    Li ri scale barlam homega hDistance nu D A R seed Mpath gain H0 H1 Zc
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail L mu eps r rhop q delta omega hh ht
      hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn homega hDistance
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hs : 0 < scale := mul_pos hcg hrhop
  have hb : 0 < barlam := div_pos (by positivity) hs
  have hCs : 0 ≤ 2 * Cw := by linarith only [hCw, hCm]
  have hCmin : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
  have hminA : (2 * Cw * (Cm + 2)) * D < A := by
    have hnon : 0 ≤ 2 * Ks * (2 * Cw) := by positivity
    dsimp only [A]
    nlinarith only [hD, hnon]
  have hA : 0 < A := (mul_nonneg hCmin hD.le).trans_lt hminA
  have hAR : A ≤ R := by dsimp only [R]; linarith only [hA]
  have hR : 0 < R := hA.trans_le hAR
  have hEq : Z = Zc := by
    funext t
    apply actual_shell_minimizer_has_orientation_independent_public_coefficients P C (h t) (hh t)
      nt (tail t) (ht t) delta omega q Cw scale barlam R A gain phi hd hdw hq0 hs hb homega
      hR hA hcore (Z t) ((hNorm t).trans_lt (hminA.trans_le hAR))
      ((hNorm t).trans_lt hminA)
    exact hMin1 t
  rw [hEq] at hMin1 hNorm hLocalGap hBulk hCenters
  exact ⟨hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hCenters⟩

end
end FangqingCanonicalExternalRelayWorlds
end
