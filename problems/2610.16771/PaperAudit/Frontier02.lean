import Mathlib
import PaperAudit.Frontier01

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: ActiveShellLargerWidth.lean

open scoped ContDiff

namespace FangqingActiveShellLargerWidth

open FangqingActualInactivePacket FangqingActiveShellClass FangqingLocalizedSeedJets
  FangqingC2SmallPerturbation FangqingHessianTensorIsometry FangqingPublicShellProfiles

noncomputable section

theorem actual_large_width_curvature (Ks Cs nu D A : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hnu : 0 ≤ nu) (hA : 0 < A)
    (hwidth : 2 * Ks * Cs * D ≤ A) :
    Ks * ((Cs * nu * D) * A) / A ^ 2 ≤ nu / 2 := by
  have heq : Ks * ((Cs * nu * D) * A) / A ^ 2 = Ks * Cs * nu * D / A := by
    field_simp [ne_of_gt hA]
    <;> try ring
  rw [heq]
  apply (div_le_iff₀ hA).mpr
  have hm := mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ nu / 2)
  convert! hm using 1 <;> try ring

theorem larger_width_choice (Ks Cs Cmin D : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hCmin : 0 ≤ Cmin) (hD : 0 < D) :
    let A := (1 + 2 * Ks * Cs + Cmin) * D
    D ≤ A ∧ 2 * Ks * Cs * D ≤ A ∧ Cmin * D < A := by
  intro A
  have hk : 0 ≤ 2 * Ks * Cs := by positivity
  have hkD : 0 ≤ 2 * Ks * Cs * D := by positivity
  have hmD : 0 ≤ Cmin * D := by positivity
  dsimp [A]
  constructor
  · nlinarith only [hkD, hmD]
  constructor
  · nlinarith only [hmD, hD]
  · nlinarith only [hkD, hD]

universe u

theorem actual_seeded_shell_any_larger_width
    (phi : ℝ → ℝ) (B left right Cs : ℝ) (hCs : 0 ≤ Cs)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (F : Type u)
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (H0 : F → ℝ) (nu L0 rho0 D A R : ℝ) (handle : F),
      AnalyticClass H0 nu L0 rho0 → 0 ≤ nu → 0 ≤ L0 →
      0 < D → D ≤ A → 2 * Ks * Cs * D ≤ A → A ≤ R → ‖handle‖ ≤ 1 →
      let s := Cs * nu * D
      let H1 := fun z => H0 z - localizedSeed theta phi R A (s * A) handle z
      AnalyticClass H1 (nu / 2) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) := by
  obtain ⟨Ks, hKs, hSeed⟩ := universal_actual_seed_jets.{u} phi B left right hp hl hr
  refine ⟨Ks, hKs, ?_⟩
  intro F inst inst' inst'' H0 nu L0 rho0 D A R handle hH0 hnu hL0 hD hDA hwidth hAR hh s H1
  have hA : 0 < A := hD.trans_le hDA
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hSC, hSJ⟩ := hSeed F R A (s * A) handle hA hAR (mul_nonneg hs hA.le) hh
  have hH02 := FangqingFenchelEndpointClass.second_jet_bound_from_gradient_rate H0 L0 hL0 hH0.2.2.1
  have hH0Lip : ∀ x y, ‖iteratedFDeriv ℝ 2 H0 x - iteratedFDeriv ℝ 2 H0 y‖ ≤ rho0 * ‖x - y‖ := by
    intro x y
    rw [second_jet_difference_eq_hessian]
    exact hH0.2.2.2 x y
  let S := Ks * (s * A) / A ^ 2
  let T := Ks * (s * A) / A ^ 3
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hT : 0 ≤ T := by dsimp [T]; positivity
  obtain ⟨hc, hsc, h2, hLip⟩ := actual_small_perturbation H0
    (localizedSeed theta phi R A (s * A) handle) nu L0 rho0 S T hH0.1 hSC hH0.2.1 hS hT
    hH02 hH0Lip (hSJ 2 (by norm_num)) (hSJ 3 (by norm_num))
  have hsmall : S ≤ nu / 2 := actual_large_width_curvature Ks Cs nu D A hKs hCs hnu hA hwidth
  have hmod : nu / 2 ≤ nu - S := by linarith only [hsmall]
  exact class_of_actual_jets H1 (nu / 2) (L0 + S) (rho0 + T) (add_nonneg hL0 hS) hc (hsc.mono hmod) h2 hLip

end
end FangqingActiveShellLargerWidth
end

section
-- Source component: ShellMinimizerTransfer.lean

open scoped Topology ContDiff

namespace FangqingShellMinimizerTransfer

open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  FangqingRadialCollar FangqingRadialCollarEtaBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_collar_zero_inner (R : ℝ) (hR : 0 < R) (z : E) (hz : ‖z‖ ≤ R) : collar psi R z = 0 := by
  have hratio : ‖z‖ / R ≤ 1 := (div_le_one hR).mpr hz
  have hh := literal_paper_collar_eq psi psi_smooth.continuous psi_zero R hR z
  rw [eta, if_pos hratio, mul_zero] at hh
  exact hh.symm

theorem actual_active_shell_inner_eq (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain : ℝ) (hR : 0 < R) (hA : 0 < A) (handle z : E) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t) (hzR : ‖z‖ < R) (hzA : ‖z‖ < A) :
    inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z =
      Q z + g z - s * inner ℝ handle z := by
  have hin : |inner ℝ handle z| < A := by
    have h1 := abs_real_inner_le_norm handle z
    have h2 := mul_le_mul_of_nonneg_right hh (norm_nonneg z)
    rw [one_mul] at h2
    exact (h1.trans h2).trans_lt hzA
  have harg : |inner ℝ handle z / A| < 1 := by
    rw [abs_div, abs_of_pos hA]
    exact (div_lt_one hA).mpr hin
  have ht := actual_cutoff_one_inside R hR z (by linarith only [hzR, hR])
  have hc := actual_collar_zero_inner R hR z hzR.le
  dsimp [inactiveShell, localizedSeed, FangqingLinearProfileJetBounds.linearProfile]
  rw [ht, hc, hphi _ harg]
  simp only [one_mul, mul_zero, add_zero]
  field_simp [ne_of_gt hA]
  <;> try ring

theorem actual_active_shell_eventually_eq_raw (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain : ℝ) (hR : 0 < R) (hA : 0 < A) (handle z : E) (hh : ‖handle‖ ≤ 1)
    (hphi : ∀ t, |t| < 1 → phi t = t) (hzR : ‖z‖ < R) (hzA : ‖z‖ < A) :
    (fun z => inactiveShell Q g R gain z - localizedSeed theta phi R A (s * A) handle z)
      =ᶠ[𝓝 z] (fun z => Q z + g z - s * inner ℝ handle z) := by
  have hn : {y : E | ‖y‖ < min R A} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds (lt_min hzR hzA)
  filter_upwards [hn] with y hy
  exact actual_active_shell_inner_eq Q g phi R A s gain hR hA handle y hh hphi
    (lt_min_iff.mp hy).1 (lt_min_iff.mp hy).2

theorem global_minimum_of_actual_local_eq (F G : E → ℝ) (nu : ℝ) (hnu : 0 < nu)
    (hc : ContDiff ℝ 2 F) (hs : StrongConvexOn (Set.univ : Set E) nu F) (z : E)
    (hmin : ∀ y, G z ≤ G y) (heq : F =ᶠ[𝓝 z] G) :
    (∀ y, F z ≤ F y) ∧ (∀ y, (∀ w, F y ≤ F w) → y = z) := by
  have hloc : IsLocalMin F z := by
    filter_upwards [heq] with y hy
    rw [heq.eq_of_nhds, hy]
    exact hmin y
  have hgrad : gradient F z = 0 := by
    simp only [gradient, hloc.fderiv_eq_zero, map_zero]
  have hminF : ∀ y, F z ≤ F y := by
    intro y
    have hh := PacketCore.strongConvex_support F nu hs (hc.differentiable (by norm_num)) z y
    rw [hgrad, inner_zero_left] at hh
    have hn : 0 ≤ nu / 2 * ‖y - z‖ ^ 2 := by positivity
    linarith only [hh, hn]
  refine ⟨hminF, ?_⟩
  intro y hy
  have hgy := PacketCore.gradient_eq_zero_at_global_min F y hy
  have hh := PacketCore.strongConvex_gradient_distance F nu hnu hs (hc.differentiable (by norm_num)) z hminF y
  rw [hgy, norm_zero] at hh
  have hn : ‖y - z‖ = 0 := le_antisymm (nonpos_of_mul_nonpos_right hh hnu) (norm_nonneg (y - z))
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem actual_active_minimizer_preserved (Q g : E → ℝ) (phi : ℝ → ℝ)
    (R A s gain nu : ℝ) (hR : 0 < R) (hA : 0 < A) (hnu : 0 < nu)
    (handle z : E) (hh : ‖handle‖ ≤ 1) (hphi : ∀ t, |t| < 1 → phi t = t)
    (hzR : ‖z‖ < R) (hzA : ‖z‖ < A)
    (hmin : ∀ y, Q z + g z - s * inner ℝ handle z ≤ Q y + g y - s * inner ℝ handle y)
    (hc : ContDiff ℝ 2 (fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y))
    (hs : StrongConvexOn (Set.univ : Set E) nu
      (fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y)) :
    let H1 := fun y => inactiveShell Q g R gain y - localizedSeed theta phi R A (s * A) handle y
    (∀ y, H1 z ≤ H1 y) ∧ (∀ y, (∀ w, H1 y ≤ H1 w) → y = z) := by
  intro H1
  exact global_minimum_of_actual_local_eq H1 (fun y => Q y + g y - s * inner ℝ handle y) nu hnu hc hs z hmin
    (actual_active_shell_eventually_eq_raw Q g phi R A s gain hR hA handle z hh hphi hzR hzA)

end
end FangqingShellMinimizerTransfer
end

section
-- Source component: InactiveShellMinimum.lean

namespace FangqingInactiveShellMinimum

open FangqingInactiveShellClass FangqingPublicShellProfiles FangqingRadialCollar FangqingRadialCollarEtaBridge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_collar_nonnegative (R : ℝ) (hR : 0 < R) (z : E) : 0 ≤ collar psi R z := by
  have hh := literal_paper_collar_eq psi psi_smooth.continuous psi_zero R hR z
  rw [← hh]
  have heta : 0 ≤ eta psi (‖z‖ / R) := by
    by_cases hr : ‖z‖ / R ≤ 1
    · rw [eta, if_pos hr]
    · rw [eta, if_neg hr]
      apply intervalIntegral.integral_nonneg (le_of_lt (lt_of_not_ge hr))
      intro t ht
      exact mul_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht.1) (psi_range _).1
  exact mul_nonneg (sq_nonneg R) heta

theorem actual_inactive_minimum_zero (Q g : E → ℝ) (R gain : ℝ) (hR : 0 < R) (hgain : 0 ≤ gain)
    (hQ : ∀ z, 0 ≤ Q z) (hg : ∀ z, 0 ≤ g z) (hQ0 : Q 0 = 0) (hg0 : g 0 = 0) :
    ∀ z, inactiveShell Q g R gain 0 ≤ inactiveShell Q g R gain z := by
  have hcol0 := FangqingShellMinimizerTransfer.actual_collar_zero_inner R hR (0 : E) (by simpa using hR.le)
  intro z
  dsimp [inactiveShell]
  rw [hQ0, hg0, mul_zero, hcol0, mul_zero, zero_add, add_zero]
  have hc := mul_nonneg hgain (actual_collar_nonnegative R hR z)
  have hprod : 0 ≤ FangqingRadialGateBounds.scaledGate theta R 0 z * g z :=
    mul_nonneg (theta_range (‖z - (0 : E)‖ ^ 2 / R ^ 2)).1 (hg z)
  linarith only [hQ z, hc, hprod]

end
end FangqingInactiveShellMinimum
end

section
-- Source component: PhysicalPairedShellMinimizers.lean

open scoped BigOperators ContDiff

namespace FangqingPhysicalPairedShellMinimizers

open FangqingAmplifier FangqingPacketLeakage FangqingPathEdgeRegularity
  FangqingActualInactivePacket FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingActiveShellLargerWidth FangqingShellMinimizerTransfer FangqingInactiveShellMinimum
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds

set_option maxHeartbeats 3000000

noncomputable section

universe u

theorem actual_physical_paired_shell_same_minimum
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      AnalyticClass F0 nu L0 rho0 ∧
      AnalyticClass F1 (nu / 2) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ 2 * Cw := by positivity
  have hCmin : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
  obtain ⟨Ce, K, hK, Kc, hKc, hInactive⟩ := actual_inactive_packet_class.{u} P
  obtain ⟨Ks, hKs, hWide⟩ := actual_seeded_shell_any_larger_width.{u} phi Bp left right (2 * Cw) hCs hp hl hr
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hwidth, hCminA⟩ := larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hR : 0 < R := hA.trans_le hAR
  have hv := physicalFrame_orthonormal C h hh n tail ht
  obtain ⟨hF0, _, _⟩ := hInactive A0 B0 W q nu scale delta omega R C (n + 2) (physicalFrame C h n tail)
    hq0.le hnu.le hscale.le hd hdw hR hv
  have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
    change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
  have hL0 : 0 ≤ L0 := by dsimp [L0, M, gain]; positivity
  have hF1 := hWide (PhysicalSpace A0 B0 W) F0 nu L0 rho0 D A R (mkPhysical h 0 0)
    hF0 hnu.le hL0 hD hDA hwidth hAR hhandle
  have hQnon : ∀ Y : PhysicalSpace A0 B0 W, 0 ≤ Q Y := by
    intro Y
    rw [show Q Y = (1 / 2 : ℝ) * inner ℝ (HPhysical q nu C Y) Y from QPhysical_eq_half_inner q nu C Y]
    exact mul_nonneg (by norm_num) ((mul_nonneg hnu.le (sq_nonneg _)).trans (physical_rayleigh_bounds q nu hq0.le hnu.le C Y).1)
  have hgnon : ∀ Y : PhysicalSpace A0 B0 W, 0 ≤ g Y := by
    intro Y
    apply mul_nonneg hscale.le
    unfold pathEdge edgeSum
    exact Finset.sum_nonneg (fun i _ => actual_edge_nonnegative P delta omega hd hdw _)
  have hg0 : g 0 = 0 := by
    have hj := (FlatCubic.edge_flat_jets_closed P delta omega 0 hd hdw (by simp only [abs_zero]; linarith only [hd])).1
    simp only [g, pathEdge, edgeSum, inner_zero_right, hj, Finset.sum_const_zero, mul_zero]
  have hQ0 : Q 0 = 0 := by simp [Q, QPhysical]
  have hGain : 0 ≤ gain := by dsimp [gain, M]; positivity
  have hMin0 := actual_inactive_minimum_zero Q g R gain hR hGain hQnon hgnon hQ0 hg0
  refine ⟨hF0, hF1, hMin0, ?_⟩
  obtain ⟨Z, hm, hu, hnorm, hgap, hbulk⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
    delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
  have hzA : ‖Z‖ < A := hnorm.trans_lt hCminA
  have hzR : ‖Z‖ < R := hzA.trans_le hAR
  have hseed := actual_seed_ratio q omega Cw lam scale hq0 homega
  have hi : ∀ Y : PhysicalSpace A0 B0 W, inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y = inner ℝ h Y.fst.fst := by
    intro Y
    change (inner ℝ h Y.fst.fst + inner ℝ (0 : B0) Y.fst.snd) + inner ℝ (0 : W) Y.snd = _
    simp only [inner_zero_left, add_zero]
  have hRaw : ∀ Y : PhysicalSpace A0 B0 W,
      rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y =
        Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
    intro Y
    rw [rawPacket_literal, hseed, hi]
    rfl
  have hrawmin : ∀ Y, Q Z + g Z - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Z ≤
      Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
    intro Y
    rw [← hRaw Z, ← hRaw Y]
    exact hm Y
  obtain ⟨hm1, hu1⟩ := actual_active_minimizer_preserved Q g phi R A s gain (nu / 2) hR hA (half_pos hnu)
    (mkPhysical h 0 0) Z hhandle hcore hzR hzA hrawmin hF1.1 hF1.2.1
  have hzval := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h 0 0) Z hhandle hcore hzR hzA
  have h0val := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h 0 0) (0 : PhysicalSpace A0 B0 W)
    hhandle hcore (by simpa using hR) (by simpa using hA)
  refine ⟨Z, hm1, hu1, hnorm, ?_, hbulk⟩
  change (inactiveShell Q g R gain 0 - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) 0) -
    (inactiveShell Q g R gain Z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) Z) ≤ _
  rw [hzval, h0val, ← hRaw Z, ← hRaw 0]
  exact hgap

end
end FangqingPhysicalPairedShellMinimizers
end

section
-- Source component: SeedWidthMonotonic.lean

namespace FangqingSeedWidthMonotonic

theorem actual_seed_rates_antitone_width (Ks s A0 A : ℝ)
    (hKs : 0 ≤ Ks) (hs : 0 ≤ s) (hA0 : 0 < A0) (hAA : A0 ≤ A) :
    Ks * (s * A) / A ^ 2 ≤ Ks * (s * A0) / A0 ^ 2 ∧
    Ks * (s * A) / A ^ 3 ≤ Ks * (s * A0) / A0 ^ 3 := by
  have hA : 0 < A := hA0.trans_le hAA
  have heq1 (B : ℝ) (hB : 0 < B) : Ks * (s * B) / B ^ 2 = Ks * s / B := by
    field_simp [ne_of_gt hB]
    <;> try ring
  have heq2 (B : ℝ) (hB : 0 < B) : Ks * (s * B) / B ^ 3 = Ks * s / B ^ 2 := by
    field_simp [ne_of_gt hB]
    <;> try ring
  constructor
  · rw [heq1 A hA, heq1 A0 hA0]
    exact div_le_div_of_nonneg_left (mul_nonneg hKs hs) hA0 hAA
  · rw [heq2 A hA, heq2 A0 hA0]
    exact div_le_div_of_nonneg_left (mul_nonneg hKs hs) (sq_pos_of_pos hA0)
      (pow_le_pow_left₀ hA0.le hAA 2)

end FangqingSeedWidthMonotonic
end

section
-- Source component: PairedShellScaleBudgets.lean

namespace FangqingPairedShellScaleBudgets

noncomputable section

theorem actual_original_rate_budgets (Ce K Kc Ks Cs Cw q nu scale omega D R : ℝ)
    (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hKc : 0 ≤ Kc) (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs)
    (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale)
    (homega : 0 < omega) (hDomega : omega ≤ D)
    (hscaleomega : scale * omega = Cw * nu * q ^ 2)
    (hRA : (1 + 2 * Ks * Cs) * D ≤ R) :
    let A := (1 + 2 * Ks * Cs) * D
    let s := Cs * nu * D
    let M := 4 * Ce * scale * omega
    let gain := (16 * K + 1) * M
    let S := Ks * (s * A) / A ^ 2
    let T := Ks * (s * A) / A ^ 3
    nu * (q + 2) + 16 * K * M + gain * Kc + S ≤
      (7 / 2 + 4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc)) * nu * q ^ 2 ∧
    K * (8 * Ce * scale) + 21 * K * M / R + gain * (Kc / R) + T ≤
      (8 * K * Ce + 4 * Ce * (21 * K + (16 * K + 1) * Kc) + Ks * Cs) * scale := by
  intro A s M gain S T
  have hD : 0 < D := homega.trans_le hDomega
  have hCA : 1 ≤ 1 + 2 * Ks * Cs := by
    have hm : 0 ≤ 2 * Ks * Cs := by positivity
    linarith only [hm]
  have hDA : D ≤ A := by
    have hh := mul_le_mul_of_nonneg_right hCA hD.le
    simpa only [one_mul] using hh
  have hA : 0 < A := hD.trans_le hDA
  have hR : 0 < R := hA.trans_le hRA
  have hq2 : 1 ≤ q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hnuq : nu ≤ nu * q ^ 2 := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hq2 hnu
  have hCwq : nu * q ^ 2 ≤ Cw * nu * q ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hCw (mul_nonneg hnu (sq_nonneg q))
    convert! hh using 1 <;> try ring
  have hnuscale : nu ≤ scale * omega := by rw [hscaleomega]; exact hnuq.trans hCwq
  have hS : S ≤ nu / 2 := FangqingActiveShellClass.actual_width_curvature_reserve Ks Cs nu D hKs hCs hnu hD
  have hqlinear : q + 2 ≤ 3 * q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hnulinear := mul_le_mul_of_nonneg_left hqlinear hnu
  have hfirst : nu * (q + 2) + S ≤ (7 / 2 : ℝ) * nu * q ^ 2 := by nlinarith only [hnulinear, hS, hnuq]
  have hMpart : 16 * K * M + gain * Kc =
      4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc) * nu * q ^ 2 := by
    dsimp [gain, M]
    calc
      _ = 4 * Ce * (16 * K + (16 * K + 1) * Kc) * (scale * omega) := by ring
      _ = _ := by rw [hscaleomega]; ring
  have hRomega : omega ≤ R := hDomega.trans (hDA.trans hRA)
  have hMR : M / R ≤ 4 * Ce * scale := by
    apply (div_le_iff₀ hR).mpr
    exact mul_le_mul_of_nonneg_left hRomega (by positivity : 0 ≤ 4 * Ce * scale)
  have hmiddle := mul_le_mul_of_nonneg_left hMR
    (by positivity : 0 ≤ 21 * K + (16 * K + 1) * Kc)
  have hmiddle' : 21 * K * M / R + gain * (Kc / R) ≤
      (21 * K + (16 * K + 1) * Kc) * (4 * Ce * scale) := by
    convert! hmiddle using 1 <;> dsimp [gain] <;> try ring
  have hnuD : nu ≤ scale * D := hnuscale.trans (mul_le_mul_of_nonneg_left hDomega hscale)
  have hnuDA : nu * D ≤ scale * A ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hnuD hD.le
    have hsquare := pow_le_pow_left₀ hD.le hDA 2
    have hl := mul_le_mul_of_nonneg_left hsquare hscale
    nlinarith only [hh, hl]
  have hTeq : T = Ks * Cs * nu * D / A ^ 2 := by
    dsimp [T, s]
    field_simp [ne_of_gt hA]
    <;> try ring
  have hT : T ≤ Ks * Cs * scale := by
    rw [hTeq]
    apply (div_le_iff₀ (sq_pos_of_pos hA)).mpr
    convert! mul_le_mul_of_nonneg_left hnuDA (mul_nonneg hKs hCs) using 1 <;> try ring
  constructor
  · nlinarith only [hfirst, hMpart]
  · nlinarith only [hmiddle', hT]

theorem universal_hessian_scale_choice (C : ℝ) (hC : 0 ≤ C) :
    ∃ cg : ℝ, 0 < cg ∧ ∀ rho : ℝ, 0 ≤ rho → C * (cg * rho) ≤ rho := by
  let cg := 1 / (C + 1)
  have hcg : 0 < cg := by dsimp [cg]; positivity
  have hbudget : C * cg ≤ 1 := by
    dsimp [cg]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < C + 1)).mpr
    linarith only [hC]
  refine ⟨cg, hcg, ?_⟩
  intro rho hrho
  have hh := mul_le_mul_of_nonneg_right hbudget hrho
  convert! hh using 1 <;> try ring

end
end FangqingPairedShellScaleBudgets
end

section
-- Source component: WidePairedShellRateBudgets.lean

namespace FangqingWidePairedShellRateBudgets

open FangqingPairedShellScaleBudgets FangqingSeedWidthMonotonic

noncomputable section

theorem actual_wider_seed_original_rates (Ce K Kc Ks Cs Cw Cmin q nu scale omega D R : ℝ)
    (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hKc : 0 ≤ Kc) (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs)
    (hCmin : 0 ≤ Cmin) (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale)
    (homega : 0 < omega) (hDomega : omega ≤ D)
    (hscaleomega : scale * omega = Cw * nu * q ^ 2)
    (hRA : (1 + 2 * Ks * Cs + Cmin) * D ≤ R) :
    let A := (1 + 2 * Ks * Cs + Cmin) * D
    let s := Cs * nu * D
    let M := 4 * Ce * scale * omega
    let gain := (16 * K + 1) * M
    nu * (q + 2) + 16 * K * M + gain * Kc + Ks * (s * A) / A ^ 2 ≤
      (7 / 2 + 4 * Ce * Cw * (16 * K + (16 * K + 1) * Kc)) * nu * q ^ 2 ∧
    K * (8 * Ce * scale) + 21 * K * M / R + gain * (Kc / R) + Ks * (s * A) / A ^ 3 ≤
      (8 * K * Ce + 4 * Ce * (21 * K + (16 * K + 1) * Kc) + Ks * Cs) * scale := by
  intro A s M gain
  let A0 := (1 + 2 * Ks * Cs) * D
  have hD : 0 < D := homega.trans_le hDomega
  have hA0 : 0 < A0 := by dsimp [A0]; positivity
  have hAA : A0 ≤ A := by
    dsimp [A0, A]
    nlinarith only [mul_nonneg hCmin hD.le]
  have hs : 0 ≤ s := by dsimp [s]; positivity
  obtain ⟨hS, hT⟩ := actual_seed_rates_antitone_width Ks s A0 A hKs hs hA0 hAA
  obtain ⟨hL, hr⟩ := actual_original_rate_budgets Ce K Kc Ks Cs Cw q nu scale omega D R
    hCe hK hKc hKs hCs hCw hq hnu hscale homega hDomega hscaleomega (hAA.trans hRA)
  constructor
  · exact (add_le_add (le_refl _) hS).trans hL
  · exact (add_le_add (le_refl _) hT).trans hr

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_class_reserve (F : E → ℝ) (nu nu' L L' rho rho' : ℝ)
    (hF : FangqingActualInactivePacket.AnalyticClass F nu L rho)
    (hnu : nu' ≤ nu) (hL : L ≤ L') (hr : rho ≤ rho') :
    FangqingActualInactivePacket.AnalyticClass F nu' L' rho' := by
  refine ⟨hF.1, hF.2.1.mono hnu, ?_, ?_⟩
  · intro x y
    exact (hF.2.2.1 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))
  · intro x y
    exact (hF.2.2.2 x y).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

end
end FangqingWidePairedShellRateBudgets
end

section
-- Source component: RawEndpointDifferenceJets.lean

open scoped ContDiff

namespace FangqingRawEndpointDifferenceJets

open FangqingLocalizedSeedJets FangqingActiveShellClass FangqingPublicShellProfiles

noncomputable section

universe u

theorem actual_endpoint_difference_all_jets (phi : ℝ → ℝ) (B left right : ℝ)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    ∀ (R A D amp : ℝ) (handle : E) (H : E → ℝ),
      0 < D → D ≤ A → A ≤ R → 0 ≤ amp → ‖handle‖ ≤ 1 →
      let difference := fun z => (H z - localizedSeed theta phi R A amp handle z) - H z
      ContDiff ℝ 3 difference ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j difference z‖ ≤ Kd * amp / D ^ j) ∧
      (∀ z, |difference z| ≤ Kd * amp) := by
  obtain ⟨Kd, hKd, hj⟩ := universal_actual_seed_jets.{u} phi B left right hp hl hr
  refine ⟨Kd, hKd, ?_⟩
  intro E inst inst' R A D amp handle H hD hDA hAR hamp hh difference
  obtain ⟨hc, hb⟩ := hj E R A amp handle (hD.trans_le hDA) hAR hamp hh
  have heq : difference = fun z => -localizedSeed theta phi R A amp handle z := by
    funext z
    dsimp [difference]
    ring
  rw [heq]
  have hall : ∀ j, j ≤ 3 → ∀ z,
      ‖iteratedFDeriv ℝ j (fun z => -localizedSeed theta phi R A amp handle z) z‖ ≤ Kd * amp / D ^ j := by
    intro j hj z
    change ‖iteratedFDeriv ℝ j (-(localizedSeed theta phi R A amp handle)) z‖ ≤ _
    rw [iteratedFDeriv_neg_apply, norm_neg]
    exact (hb j hj z).trans (div_le_div_of_nonneg_left (mul_nonneg hKd hamp)
      (pow_pos hD j) (pow_le_pow_left₀ hD.le hDA j))
  refine ⟨hc.neg, hall, ?_⟩
  intro z
  have hh := hall 0 (by norm_num) z
  simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, div_one] using hh

end
end FangqingRawEndpointDifferenceJets
end

section
-- Source component: PairedShellAnalyticItems.lean

open scoped ContDiff

namespace FangqingPairedShellAnalyticItems

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingActiveShellLargerWidth
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingPhysicalPairedShellMinimizers FangqingRawEndpointDifferenceJets
  FangqingWidePairedShellRateBudgets

noncomputable section

set_option maxHeartbeats 4000000

universe u

theorem actual_paired_shell_analytic_items
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      AnalyticClass F0 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      AnalyticClass F1 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      ContDiff ℝ 3 (fun z => F1 z - F0 z) ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (fun z => F1 z - F0 z) z‖ ≤ Kd * (s * A) / D ^ j) ∧
      (∀ z, |F1 z - F0 z| ≤ Kd * (s * A)) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) := by
  obtain ⟨Ce, K, hK, Kc, hKc, Ks, hKs, hPhysical⟩ :=
    actual_physical_paired_shell_same_minimum.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  obtain ⟨Kd, hKd, hDiff⟩ := actual_endpoint_difference_all_jets.{u} phi Bp left right hp hl hr
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
    nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0 CL Crho
  obtain ⟨hF0, hF1, hRest⟩ := hPhysical A0 B0 W C h n tail delta omega q scale lam
    hh ht hd hdw hq hscale hlam homega hn
  have hCw1 : 1 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCmin : 0 ≤ Cmin := by dsimp [Cmin]; positivity
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hWidth, hMinA⟩ := larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hRA : (1 + 2 * Ks * Cs + Cmin) * D ≤ R := hAR
  have hsqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  have hqp : 1 ≤ q * Real.sqrt q := by
    nlinarith only [hq, hsqrt, mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hsqrt)]
  have hDomega : omega ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hqp hw.le
    simpa only [one_mul, D, distanceScale] using hh
  have hscaleomega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; dsimp [nu]; ring
  obtain ⟨hL, hrho⟩ := actual_wider_seed_original_rates (Ce : ℝ) K Kc Ks Cs Cw Cmin q nu scale omega D R
    Ce.coe_nonneg hK hKc hKs hCs hCmin hCw1 hq hnu.le hscale.le hw hDomega hscaleomega hRA
  have hS : 0 ≤ Ks * (s * A) / A ^ 2 := by positivity
  have hT : 0 ≤ Ks * (s * A) / A ^ 3 := by positivity
  have hL0 : L0 ≤ CL * nu * q ^ 2 := (le_add_of_nonneg_right hS).trans hL
  have hr0 : rho0 ≤ Crho * scale := (le_add_of_nonneg_right hT).trans hrho
  have hClass0 := actual_class_reserve F0 nu (nu / 2) L0 (CL * nu * q ^ 2) rho0 (Crho * scale)
    hF0 (by linarith only [hnu]) hL0 hr0
  have hClass1 := actual_class_reserve F1 (nu / 2) (nu / 2)
    (L0 + Ks * (s * A) / A ^ 2) (CL * nu * q ^ 2)
    (rho0 + Ks * (s * A) / A ^ 3) (Crho * scale) hF1 le_rfl hL hrho
  have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
    have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
    have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
    change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
    change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
    rw [hh, norm_zero] at hn2
    rw [norm_zero] at hn1
    nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
  obtain ⟨hDC, hDJ, hD0⟩ := hDiff (PhysicalSpace A0 B0 W) R A D (s * A) (mkPhysical h 0 0) F0
    hD hDA hAR (by positivity) hhandle
  exact ⟨hClass0, hClass1, hDC, hDJ, hD0, hRest⟩

end
end FangqingPairedShellAnalyticItems
end

section
-- Source component: ShellPrefixLocality.lean

open scoped Topology BigOperators

namespace FangqingShellPrefixLocality

open FangqingPacketLeakage

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [Fintype I]

noncomputable def selectedEdgeSum (g : ℝ → ℝ) (d : I → E) (selected : Finset I) (y : E) : ℝ :=
  ∑ i ∈ selected, g (inner ℝ (d i) y)

noncomputable def bundle (f : E → ℝ) (y : E) : ℝ × E × (E →L[ℝ] E) :=
  (f y, gradient f y, fderiv ℝ (gradient f) y)

theorem bundle_of_eventuallyEq (f g : E → ℝ) (y : E) (heq : f =ᶠ[𝓝 y] g) :
    bundle f y = bundle g y := by
  unfold bundle
  rw [heq.eq_of_nhds, heq.gradient_eq, heq.gradient.fderiv_eq]

theorem edgeSum_eventually_eq_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    edgeSum (FlatCubic.edge P delta Delta) d =ᶠ[𝓝 y]
      selectedEdgeSum (FlatCubic.edge P delta Delta) d selected := by
  classical
  have hi : ∀ i : I, ∀ᶠ z in 𝓝 y,
      i ∉ selected → FlatCubic.edge P delta Delta (inner ℝ (d i) z) = 0 := by
    intro i
    by_cases his : i ∈ selected
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h his))
    · have hc : Continuous (fun z : E => |inner ℝ (d i) z|) := (innerSL ℝ (d i)).continuous.abs
      have hn : {z : E | |inner ℝ (d i) z| < delta / 2} ∈ 𝓝 y :=
        (isOpen_lt hc continuous_const).mem_nhds (hflat i his)
      filter_upwards [hn] with z hz _
      exact (FlatCubic.edge_flat_jets_closed P delta Delta _ hd hdD hz.le).1
  have hall : ∀ᶠ z in 𝓝 y, ∀ i : I,
      i ∉ selected → FlatCubic.edge P delta Delta (inner ℝ (d i) z) = 0 :=
    Filter.eventually_all.mpr hi
  filter_upwards [hall] with z hz
  unfold edgeSum selectedEdgeSum
  symm
  exact Finset.sum_subset (Finset.subset_univ selected) (fun i _ hin => hz i hin)

theorem localized_eventually_eq_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (chi collar : ℝ → ℝ) (R scale : ℝ)
    (Q seed : E → ℝ) (y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    localized chi collar R Q (fun z => scale * edgeSum (FlatCubic.edge P delta Delta) d z + seed z)
      =ᶠ[𝓝 y]
    localized chi collar R Q
      (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta) d selected z + seed z) := by
  filter_upwards [edgeSum_eventually_eq_selected P delta Delta hd hdD d selected y hflat] with z hz
  simp only [localized, hz]

theorem actual_active_endpoint_bundle_selected
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (d : I → E) (selected : Finset I) (chi collar phi : ℝ → ℝ) (R scale s A : ℝ)
    (Q : E → ℝ) (handle y : E)
    (hflat : ∀ i ∉ selected, |inner ℝ (d i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) d scale s A handle) y =
      bundle (localized chi collar R Q
        (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta) d selected z + boundedSeed phi s A handle z)) y := by
  exact bundle_of_eventuallyEq _ _ y
    (localized_eventually_eq_selected P delta Delta hd hdD d selected chi collar R scale Q
      (boundedSeed phi s A handle) y hflat)

noncomputable def prefixEdges (n k : ℕ) : Finset (Fin (n + 2)) :=
  Finset.univ.filter (fun i => i.val < k)

theorem selected_path_prefix_invariant
    (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (g : ℝ → ℝ) :
    selectedEdgeSum g (pathDirection n v) (prefixEdges n k) =
      selectedEdgeSum g (pathDirection n w) (prefixEdges n k) := by
  classical
  funext z
  unfold selectedEdgeSum
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i.val < k := (Finset.mem_filter.mp hi).2
  have hleft : v i.castSucc = w i.castSucc := hprefix _ (by simp only [Fin.val_castSucc]; omega)
  have hright : v i.succ = w i.succ := hprefix _ (by simp only [Fin.val_succ]; omega)
  simp only [pathDirection, hleft, hright]

theorem actual_path_endpoint_prefix_bundle_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle y : E)
    (hflatV : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2)
    (hflatW : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n w i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n v) scale s A handle) y =
      bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n w) scale s A handle) y := by
  have hv : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflatV i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have hw : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n w i) y| < delta / 2 := by
    intro i hi
    apply hflatW i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  rw [actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hv,
    actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hw,
    selected_path_prefix_invariant n k v w hprefix]

noncomputable def maskedPrefix (n k : ℕ) (v : Fin (n + 3) → E) : Fin (n + 3) → E :=
  fun j => if j.val < k + 1 then v j else 0

theorem maskedPrefix_agrees (n k : ℕ) (v : Fin (n + 3) → E) :
    ∀ j : Fin (n + 3), j.val < k + 1 → v j = maskedPrefix n k v j := by
  intro j hj
  simp only [maskedPrefix, if_pos hj]

theorem maskedPrefix_invariant (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j) :
    maskedPrefix n k v = maskedPrefix n k w := by
  funext j
  by_cases hj : j.val < k + 1
  · simp only [maskedPrefix, if_pos hj, hprefix j hj]
  · simp only [maskedPrefix, if_neg hj]

theorem maskedPrefix_measurable [MeasurableSpace E] (n k : ℕ) :
    Measurable (maskedPrefix n k : (Fin (n + 3) → E) → (Fin (n + 3) → E)) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j.val < k + 1
  · simpa only [maskedPrefix, if_pos hj] using measurable_pi_apply j
  · simpa only [maskedPrefix, if_neg hj] using (measurable_const : Measurable (fun _ : Fin (n + 3) → E => (0 : E)))

noncomputable def virtualActiveEndpoint
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v : Fin (n + 3) → E)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle : E) : E → ℝ :=
  localized chi collar R Q (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta)
    (pathDirection n (maskedPrefix n k v)) (prefixEdges n k) z + boundedSeed phi s A handle z)

theorem virtualActiveEndpoint_prefix_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle : E) :
    virtualActiveEndpoint P delta Delta n k v chi collar phi R scale s A Q handle =
      virtualActiveEndpoint P delta Delta n k w chi collar phi R scale s A Q handle := by
  unfold virtualActiveEndpoint
  rw [maskedPrefix_invariant n k v w hprefix]

theorem actual_bundle_eq_virtual_on_flat_event
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E)
    (chi collar phi : ℝ → ℝ) (R scale s A : ℝ) (Q : E → ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    bundle (activeEndpoint chi collar phi R Q (FlatCubic.edge P delta Delta) (pathDirection n v) scale s A handle) y =
      bundle (virtualActiveEndpoint P delta Delta n k v chi collar phi R scale s A Q handle) y := by
  have hv : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflat i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  rw [actual_active_endpoint_bundle_selected P delta Delta hd hdD _ (prefixEdges n k) chi collar phi R scale s A Q handle y hv]
  unfold virtualActiveEndpoint
  rw [selected_path_prefix_invariant n k v (maskedPrefix n k v) (maskedPrefix_agrees n k v)]

end FangqingShellPrefixLocality
end

section
-- Source component: PhysicalPairedShellPrefixBundle.lean

set_option maxHeartbeats 800000
open scoped Topology BigOperators

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def actualInactive (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) : E → ℝ :=
  inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain

noncomputable def actualActive (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) : E → ℝ :=
  fun z => actualInactive P delta Delta n v Q scale R gain z - localizedSeed theta phi R A amplitude handle z

noncomputable def publicEndpoint (Q : E → ℝ) (R gain : ℝ) : E → ℝ :=
  fun z => Q z + gain * FangqingRadialCollar.collar psi R z

noncomputable def virtualInactive (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) : E → ℝ :=
  inactiveShell Q (fun z => scale * selectedEdgeSum (FlatCubic.edge P delta Delta)
    (pathDirection n (maskedPrefix n k v)) (prefixEdges n k) z) R gain

noncomputable def virtualActive (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ)
    (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) : E → ℝ :=
  fun z => virtualInactive P delta Delta n k v Q scale R gain z - localizedSeed theta phi R A amplitude handle z

theorem actualInactive_eventually_virtual
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    actualInactive P delta Delta n v Q scale R gain =ᶠ[𝓝 y]
      virtualInactive P delta Delta n k v Q scale R gain := by
  have hf : ∀ i ∉ prefixEdges n k, |inner ℝ (pathDirection n v i) y| < delta / 2 := by
    intro i hi
    apply hflat i
    by_contra hn
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩)
  have he := edgeSum_eventually_eq_selected P delta Delta hd hdD (pathDirection n v) (prefixEdges n k) y hf
  rw [selected_path_prefix_invariant n k v (maskedPrefix n k v) (maskedPrefix_agrees n k v)] at he
  filter_upwards [he] with z hz
  change Q z + FangqingRadialGateBounds.scaledGate theta R 0 z * (scale * edgeSum (FlatCubic.edge P delta Delta) (pathDirection n v) z) +
      gain * FangqingRadialCollar.collar psi R z = _
  simp only [hz]
  rfl

theorem actualActive_eventually_virtual
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    actualActive P delta Delta n v Q phi scale R gain A amplitude handle =ᶠ[𝓝 y]
      virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle := by
  filter_upwards [actualInactive_eventually_virtual P delta Delta hd hdD n k v Q scale R gain y hflat] with z hz
  exact congrArg (fun value => value - localizedSeed theta phi R A amplitude handle z) hz

theorem actual_inactive_full_bundle_public
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n v i) y| < delta / 2) :
    bundle (actualInactive P delta Delta n v Q scale R gain) y = bundle (publicEndpoint Q R gain) y := by
  apply bundle_of_eventuallyEq
  have hh := actualInactive_eventually_virtual P delta Delta hd hdD n 0 v Q scale R gain y (fun i _ => hflat i)
  filter_upwards [hh] with z hz
  rw [hz]
  simp only [virtualInactive, prefixEdges, Nat.not_lt_zero, Finset.filter_false,
    selectedEdgeSum, Finset.sum_empty, mul_zero, inactiveShell, mul_zero, add_zero, publicEndpoint]

theorem actual_paired_full_bundle_factors_through_prefix
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2) :
    (bundle (actualInactive P delta Delta n v Q scale R gain) y,
      bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) y) =
    (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
      bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) y) := by
  exact Prod.ext (bundle_of_eventuallyEq _ _ y (actualInactive_eventually_virtual P delta Delta hd hdD n k v Q scale R gain y hflat))
    (bundle_of_eventuallyEq _ _ y (actualActive_eventually_virtual P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle y hflat))

theorem virtual_paired_prefix_invariant
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n k : ℕ) (v w : Fin (n + 3) → E)
    (hprefix : ∀ i : Fin (n + 3), i.val < k + 1 → v i = w i)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E) :
    virtualInactive P delta Delta n k v Q scale R gain = virtualInactive P delta Delta n k w Q scale R gain ∧
      virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle =
        virtualActive P delta Delta n k w Q phi scale R gain A amplitude handle := by
  constructor
  · unfold virtualInactive
    rw [maskedPrefix_invariant n k v w hprefix]
  · unfold virtualActive virtualInactive
    rw [maskedPrefix_invariant n k v w hprefix]

section Physical
variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_inactive_public_no_handle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2) :
    bundle (inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta Delta (n + 2) (physicalFrame C h n tail) z) R gain) y =
      bundle (publicEndpoint (QPhysical q nu C) R gain) y :=
  actual_inactive_full_bundle_public P delta Delta hd hdD n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain y hflat

theorem actual_physical_paired_prefix_full_bundle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain A amplitude : ℝ) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| < delta / 2) :
    let v := physicalFrame C h n tail
    let Q := QPhysical q nu C
    let H0 := inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A amplitude (mkPhysical h (0 : B0) (0 : W)) z
    (bundle H0 y, bundle H1 y) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
       bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W))) y) :=
  actual_paired_full_bundle_factors_through_prefix P delta Delta hd hdD n k (physicalFrame C h n tail) (QPhysical q nu C)
    phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W)) y hflat

end Physical
end OriginalPhysicalPairedShellPrefix
end

section
-- Source component: PhysicalPairedShellClosedCore.lean

set_option maxHeartbeats 800000
open scoped Topology BigOperators

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem contDiff_gradient_of_contDiff_two (f : E → ℝ) (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  change ContDiff ℝ 1 (fun z => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z))
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hd

theorem continuous_bundle_of_contDiff_two (f : E → ℝ) (hf : ContDiff ℝ 2 f) : Continuous (bundle f) := by
  have hg := contDiff_gradient_of_contDiff_two f hf
  have hH : ContDiff ℝ 0 (fderiv ℝ (gradient f)) := hg.fderiv_right (by norm_num)
  exact hf.continuous.prodMk (hg.continuous.prodMk hH.continuous)

theorem bundle_eq_of_radial_strict_approximations (f g : E → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (y : E)
    (heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, bundle f (r • y) = bundle g (r • y)) : bundle f y = bundle g y := by
  have hc : Continuous (fun r : ℝ => r • y) := continuous_id.smul continuous_const
  have hclosed : IsClosed {r : ℝ | bundle f (r • y) = bundle g (r • y)} :=
    isClosed_eq ((continuous_bundle_of_contDiff_two f hf).comp hc) ((continuous_bundle_of_contDiff_two g hg).comp hc)
  have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {r : ℝ | bundle f (r • y) = bundle g (r • y)} := fun r hr => heq r hr
  have hmem : (1 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨by norm_num, le_rfl⟩
  simpa only [Set.mem_setOf_eq, one_smul] using (hclosed.closure_subset_iff.mpr hsub) hmem

theorem flat_closed_scales_to_strict (delta : ℝ) (hd : 0 < delta) (d y : E)
    (hflat : |inner ℝ d y| ≤ delta / 2) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    |inner ℝ d (r • y)| < delta / 2 := by
  rw [inner_smul_right, abs_mul, abs_of_pos hr.1]
  have hh := mul_le_mul_of_nonneg_left hflat hr.1.le
  have hc : r * (delta / 2) < delta / 2 := by nlinarith only [hd, hr.2]
  exact hh.trans_lt hc

theorem inactiveShell_contDiff_two (Q g : E → ℝ) (R gain : ℝ) (hR : 0 < R)
    (hQ : ContDiff ℝ 2 Q) (hg : ContDiff ℝ 2 g) : ContDiff ℝ 2 (inactiveShell Q g R gain) := by
  have ht : ContDiff ℝ 3 (FangqingRadialGateBounds.scaledGate theta R 0 : E → ℝ) :=
    FangqingGateBudgetBridge.scaledGate_contDiff theta R 0 hR (theta_smooth.of_le (by decide))
  have hc : ContDiff ℝ 2 (FangqingRadialCollar.collar psi R : E → ℝ) :=
    (FangqingRadialCollar.collar_contDiff_three psi (psi_smooth.of_le (by decide)) R).of_le (by norm_num)
  exact (hQ.add ((ht.of_le (by norm_num)).mul hg)).add (contDiff_const.mul hc)

theorem actualInactive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (scale R gain : ℝ) (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) :
    ContDiff ℝ 2 (actualInactive P delta Delta n v Q scale R gain) :=
  inactiveShell_contDiff_two Q _ R gain hR hQ (contDiff_const.mul (pathEdge_contDiff P delta Delta hd hdD (n + 2) v))

theorem virtualInactive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n k : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (scale R gain : ℝ) (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) :
    ContDiff ℝ 2 (virtualInactive P delta Delta n k v Q scale R gain) := by
  classical
  apply inactiveShell_contDiff_two Q _ R gain hR hQ
  apply ContDiff.mul contDiff_const
  unfold selectedEdgeSum
  apply ContDiff.sum
  intro i hi
  exact (FlatCubic.edge_contDiff_two P delta Delta hd hdD).comp (innerSL ℝ (pathDirection n (maskedPrefix n k v) i)).contDiff

theorem actualActive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 2 (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) := by
  exact (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ).sub
    ((localizedSeed_contDiff theta phi R A amplitude handle hR (theta_smooth.of_le (by decide)) hphi).of_le (by norm_num))

theorem virtualActive_contDiff_two (P : FlatCubic.Profile) (delta Delta : ℝ)
    (hd : 0 < delta) (hdD : delta ≤ Delta) (n k : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (handle : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi) :
    ContDiff ℝ 2 (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) := by
  exact (virtualInactive_contDiff_two P delta Delta hd hdD n k v Q scale R gain hR hQ).sub
    ((localizedSeed_contDiff theta phi R A amplitude handle hR (theta_smooth.of_le (by decide)) hphi).of_le (by norm_num))

theorem actual_inactive_full_bundle_public_closed
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n v i) y| ≤ delta / 2) :
    bundle (actualInactive P delta Delta n v Q scale R gain) y = bundle (publicEndpoint Q R gain) y := by
  have hpub : ContDiff ℝ 2 (publicEndpoint Q R gain) := hQ.add
    (contDiff_const.mul ((FangqingRadialCollar.collar_contDiff_three psi (psi_smooth.of_le (by decide)) R).of_le (by norm_num)))
  apply bundle_eq_of_radial_strict_approximations _ _ (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ) hpub y
  intro r hr
  exact actual_inactive_full_bundle_public P delta Delta hd hdD n v Q scale R gain (r • y)
    (fun i => flat_closed_scales_to_strict delta hd _ y (hflat i) r hr)

theorem actual_paired_full_bundle_factors_through_prefix_closed
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hR : 0 < R) (hQ : ContDiff ℝ 2 Q) (hphi : ContDiff ℝ 3 phi)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| ≤ delta / 2) :
    (bundle (actualInactive P delta Delta n v Q scale R gain) y,
      bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) y) =
    (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
      bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) y) := by
  have heq : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (bundle (actualInactive P delta Delta n v Q scale R gain) (r • y), bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) (r • y)) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) (r • y), bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude handle) (r • y)) := by
    intro r hr
    exact actual_paired_full_bundle_factors_through_prefix P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle (r • y)
      (fun i hi => flat_closed_scales_to_strict delta hd _ y (hflat i hi) r hr)
  apply Prod.ext
  · apply bundle_eq_of_radial_strict_approximations _ _
      (actualInactive_contDiff_two P delta Delta hd hdD n v Q scale R gain hR hQ)
      (virtualInactive_contDiff_two P delta Delta hd hdD n k v Q scale R gain hR hQ) y
    exact fun r hr => congrArg Prod.fst (heq r hr)
  · apply bundle_eq_of_radial_strict_approximations _ _
      (actualActive_contDiff_two P delta Delta hd hdD n v Q phi scale R gain A amplitude handle hR hQ hphi)
      (virtualActive_contDiff_two P delta Delta hd hdD n k v Q phi scale R gain A amplitude handle hR hQ hphi) y
    exact fun r hr => congrArg Prod.snd (heq r hr)

end OriginalPhysicalPairedShellPrefix

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_inactive_public_closed_no_handle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (hR : 0 < R) (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) :
    bundle (inactiveShell (QPhysical q nu C)
      (fun z => scale * pathEdge P delta Delta (n + 2) (physicalFrame C h n tail) z) R gain) y =
      bundle (publicEndpoint (QPhysical q nu C) R gain) y :=
  actual_inactive_full_bundle_public_closed P delta Delta hd hdD n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain y
    hR (FangqingAmplifierRegularity.physical_quadratic_contDiff q nu C) hflat

theorem actual_physical_paired_closed_prefix_full_bundle
    (P : FlatCubic.Profile) (delta Delta : ℝ) (hd : 0 < delta) (hdD : delta ≤ Delta)
    (n k : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi) (q nu scale R gain A amplitude : ℝ) (hR : 0 < R)
    (y : PhysicalSpace A0 B0 W)
    (hflat : ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) :
    let v := physicalFrame C h n tail
    let Q := QPhysical q nu C
    let H0 := inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A amplitude (mkPhysical h (0 : B0) (0 : W)) z
    (bundle H0 y, bundle H1 y) =
      (bundle (virtualInactive P delta Delta n k v Q scale R gain) y,
       bundle (virtualActive P delta Delta n k v Q phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W))) y) :=
  actual_paired_full_bundle_factors_through_prefix_closed P delta Delta hd hdD n k (physicalFrame C h n tail) (QPhysical q nu C)
    phi scale R gain A amplitude (mkPhysical h (0 : B0) (0 : W)) y hR
    (FangqingAmplifierRegularity.physical_quadratic_contDiff q nu C) hphi hflat

end OriginalPhysicalPairedShellPrefix
end

section
-- Source component: PairedShellComplete.lean

open scoped ContDiff NNReal

/- A shared actual endpoint pair, all analytic/minimizer claims, and literal
closed-flat value-gradient-Hessian prefix factorization. The post-activation
factorization is explicitly conditional on the later edges being flat. This
source does not assert that arbitrary off-event fixed-frame responses reveal
one direction, nor that a Haar/resisting event has already been generated.
Fresh original-claim correspondence must decide the scope of item (iv). -/


namespace OriginalPairedShellComplete

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingActiveShellLargerWidth
  FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingPhysicalPairedShellMinimizers FangqingRawEndpointDifferenceJets
  FangqingWidePairedShellRateBudgets FangqingPairedShellAnalyticItems
  FangqingShellPrefixLocality OriginalPhysicalPairedShellPrefix FangqingPacketLeakage

noncomputable section

set_option maxHeartbeats 4000000

universe u

theorem actual_shared_paired_shell_with_closed_prefix_locality
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧ ∃ Kd : ℝ, 0 ≤ Kd ∧
    ∀ (A0 B0 W : Type u)
      [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
      [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
    ∀ (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (n : ℕ) (tail : Fin (n + 2) → W)
      (delta omega q scale lam : ℝ),
      ‖h‖ = 1 → Orthonormal ℝ tail → 0 < delta → delta ≤ omega → 1 ≤ q →
      0 < scale → 0 < lam → omega = Cw * lam * q ^ 2 → ((n + 2 : ℕ) : ℝ) ≤ Cm * q →
      let nu := scale * lam
      let D := distanceScale q omega
      let Cs := 2 * Cw
      let Cmin := 2 * Cw * (Cm + 2)
      let A := (1 + 2 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (16 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h 0 0) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (16 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (16 * K + 1) * Kc) + Ks * Cs
      (AnalyticClass F0 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      AnalyticClass F1 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      ContDiff ℝ 3 (fun z => F1 z - F0 z) ∧
      (∀ j, j ≤ 3 → ∀ z, ‖iteratedFDeriv ℝ j (fun z => F1 z - F0 z) z‖ ≤ Kd * (s * A) / D ^ j) ∧
      (∀ z, |F1 z - F0 z| ≤ Kd * (s * A)) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z)) ∧
      (∀ Z : PhysicalSpace A0 B0 W, (∀ Y, F1 Z ≤ F1 Y) →
        ∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
          rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
      (∀ y : PhysicalSpace A0 B0 W,
        (∀ i : Fin (n + 2), |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) →
        bundle F0 y = bundle (publicEndpoint Q R gain) y) ∧
      (∀ (k : ℕ) (y : PhysicalSpace A0 B0 W),
        (∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n (physicalFrame C h n tail) i) y| ≤ delta / 2) →
        (bundle F0 y, bundle F1 y) =
          (bundle (virtualInactive P delta omega n k (physicalFrame C h n tail) Q scale R gain) y,
           bundle (virtualActive P delta omega n k (physicalFrame C h n tail) Q phi scale R gain A (s * A) (mkPhysical h 0 0)) y)) ∧
      (∀ (k : ℕ) (w : Fin (n + 3) → PhysicalSpace A0 B0 W),
        (∀ i : Fin (n + 3), i.val < k + 1 → physicalFrame C h n tail i = w i) →
        virtualInactive P delta omega n k (physicalFrame C h n tail) Q scale R gain =
          virtualInactive P delta omega n k w Q scale R gain ∧
        virtualActive P delta omega n k (physicalFrame C h n tail) Q phi scale R gain A (s * A) (mkPhysical h 0 0) =
          virtualActive P delta omega n k w Q phi scale R gain A (s * A) (mkPhysical h 0 0)) := by
  obtain ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, hAnalytic⟩ :=
    actual_paired_shell_analytic_items.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  refine ⟨Ce, K, hK, Kc, hKc, Ks, hKs, Kd, hKd, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
    nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0 CL Crho
  have hA := hAnalytic A0 B0 W C h n tail delta omega q scale lam
    hh ht hd hdw hq hscale hlam homega hn
  have hCw0 : 0 < Cw := by linarith only [hCm, hCw]
  have hw : 0 < omega := hd.trans_le hdw
  have hq0 : 0 < q := by linarith only [hq]
  have hR : 0 < R := by
    dsimp [R, A, D, Cs, Cmin, distanceScale]
    positivity
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCmin : 0 ≤ Cmin := by dsimp [Cmin]; positivity
  obtain ⟨hDA, hWidth, hMinA⟩ :=
    FangqingActiveShellLargerWidth.larger_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hAp : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hAp]
  refine ⟨hA, ?_, ?_, ?_, ?_⟩
  · obtain ⟨Zraw, hm, hu, hnorm, hgap, hbulk⟩ := actual_physical_minimizer_norm_gap_bulk P C h hh n tail ht
      delta omega q Cm Cw scale lam hd hdw hq hCm hCw hscale hlam homega hn
    have hzA : ‖Zraw‖ < A := hnorm.trans_lt hMinA
    have hzR : ‖Zraw‖ < R := hzA.trans_le hAR
    have hhandle : ‖mkPhysical h (0 : B0) (0 : W)‖ ≤ 1 := by
      have hn1 := WithLp.prod_norm_sq_eq_of_L2 (mkPhysical h (0 : B0) (0 : W))
      have hn2 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (h, (0 : B0)))
      change ‖mkPhysical h (0 : B0) (0 : W)‖ ^ 2 = ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 + ‖(0 : W)‖ ^ 2 at hn1
      change ‖WithLp.toLp 2 (h, (0 : B0))‖ ^ 2 = ‖h‖ ^ 2 + ‖(0 : B0)‖ ^ 2 at hn2
      rw [hh, norm_zero] at hn2
      rw [norm_zero] at hn1
      nlinarith only [hn1, hn2, norm_nonneg (mkPhysical h (0 : B0) (0 : W))]
    have hseed := actual_seed_ratio q omega Cw lam scale hq0 homega
    have hi : ∀ Y : PhysicalSpace A0 B0 W, inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y = inner ℝ h Y.fst.fst := by
      intro Y
      change (inner ℝ h Y.fst.fst + inner ℝ (0 : B0) Y.fst.snd) + inner ℝ (0 : W) Y.snd = _
      simp only [inner_zero_left, add_zero]
    have hRaw : ∀ Y : PhysicalSpace A0 B0 W,
        rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale (scale * (2 * omega ^ 2 / Real.sqrt q)) Y =
          Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
      intro Y
      rw [rawPacket_literal, hseed, hi]
      rfl
    have hrawmin : ∀ Y, Q Zraw + g Zraw - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Zraw ≤
        Q Y + g Y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) Y := by
      intro Y
      rw [← hRaw Zraw, ← hRaw Y]
      exact hm Y
    obtain ⟨hm1, hu1⟩ := FangqingShellMinimizerTransfer.actual_active_minimizer_preserved
      Q g phi R A s gain (nu / 2) hR hAp (half_pos hnu) (mkPhysical h 0 0) Zraw
      hhandle hcore hzR hzA hrawmin hA.2.1.1 hA.2.1.2.1
    intro Z hZ Y
    have hsame : Z = Zraw := hu1 Z hZ
    rw [hsame]
    exact hm Y
  · intro y hy
    exact actual_physical_inactive_public_closed_no_handle P delta omega hd hdw n C h tail
      q nu scale R gain hR y hy
  · intro k y hy
    exact actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail
      phi hp q nu scale R gain A (s * A) hR y hy
  · intro k w hw
    exact virtual_paired_prefix_invariant P delta omega n k (physicalFrame C h n tail) w hw
      Q phi scale R gain A (s * A) (mkPhysical h 0 0)

end
end OriginalPairedShellComplete
end

section
-- Source component: RelayStationarity.lean

open scoped BigOperators Topology

namespace FangqingRelayStationarity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

abbrev Blocks (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin (n + 1) => E)

def incoming (n : ℕ) (gate : Fin n → E → ℝ)
    (s : Fin (n + 1) → E) : Fin (n + 1) → ℝ :=
  Fin.cases 1 (fun i => gate i (s i.castSucc))

def endpoint (β lam : ℝ) (h : E → ℝ) (m : ℝ) (x y : E) : ℝ :=
  β / 2 * ‖x‖ ^ 2 + lam * inner ℝ x y - h y + m

def delta (h0 h1 : E → ℝ) (m0 m1 : ℝ) (y : E) : ℝ :=
  h0 y - h1 y + m1 - m0

/- Exactly the paper's finite relay, regrouped into one local packet sum,
   the relay quadratic, and the progress reward.  Fin (n+1) represents T
   packets and Fin n represents the T-1 gates. -/
def family (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E) : ℝ :=
  (∑ t, (endpoint β lam (h0 t) (m0 t) (x t) (y t) +
    incoming n gate s t * delta (h0 t) (h1 t) (m0 t) (m1 t) (y t))) -
  sigma / 2 * (∑ t, ‖s t - a • x t‖ ^ 2) -
  reward * (∑ i, gate i (s i.castSucc))

def vary {ι : Type*} [DecidableEq ι] (x : ι → E) (i : ι) (v : E) (t : ℝ) : ι → E :=
  Function.update x i (x i + t • v)

theorem vary_zero {ι : Type*} [DecidableEq ι]
    (x : ι → E) (i : ι) (v : E) : vary x i v 0 = x := by
  simp [vary]

theorem vary_same {ι : Type*} [DecidableEq ι]
    (x : ι → E) (i : ι) (v : E) (t : ℝ) : vary x i v t i = x i + t • v := by
  simp [vary]

theorem vary_other {ι : Type*} [DecidableEq ι]
    (x : ι → E) (i j : ι) (v : E) (t : ℝ) (hji : j ≠ i) :
    vary x i v t j = x j := by simp [vary, hji]

theorem sum_update {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → E → ℝ) (x : ι → E) (i : ι) (z : E) :
    (∑ j, g j (Function.update x i z j)) =
      (∑ j, g j (x j)) + g i z - g i (x i) := by
  have heq : (∑ j, (g j (Function.update x i z j) - g j (x j))) =
      g i z - g i (x i) := by
    calc
      _ = g i (Function.update x i z i) - g i (x i) := by
        apply Finset.sum_eq_single i
        · intro j hj hji
          simp [Function.update_of_ne hji]
        · simp
      _ = _ := by simp
  rw [Finset.sum_sub_distrib] at heq
  linarith only [heq]

theorem toLp_vary (n : ℕ) (x : Fin (n + 1) → E) (i : Fin (n + 1))
    (v : E) (t : ℝ) :
    WithLp.toLp 2 (vary x i v t) =
      (WithLp.toLp 2 x : Blocks n E) + t • PiLp.single 2 i v := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [vary, PiLp.single_apply]
  · simp [vary, Function.update_of_ne hji, PiLp.single_apply, hji]

theorem hasDerivAt_toLp_vary (n : ℕ) (x : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) :
    HasDerivAt (fun t : ℝ => (WithLp.toLp 2 (vary x i v t) : Blocks n E))
      (PiLp.single 2 i v) 0 := by
  simp_rw [toLp_vary]
  simpa only [id_eq, one_smul] using
    (((hasDerivAt_id (0 : ℝ)).smul_const (PiLp.single 2 i v)).const_add
      (WithLp.toLp 2 x : Blocks n E))

theorem inner_single (n : ℕ) (G : Blocks n E) (i : Fin (n + 1)) (v : E) :
    inner ℝ G (PiLp.single 2 i v) = inner ℝ (G i) v := by
  classical
  simp [PiLp.inner_apply, PiLp.single_apply, apply_ite]

theorem family_x_vary (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) (t : ℝ) :
    family n β lam a sigma reward h0 h1 m0 m1 gate (vary x i v t) y s =
      family n β lam a sigma reward h0 h1 m0 m1 gate x y s +
      (endpoint β lam (h0 i) (m0 i) (x i + t • v) (y i) -
        endpoint β lam (h0 i) (m0 i) (x i) (y i)) -
      sigma / 2 * (‖s i - a • (x i + t • v)‖ ^ 2 - ‖s i - a • x i‖ ^ 2) := by
  unfold family vary
  have hpacket := sum_update
    (fun j z => endpoint β lam (h0 j) (m0 j) z (y j) +
      incoming n gate s j * delta (h0 j) (h1 j) (m0 j) (m1 j) (y j)) x i (x i + t • v)
  have hquad := sum_update (fun j z => ‖s j - a • z‖ ^ 2) x i (x i + t • v)
  rw [hpacket, hquad]
  ring

theorem family_x_deriv (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) :
    HasDerivAt (fun t : ℝ =>
      family n β lam a sigma reward h0 h1 m0 m1 gate (vary x i v t) y s)
      (inner ℝ (β • x i + lam • y i + (sigma * a) • (s i - a • x i)) v) 0 := by
  have hc : HasDerivAt (fun t : ℝ => x i + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (x i))
  have hn := hc.norm_sq
  have hi := HasDerivAt.inner ℝ hc (hasDerivAt_const (0 : ℝ) (y i))
  have hq := ((hasDerivAt_const (0 : ℝ) (s i)).sub (hc.const_smul a)).norm_sq
  have he := (((hn.const_mul (β / 2)).add (hi.const_mul lam)).sub_const
    (h0 i (y i))).add_const (m0 i)
  have hh := ((he.sub_const (endpoint β lam (h0 i) (m0 i) (x i) (y i))).const_add
      (family n β lam a sigma reward h0 h1 m0 m1 gate x y s)).sub
    ((hq.sub_const (‖s i - a • x i‖ ^ 2)).const_mul (sigma / 2))
  simp_rw [family_x_vary]
  convert! hh using 1 <;>
    simp only [Pi.sub_apply, Pi.smul_apply, zero_smul, add_zero, zero_sub, inner_neg_right,
      real_inner_smul_left, real_inner_smul_right, inner_add_left,
      inner_zero_left, add_zero, inner_zero_right, sub_zero, real_inner_comm v (y i)] <;> ring

theorem actual_outer_coordinate (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (Phi : Blocks n E → ℝ) (G : Blocks n E)
    (hgrad : HasGradientAt Phi G (WithLp.toLp 2 x))
    (hvalue : Phi (WithLp.toLp 2 x) = family n β lam a sigma reward h0 h1 m0 m1 gate x y s)
    (hmax : ∀ z : Fin (n + 1) → E,
      family n β lam a sigma reward h0 h1 m0 m1 gate z y s ≤ Phi (WithLp.toLp 2 z))
    (i : Fin (n + 1)) :
    G i = β • x i + lam • y i + (sigma * a) • (s i - a • x i) := by
  apply ext_inner_right ℝ
  intro v
  have hp : HasDerivAt (fun t : ℝ => Phi (WithLp.toLp 2 (vary x i v t)))
      (inner ℝ (G i) v) 0 := by
    have hh : HasFDerivAt Phi ((InnerProductSpace.toDual ℝ (Blocks n E)) G)
        (WithLp.toLp 2 (vary x i v 0)) := by simpa only [vary_zero] using hgrad.hasFDerivAt
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply, inner_single] using
      (hh.comp_hasDerivAt 0 (hasDerivAt_toLp_vary n x i v))
  have hf := family_x_deriv n β lam a sigma reward h0 h1 m0 m1 gate x y s i v
  have hmin : IsLocalMin (fun t : ℝ =>
      Phi (WithLp.toLp 2 (vary x i v t)) -
      family n β lam a sigma reward h0 h1 m0 m1 gate (vary x i v t) y s) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simp only [vary_zero]
    rw [hvalue]
    linarith only [hmax (vary x i v t)]
  have hz := hmin.hasDerivAt_eq_zero (hp.sub hf)
  linarith only [hz]


theorem family_y_vary (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) (t : ℝ) :
    family n β lam a sigma reward h0 h1 m0 m1 gate x (vary y i v t) s =
      family n β lam a sigma reward h0 h1 m0 m1 gate x y s +
      (endpoint β lam (h0 i) (m0 i) (x i) (y i + t • v) -
        endpoint β lam (h0 i) (m0 i) (x i) (y i)) +
      incoming n gate s i *
        (delta (h0 i) (h1 i) (m0 i) (m1 i) (y i + t • v) -
         delta (h0 i) (h1 i) (m0 i) (m1 i) (y i)) := by
  unfold family vary
  have hpacket := sum_update
    (fun j z => endpoint β lam (h0 j) (m0 j) (x j) z +
      incoming n gate s j * delta (h0 j) (h1 j) (m0 j) (m1 j) z) y i (y i + t • v)
  rw [hpacket]
  ring

theorem actual_active_inner_coordinate (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (hdiff : ∀ j, Differentiable ℝ (h1 j))
    (hmax : ∀ z : Fin (n + 1) → E,
      family n β lam a sigma reward h0 h1 m0 m1 gate x z s ≤
      family n β lam a sigma reward h0 h1 m0 m1 gate x y s)
    (i : Fin (n + 1)) (hactive : incoming n gate s i = 1) :
    gradient (h1 i) (y i) = lam • x i := by
  apply ext_inner_right ℝ
  intro v
  have hc : HasDerivAt (fun t : ℝ => y i + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (y i))
  have hh : HasFDerivAt (h1 i) (fderiv ℝ (h1 i) (y i)) (y i + (0 : ℝ) • v) := by
    simpa using (hdiff i (y i)).hasFDerivAt
  have hH : HasDerivAt (fun t : ℝ => h1 i (y i + t • v))
      (inner ℝ (gradient (h1 i) (y i)) v) 0 := by
    simpa only [Function.comp_def, inner_gradient_left] using hh.comp_hasDerivAt 0 hc
  have hi := HasDerivAt.inner ℝ (hasDerivAt_const (0 : ℝ) (x i)) hc
  have hd := (hi.const_mul lam).sub hH
  have hloc : IsLocalMax (fun t : ℝ => lam * inner ℝ (x i) (y i + t • v) -
      h1 i (y i + t • v)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hmax (vary y i v t)
    rw [family_y_vary, hactive] at h
    simp only [zero_smul, add_zero]
    dsimp only [endpoint, delta] at h
    linarith only [h]
  have hz := hloc.hasDerivAt_eq_zero hd
  simp only [zero_smul, add_zero, inner_zero_left, zero_add] at hz
  rw [real_inner_smul_left]
  linarith only [hz]

def gateExt (n : ℕ) (gate : Fin n → E → ℝ) : Fin (n + 1) → E → ℝ :=
  Fin.lastCases (fun _ => 0) gate

def coefficient (n : ℕ) (reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (y : Fin (n + 1) → E) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun i => delta (h0 i.succ) (h1 i.succ)
    (m0 i.succ) (m1 i.succ) (y i.succ) - reward)

theorem family_gate_sum (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E) :
    family n β lam a sigma reward h0 h1 m0 m1 gate x y s =
      (∑ t, endpoint β lam (h0 t) (m0 t) (x t) (y t)) +
      delta (h0 0) (h1 0) (m0 0) (m1 0) (y 0) +
      (∑ t, gateExt n gate t (s t) * coefficient n reward h0 h1 m0 m1 y t) -
      sigma / 2 * (∑ t, ‖s t - a • x t‖ ^ 2) := by
  have hin : (∑ t, incoming n gate s t *
      delta (h0 t) (h1 t) (m0 t) (m1 t) (y t)) =
      delta (h0 0) (h1 0) (m0 0) (m1 0) (y 0) +
      ∑ i, gate i (s i.castSucc) *
        delta (h0 i.succ) (h1 i.succ) (m0 i.succ) (m1 i.succ) (y i.succ) := by
    rw [Fin.sum_univ_succ]
    simp [incoming]
  have hout : (∑ t, gateExt n gate t (s t) * coefficient n reward h0 h1 m0 m1 y t) =
      (∑ i, gate i (s i.castSucc) *
        delta (h0 i.succ) (h1 i.succ) (m0 i.succ) (m1 i.succ) (y i.succ)) -
      reward * (∑ i, gate i (s i.castSucc)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [gateExt, coefficient, Fin.lastCases_castSucc, Fin.lastCases_last,
      zero_mul, add_zero, mul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul]
    ring
  unfold family
  rw [Finset.sum_add_distrib, hin, hout]
  ring

theorem family_s_vary (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (v : E) (t : ℝ) :
    family n β lam a sigma reward h0 h1 m0 m1 gate x y (vary s i v t) =
      family n β lam a sigma reward h0 h1 m0 m1 gate x y s +
      coefficient n reward h0 h1 m0 m1 y i *
        (gateExt n gate i (s i + t • v) - gateExt n gate i (s i)) -
      sigma / 2 * (‖s i + t • v - a • x i‖ ^ 2 - ‖s i - a • x i‖ ^ 2) := by
  rw [family_gate_sum, family_gate_sum]
  unfold vary
  rw [sum_update (fun j z => gateExt n gate j z * coefficient n reward h0 h1 m0 m1 y j)
    s i (s i + t • v), sum_update (fun j z => ‖z - a • x j‖ ^ 2) s i (s i + t • v)]
  ring

theorem actual_relay_inner_coordinate (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (p : E) (hp : HasGradientAt (gateExt n gate i) p (s i))
    (hmax : ∀ z : Fin (n + 1) → E,
      family n β lam a sigma reward h0 h1 m0 m1 gate x y z ≤
      family n β lam a sigma reward h0 h1 m0 m1 gate x y s) :
    sigma • (s i - a • x i) = coefficient n reward h0 h1 m0 m1 y i • p := by
  apply ext_inner_right ℝ
  intro v
  have hc : HasDerivAt (fun t : ℝ => s i + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (s i))
  have hpg : HasFDerivAt (gateExt n gate i) ((InnerProductSpace.toDual ℝ E) p)
      (s i + (0 : ℝ) • v) := by simpa using hp.hasFDerivAt
  have hg : HasDerivAt (fun t : ℝ => gateExt n gate i (s i + t • v))
      (inner ℝ p v) 0 := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      hpg.comp_hasDerivAt 0 hc
  have hn := (hc.sub_const (a • x i)).norm_sq
  have hd := ((hg.sub_const (gateExt n gate i (s i))).const_mul
    (coefficient n reward h0 h1 m0 m1 y i)).sub
      ((hn.sub_const (‖s i - a • x i‖ ^ 2)).const_mul (sigma / 2))
  have hloc : IsLocalMax (fun t : ℝ =>
      coefficient n reward h0 h1 m0 m1 y i *
        (gateExt n gate i (s i + t • v) - gateExt n gate i (s i)) -
      sigma / 2 * (‖s i + t • v - a • x i‖ ^ 2 - ‖s i - a • x i‖ ^ 2)) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    have h := hmax (vary s i v t)
    rw [family_s_vary] at h
    simp only [zero_smul, add_zero, sub_self, mul_zero, sub_zero]
    linarith only [h]
  have hz := hloc.hasDerivAt_eq_zero hd
  simp only [zero_smul, add_zero, sub_zero] at hz
  rw [real_inner_smul_left, real_inner_smul_left]
  nlinarith only [hz]


/- A genuine radial profile, evaluated at the actual squared distance. -/
def radialGate (theta : ℝ → ℝ) (a ell : ℝ) (star z : E) : ℝ :=
  theta (‖z - a • star‖ ^ 2 / (a ^ 2 * ell ^ 2))

def eta (theta : ℝ → ℝ) (a ell : ℝ) (star z : E) : ℝ :=
  -(2 * deriv theta (‖z - a • star‖ ^ 2 / (a ^ 2 * ell ^ 2))) /
    (a ^ 2 * ell ^ 2)

theorem radialGate_hasGradientAt (theta : ℝ → ℝ) (a ell : ℝ) (star z : E)
    (htheta : Differentiable ℝ theta) :
    HasGradientAt (radialGate theta a ell star)
      (-eta theta a ell star z • (z - a • star)) z := by
  have hnorm := ((hasFDerivAt_id z).sub_const (a • star)).norm_sq
  have harg := hnorm.const_smul ((a ^ 2 * ell ^ 2)⁻¹)
  have hh := (htheta _).hasDerivAt.comp_hasFDerivAt z harg
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hh using 1
  · funext w
    simp [radialGate, div_eq_mul_inv, mul_comm]
  · ext v
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, innerSL_apply_apply,
      Pi.sub_apply, Pi.div_apply, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, eta, id_eq]
    simp only [mul_comm ((a ^ 2 * ell ^ 2)⁻¹) _]
    ring

theorem eta_nonneg_le (theta : ℝ → ℝ) (a ell C : ℝ) (star z : E)
    (ha : 0 < a) (hell : 0 < ell) (hC : 0 ≤ C)
    (hanti : Antitone theta) (hderiv : ∀ u, |deriv theta u| ≤ C) :
    0 ≤ eta theta a ell star z ∧
      eta theta a ell star z ≤ 2 * C / (a ^ 2 * ell ^ 2) := by
  have hden : 0 < a ^ 2 * ell ^ 2 := by positivity
  have hn := hanti.deriv_nonpos (x := ‖z - a • star‖ ^ 2 / (a ^ 2 * ell ^ 2))
  have hb := (abs_le.mp (hderiv (‖z - a • star‖ ^ 2 / (a ^ 2 * ell ^ 2)))).1
  unfold eta
  constructor
  · exact div_nonneg (by linarith only [hn]) hden.le
  · apply (div_le_div_iff_of_pos_right hden).mpr
    linarith only [hb]

theorem radialGate_unit (theta : ℝ → ℝ) (a ell radius : ℝ) (star z : E)
    (ha : 0 < a) (hell : 0 < ell) (hr : 0 ≤ radius)
    (hunit : ∀ u, 0 ≤ u → u ≤ radius ^ 2 → theta u = 1)
    (hnear : ‖z - a • star‖ ≤ a * ell * radius) :
    radialGate theta a ell star z = 1 := by
  apply hunit _ (div_nonneg (sq_nonneg _) (by positivity))
  apply (div_le_iff₀ (by positivity : 0 < a ^ 2 * ell ^ 2)).mpr
  have hs := sq_le_sq₀ (norm_nonneg (z - a • star))
    (by positivity : 0 ≤ a * ell * radius) |>.mpr hnear
  nlinarith only [hs]

/- This geometric force is derived from the true relay first-order
   equation.  It never assumes that a gate is open or that x is close. -/
theorem radial_relay_force (β a sigma eps B eta0 : ℝ)
    (d r residual locgrad outer : E)
    (hβ : 0 < β) (ha : 0 < a) (hsigma : 0 < sigma)
    (hB : B ≤ 0) (heta : 0 ≤ eta0)
    (hsmall : (-B) * eta0 ≤ sigma / 2)
    (hrel : a • d = r - residual)
    (hfoc : sigma • residual = B • (-eta0 • r))
    (hsupport : β * ‖d‖ ^ 2 ≤ inner ℝ locgrad d)
    (houter : outer = locgrad + (sigma * a) • residual)
    (hstationary : ‖outer‖ ≤ eps) :
    β * ‖d‖ ≤ eps ∧ ‖r‖ ≤ 2 * a * eps / β := by
  let shrink : ℝ := (-B) * eta0 / sigma
  have hsh0 : 0 ≤ shrink :=
    div_nonneg (mul_nonneg (neg_nonneg.mpr hB) heta) hsigma.le
  have hsh : shrink ≤ 1 / 2 := by
    dsimp [shrink]
    apply (div_le_iff₀ hsigma).mpr
    linarith only [hsmall]
  have hres : residual = shrink • r := by
    have hh := congrArg (fun z : E => sigma⁻¹ • z) hfoc
    simp only [smul_smul, inv_mul_cancel₀ hsigma.ne', one_smul] at hh
    calc
      residual = (sigma⁻¹ * (B * -eta0)) • r := hh
      _ = shrink • r := by congr 1; dsimp [shrink]; ring
  have hcol : a • d = (1 - shrink) • r := by
    rw [hrel, hres, sub_smul, one_smul]
  have hdot : 0 ≤ inner ℝ residual d := by
    have hh := congrArg (fun z : E => inner ℝ residual z) hcol
    simp only [real_inner_smul_right] at hh
    have hr : inner ℝ residual r = shrink * ‖r‖ ^ 2 := by
      rw [hres, real_inner_smul_left, real_inner_self_eq_norm_sq]
    rw [hr] at hh
    have hn : 0 ≤ (1 - shrink) * (shrink * ‖r‖ ^ 2) :=
      mul_nonneg (by linarith only [hsh]) (mul_nonneg hsh0 (sq_nonneg _))
    nlinarith only [hh, hn, ha]
  have hproj : β * ‖d‖ ^ 2 ≤ inner ℝ outer d := by
    rw [houter, inner_add_left, real_inner_smul_left]
    have hc : 0 ≤ sigma * a * inner ℝ residual d := by positivity
    linarith only [hsupport, hc]
  have hcs := real_inner_le_norm outer d
  have hm := mul_le_mul_of_nonneg_right hstationary (norm_nonneg d)
  have hforce : β * ‖d‖ ≤ eps := by
    by_cases hd : ‖d‖ = 0
    · rw [hd, mul_zero]
      exact (norm_nonneg outer).trans hstationary
    · have hdpos : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg d) (Ne.symm hd)
      nlinarith only [hproj, hcs, hm, hdpos]
  refine ⟨hforce, ?_⟩
  have hn := congrArg norm hcol
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ha, abs_of_nonneg (by linarith only [hsh] : 0 ≤ 1 - shrink)] at hn
  apply (le_div_iff₀ hβ).mpr
  have hr : ‖r‖ ≤ 2 * a * ‖d‖ := by
    have hh := mul_nonneg (by linarith only [hsh] : 0 ≤ 1 / 2 - shrink) (norm_nonneg r)
    nlinarith only [hn, hh]
  have hp := mul_le_mul_of_nonneg_left hforce (by positivity : 0 ≤ 2 * a)
  have hm := mul_le_mul_of_nonneg_right hr hβ.le
  nlinarith only [hp, hm]


theorem active_packet_support (h : E → ℝ) (β lam mu : ℝ)
    (x y star ystar : E) (hmu : 0 ≤ mu)
    (hsc : StrongConvexOn (Set.univ : Set E) mu h)
    (hdiff : Differentiable ℝ h)
    (hy : gradient h y = lam • x)
    (hyref : gradient h ystar = lam • star)
    (hxref : β • star + lam • ystar = 0) :
    β * ‖x - star‖ ^ 2 ≤ inner ℝ (β • x + lam • y) (x - star) := by
  have hm := PacketCore.gradient_strong_monotone h mu hsc hdiff y ystar
  rw [hy, hyref, ← smul_sub, real_inner_smul_left] at hm
  have hn : 0 ≤ lam * inner ℝ (y - ystar) (x - star) := by
    rw [real_inner_comm]
    exact (by positivity : 0 ≤ mu * ‖y - ystar‖ ^ 2) |>.trans hm
  have href : β • star = -(lam • ystar) := eq_neg_of_add_eq_zero_left hxref
  have heq : β • x + lam • y = β • (x - star) + lam • (y - ystar) := by
    rw [smul_sub, smul_sub, href]
    abel
  rw [heq, inner_add_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  linarith only [hn]

def etaExt (n : ℕ) (theta : ℝ → ℝ) (a ell : ℝ)
    (star s : Fin (n + 1) → E) : Fin (n + 1) → ℝ :=
  Fin.lastCases 0 (fun i => eta theta a ell (star i.castSucc) (s i.castSucc))

theorem radial_gateExt_hasGradientAt (n : ℕ) (theta : ℝ → ℝ) (a ell : ℝ)
    (star s : Fin (n + 1) → E) (htheta : Differentiable ℝ theta) (i : Fin (n + 1)) :
    HasGradientAt
      (gateExt n (fun j => radialGate theta a ell (star j.castSucc)) i)
      (-etaExt n theta a ell star s i • (s i - a • star i)) (s i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [gateExt, etaExt] using (hasGradientAt_const (s (Fin.last n)) (0 : ℝ))
  · simpa [gateExt, etaExt] using
      radialGate_hasGradientAt theta a ell (star j.castSucc) (s j.castSucc) htheta

theorem coefficient_bounds (n : ℕ) (reward M : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (y : Fin (n + 1) → E) (hM : 0 ≤ M) (hreward : M ≤ reward)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (i : Fin (n + 1)) :
    -(reward + M) ≤ coefficient n reward h0 h1 m0 m1 y i ∧
      coefficient n reward h0 h1 m0 m1 y i ≤ 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [coefficient, Fin.lastCases_last]
    constructor <;> linarith only [hreward, hM]
  · simp only [coefficient, Fin.lastCases_castSucc]
    have hh := abs_le.mp (hdelta j.succ (y j.succ))
    constructor <;> linarith only [hh.1, hh.2, hreward]

/- Full finite-T implication for the actual relay.  The premises are
   the preceding endpoint/hierarchy facts (regularity, packet convexity,
   bounded endpoint difference, and scalar constant margins), rather
   than assumed oracle/FOC/gradient identities or gate conclusions. -/
theorem stationarity_opens_all (n : ℕ) (β lam mu a sigma reward M C ell radius b0 eps : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (star ystar x y s : Fin (n + 1) → E) (theta : ℝ → ℝ)
    (hβ : 0 < β) (ha : 0 < a) (hsigma : 0 < sigma) (hell : 0 < ell)
    (hmu : 0 ≤ mu) (hM : 0 ≤ M) (hC : 0 ≤ C) (hradius : 0 ≤ radius)
    (hsc : ∀ t, StrongConvexOn (Set.univ : Set E) mu (h1 t))
    (hdiff : ∀ t, Differentiable ℝ (h1 t))
    (hyref : ∀ t, gradient (h1 t) (ystar t) = lam • star t)
    (hxref : ∀ t, β • star t + lam • ystar t = 0)
    (htheta : Differentiable ℝ theta) (hanti : Antitone theta)
    (hderiv : ∀ u, |deriv theta u| ≤ C)
    (hunit : ∀ u, 0 ≤ u → u ≤ radius ^ 2 → theta u = 1)
    (hreward : M ≤ reward)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (hsmall : (reward + M) * (2 * C / (a ^ 2 * ell ^ 2)) ≤ sigma / 2)
    (hwidth : 2 * eps ≤ β * ell * radius) (hclose : eps ≤ β * b0 * ell)
    (Phi : Blocks n E → ℝ) (G : Blocks n E)
    (hgrad : HasGradientAt Phi G (WithLp.toLp 2 x))
    (hstationary : ‖G‖ ≤ eps)
    (hvalue : Phi (WithLp.toLp 2 x) = family n β lam a sigma reward h0 h1 m0 m1
      (fun j => radialGate theta a ell (star j.castSucc)) x y s)
    (hmaxOuter : ∀ z : Fin (n + 1) → E,
      family n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) z y s ≤ Phi (WithLp.toLp 2 z))
    (hmaxDual : ∀ yy ss : Fin (n + 1) → E,
      family n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) x yy ss ≤
      family n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) x y s) :
    (∀ j : Fin n, radialGate theta a ell (star j.castSucc) (s j.castSucc) = 1) ∧
      (∀ t : Fin (n + 1), ‖x t - star t‖ ≤ b0 * ell) := by
  let gate : Fin n → E → ℝ := fun j => radialGate theta a ell (star j.castSucc)
  have hforce : ∀ t : Fin (n + 1), incoming n gate s t = 1 →
      β * ‖x t - star t‖ ≤ eps ∧ ‖s t - a • star t‖ ≤ 2 * a * eps / β := by
    intro t hactive
    have hy := actual_active_inner_coordinate n β lam a sigma reward h0 h1 m0 m1 gate
      x y s hdiff (fun yy => hmaxDual yy s) t hactive
    have hsupport := active_packet_support (h1 t) β lam mu (x t) (y t)
      (star t) (ystar t) hmu (hsc t) (hdiff t) hy (hyref t) (hxref t)
    have houter := actual_outer_coordinate n β lam a sigma reward h0 h1 m0 m1 gate
      x y s Phi G hgrad hvalue hmaxOuter t
    have hfoc := actual_relay_inner_coordinate n β lam a sigma reward h0 h1 m0 m1 gate
      x y s t _ (radial_gateExt_hasGradientAt n theta a ell star s htheta t)
      (fun ss => hmaxDual y ss)
    have hb := coefficient_bounds n reward M h0 h1 m0 m1 y hM hreward hdelta t
    have he : 0 ≤ etaExt n theta a ell star s t ∧
        etaExt n theta a ell star s t ≤ 2 * C / (a ^ 2 * ell ^ 2) := by
      refine Fin.lastCases ?_ (fun j => ?_) t
      · simp only [etaExt, Fin.lastCases_last]
        exact ⟨le_rfl, by positivity⟩
      · simpa [etaExt] using eta_nonneg_le theta a ell C
          (star _) (s _) ha hell hC hanti hderiv
    have hsm : (-coefficient n reward h0 h1 m0 m1 y t) * etaExt n theta a ell star s t ≤
        sigma / 2 := by
      calc
        _ ≤ (reward + M) * (2 * C / (a ^ 2 * ell ^ 2)) :=
          mul_le_mul (by linarith only [hb.1]) he.2 he.1
            (by linarith only [hreward, hM])
        _ ≤ _ := hsmall
    have hrel : a • (x t - star t) = (s t - a • star t) - (s t - a • x t) := by
      rw [smul_sub]
      abel
    have hstat : ‖G t‖ ≤ eps := (PiLp.norm_apply_le G t).trans hstationary
    exact radial_relay_force β a sigma eps (coefficient n reward h0 h1 m0 m1 y t)
      (etaExt n theta a ell star s t) (x t - star t) (s t - a • star t)
      (s t - a • x t) (β • x t + lam • y t) (G t)
      hβ ha hsigma hb.2 he.1 hsm hrel hfoc hsupport houter hstat
  have hopen : ∀ j : Fin n, incoming n gate s j.castSucc = 1 →
      gate j (s j.castSucc) = 1 := by
    intro j hactive
    apply radialGate_unit theta a ell radius (star j.castSucc) (s j.castSucc)
      ha hell hradius hunit
    refine (hforce j.castSucc hactive).2.trans ?_
    apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hwidth ha.le
    nlinarith only [hh]
  have hin : ∀ t : Fin (n + 1), incoming n gate s t = 1 := by
    intro t
    refine Fin.induction ?_ (fun j hj => ?_) t
    · simp [incoming]
    · simpa [incoming] using hopen j hj
  refine ⟨(fun j => hopen j (hin _)), ?_⟩
  intro t
  have hh := (hforce t (hin t)).1.trans hclose
  exact (mul_le_mul_iff_right₀ hβ).mp (by nlinarith only [hh])


/- The regrouping above is exactly the boxed family in the manuscript. -/
theorem family_eq_paper (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E) :
    family n β lam a sigma reward h0 h1 m0 m1 gate x y s =
      endpoint β lam (h1 0) (m1 0) (x 0) (y 0) -
      sigma / 2 * (∑ t, ‖s t - a • x t‖ ^ 2) +
      (∑ i, (endpoint β lam (h0 i.succ) (m0 i.succ) (x i.succ) (y i.succ) +
        gate i (s i.castSucc) *
          (endpoint β lam (h1 i.succ) (m1 i.succ) (x i.succ) (y i.succ) -
           endpoint β lam (h0 i.succ) (m0 i.succ) (x i.succ) (y i.succ)))) -
      reward * (∑ i, gate i (s i.castSucc)) := by
  unfold family
  rw [Fin.sum_univ_succ]
  simp only [incoming, Fin.cases_zero, one_mul, Fin.cases_succ]
  have hid : ∀ i : Fin n,
      endpoint β lam (h0 i.succ) (m0 i.succ) (x i.succ) (y i.succ) +
          gate i (s i.castSucc) * delta (h0 i.succ) (h1 i.succ)
            (m0 i.succ) (m1 i.succ) (y i.succ) =
      endpoint β lam (h0 i.succ) (m0 i.succ) (x i.succ) (y i.succ) +
          gate i (s i.castSucc) *
            (endpoint β lam (h1 i.succ) (m1 i.succ) (x i.succ) (y i.succ) -
             endpoint β lam (h0 i.succ) (m0 i.succ) (x i.succ) (y i.succ)) := by
    intro i
    dsimp [endpoint, delta]
    ring
  simp_rw [hid]
  dsimp only [endpoint, delta]
  ring

/- The reference identities are proved from the actual packet minimizer,
   h=H-c/2||.||², and lambda²=beta*c. -/
def fenchelPotential (H : E → ℝ) (c : ℝ) (y : E) : ℝ := H y - c / 2 * ‖y‖ ^ 2

theorem fenchel_reference (H : E → ℝ) (β c lam : ℝ) (z : E)
    (hβ : 0 < β) (hrel : lam ^ 2 = β * c)
    (hdiff : Differentiable ℝ H) (hmin : ∀ w, H z ≤ H w) :
    gradient (fenchelPotential H c) z = lam • ((-lam / β) • z) ∧
      β • ((-lam / β) • z) + lam • z = 0 := by
  have hz := PacketCore.gradient_eq_zero_at_global_min H z hmin
  have hg := (hdiff z).hasGradientAt
  have hn := hasStrictFDerivAt_norm_sq z
  have hf : HasGradientAt (fenchelPotential H c) (-c • z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hh := hg.hasFDerivAt.sub (hn.hasFDerivAt.const_smul (c / 2))
    rw [hz] at hh
    convert! hh using 1
    ext v
    simp only [InnerProductSpace.toDual_apply_apply, real_inner_smul_left,
        ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        innerSL_apply_apply, inner_zero_left]
    ring
  have hid : lam * (-lam / β) = -c := by
    apply (eq_neg_iff_add_eq_zero).mpr
    field_simp
    nlinarith only [hrel]
  constructor
  · rw [smul_smul, hid]
    exact hf.gradient
  · rw [smul_smul, show β * (-lam / β) = -lam by field_simp, neg_smul]
    abel

/- The value function below uses actual global inner maximizers; its
   derivative identities are proved above by a supporting difference,
   rather than assumed as a Danskin formula. -/
def exactValue (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ)
    (Y S : Blocks n E → (Fin (n + 1) → E)) (X : Blocks n E) : ℝ :=
  family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp (Y X) (S X)

theorem exact_relay_stationarity (n : ℕ) (β lam mu a sigma reward M C ell radius b0 eps : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (star ystar : Fin (n + 1) → E) (theta : ℝ → ℝ)
    (hβ : 0 < β) (ha : 0 < a) (hsigma : 0 < sigma) (hell : 0 < ell)
    (hmu : 0 ≤ mu) (hM : 0 ≤ M) (hC : 0 ≤ C) (hradius : 0 ≤ radius)
    (hsc : ∀ t, StrongConvexOn (Set.univ : Set E) mu (h1 t))
    (hdiff : ∀ t, Differentiable ℝ (h1 t))
    (hyref : ∀ t, gradient (h1 t) (ystar t) = lam • star t)
    (hxref : ∀ t, β • star t + lam • ystar t = 0)
    (htheta : Differentiable ℝ theta) (hanti : Antitone theta)
    (hderiv : ∀ u, |deriv theta u| ≤ C)
    (hunit : ∀ u, 0 ≤ u → u ≤ radius ^ 2 → theta u = 1)
    (hreward : M ≤ reward)
    (hdelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M)
    (hsmall : (reward + M) * (2 * C / (a ^ 2 * ell ^ 2)) ≤ sigma / 2)
    (hwidth : 2 * eps ≤ β * ell * radius) (hclose : eps ≤ β * b0 * ell)
    (Y S : Blocks n E → (Fin (n + 1) → E))
    (hmax : ∀ (Z : Blocks n E) (yy ss : Fin (n + 1) → E),
      family n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) Z.ofLp yy ss ≤
      exactValue n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) Y S Z)
    (X : Blocks n E)
    (hdiffValue : DifferentiableAt ℝ
      (exactValue n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) Y S) X)
    (hstationary : ‖gradient (exactValue n β lam a sigma reward h0 h1 m0 m1
        (fun j => radialGate theta a ell (star j.castSucc)) Y S) X‖ ≤ eps) :
    (∀ j : Fin n, radialGate theta a ell (star j.castSucc) (S X j.castSucc) = 1) ∧
      (∀ t : Fin (n + 1), ‖X t - star t‖ ≤ b0 * ell) := by
  apply stationarity_opens_all n β lam mu a sigma reward M C ell radius b0 eps
    h0 h1 m0 m1 star ystar X.ofLp (Y X) (S X) theta hβ ha hsigma hell
    hmu hM hC hradius hsc hdiff hyref hxref htheta hanti hderiv hunit hreward hdelta
    hsmall hwidth hclose
    (exactValue n β lam a sigma reward h0 h1 m0 m1
      (fun j => radialGate theta a ell (star j.castSucc)) Y S)
    _ (by simpa using hdiffValue.hasGradientAt) (by simpa using hstationary)
  · rfl
  · intro z
    exact hmax (WithLp.toLp 2 z) (Y X) (S X)
  · intro yy ss
    exact hmax X yy ss


/- These numerical margins are obtained by universal choices, with no
   dependence on T, L, epsilon, or a.  This addresses the stationarity
   part of the hierarchy only; global derivative budgets remain in the
   separate analytic-validity lemma. -/
theorem universal_stationarity_constants (b radius b0 C CM K0 : ℝ)
    (hb : 0 < b) (hradius : 0 < radius) (hb0 : 0 < b0)
    (hC : 0 ≤ C) (hCM : 0 ≤ CM) (hK0 : CM ≤ K0) :
    ∃ KD csigma : ℝ, 1 ≤ KD ∧ 0 < csigma ∧
      4 * C * (K0 + CM) ≤ csigma * KD ^ 2 ∧
      2 ≤ b * KD * radius ∧ 1 ≤ b * KD * b0 := by
  let KD := 1 + 2 / (b * radius) + 1 / (b * b0)
  let csigma := 4 * C * (K0 + CM) + 1
  have hrterm : 0 ≤ 2 / (b * radius) := by positivity
  have hbterm : 0 ≤ 1 / (b * b0) := by positivity
  have hKD : 1 ≤ KD := by dsimp [KD]; linarith only [hrterm, hbterm]
  have hKDpos : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hbig : 0 ≤ 4 * C * (K0 + CM) := by
    exact mul_nonneg (by positivity) (by linarith only [hK0, hCM])
  have hcsigma : 0 < csigma := by dsimp [csigma]; linarith only [hbig]
  refine ⟨KD, csigma, hKD, hcsigma, ?_, ?_, ?_⟩
  · have hsq : 1 ≤ KD ^ 2 := by nlinarith [sq_nonneg (KD - 1)]
    have hm := mul_le_mul_of_nonneg_left hsq hcsigma.le
    dsimp only [csigma] at *
    nlinarith only [hm]
  · have hfrac : 2 / (b * radius) ≤ KD := by dsimp [KD]; linarith only [hbterm]
    have hm := mul_le_mul_of_nonneg_right hfrac (mul_pos hb hradius).le
    have heq : 2 / (b * radius) * (b * radius) = 2 :=
      div_mul_cancel₀ _ (mul_pos hb hradius).ne'
    rw [heq] at hm
    nlinarith only [hm]
  · have hfrac : 1 / (b * b0) ≤ KD := by dsimp [KD]; linarith only [hrterm]
    have hm := mul_le_mul_of_nonneg_right hfrac (mul_pos hb hb0).le
    have heq : 1 / (b * b0) * (b * b0) = 1 :=
      div_mul_cancel₀ _ (mul_pos hb hb0).ne'
    rw [heq] at hm
    nlinarith only [hm]

theorem scaled_stationarity_margins (b KD csigma C CM K0 radius b0 L eps a : ℝ)
    (hL : 0 < L) (heps : 0 < eps) (ha : 0 < a) (hKD : 0 < KD)
    (hsmall : 4 * C * (K0 + CM) ≤ csigma * KD ^ 2)
    (hwidth : 2 ≤ b * KD * radius) (hclose : 1 ≤ b * KD * b0) :
    let energy := eps ^ 2 / L
    let width := KD * eps / L
    let curvature := csigma * L / a ^ 2
    ((K0 * energy + CM * energy) * (2 * C / (a ^ 2 * width ^ 2)) ≤ curvature / 2) ∧
      (2 * eps ≤ (b * L) * width * radius) ∧
      (eps ≤ (b * L) * b0 * width) := by
  dsimp only
  constructor
  · have hm := mul_le_mul_of_nonneg_left hsmall
      (by positivity : 0 ≤ L / (2 * a ^ 2 * KD ^ 2))
    convert! hm using 1 <;> field_simp <;> ring
  constructor
  · have hm := mul_le_mul_of_nonneg_right hwidth heps.le
    convert! hm using 1 <;> field_simp <;> ring
  · have hm := mul_le_mul_of_nonneg_right hclose heps.le
    convert! hm using 1 <;> field_simp <;> ring


theorem original_packet_relay_stationarity (n : ℕ)
    (β c lam mu a sigma reward M C ell radius b0 eps : ℝ)
    (H0 H1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (ystar : Fin (n + 1) → E) (theta : ℝ → ℝ)
    (hβ : 0 < β) (hrel : lam ^ 2 = β * c) (ha : 0 < a)
    (hsigma : 0 < sigma) (hell : 0 < ell) (hmu : 0 ≤ mu)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (hradius : 0 ≤ radius)
    (hscH : ∀ t, StrongConvexOn (Set.univ : Set E) (mu + c) (H1 t))
    (hdiffH : ∀ t, Differentiable ℝ (H1 t))
    (hminH : ∀ t z, H1 t (ystar t) ≤ H1 t z)
    (htheta : Differentiable ℝ theta) (hanti : Antitone theta)
    (hderiv : ∀ u, |deriv theta u| ≤ C)
    (hunit : ∀ u, 0 ≤ u → u ≤ radius ^ 2 → theta u = 1)
    (hreward : M ≤ reward)
    (hdeltaH : ∀ t z, |H0 t z - H1 t z + m1 t - m0 t| ≤ M)
    (hsmall : (reward + M) * (2 * C / (a ^ 2 * ell ^ 2)) ≤ sigma / 2)
    (hwidth : 2 * eps ≤ β * ell * radius) (hclose : eps ≤ β * b0 * ell)
    (Y S : Blocks n E → (Fin (n + 1) → E))
    (hmax : ∀ (Z : Blocks n E) (yy ss : Fin (n + 1) → E),
      family n β lam a sigma reward
        (fun t => fenchelPotential (H0 t) c) (fun t => fenchelPotential (H1 t) c) m0 m1
        (fun j => radialGate theta a ell ((-lam / β) • ystar j.castSucc)) Z.ofLp yy ss ≤
      exactValue n β lam a sigma reward
        (fun t => fenchelPotential (H0 t) c) (fun t => fenchelPotential (H1 t) c) m0 m1
        (fun j => radialGate theta a ell ((-lam / β) • ystar j.castSucc)) Y S Z)
    (X : Blocks n E)
    (hdiffValue : DifferentiableAt ℝ
      (exactValue n β lam a sigma reward
        (fun t => fenchelPotential (H0 t) c) (fun t => fenchelPotential (H1 t) c) m0 m1
        (fun j => radialGate theta a ell ((-lam / β) • ystar j.castSucc)) Y S) X)
    (hstationary : ‖gradient (exactValue n β lam a sigma reward
        (fun t => fenchelPotential (H0 t) c) (fun t => fenchelPotential (H1 t) c) m0 m1
        (fun j => radialGate theta a ell ((-lam / β) • ystar j.castSucc)) Y S) X‖ ≤ eps) :
    (∀ j : Fin n, radialGate theta a ell ((-lam / β) • ystar j.castSucc) (S X j.castSucc) = 1) ∧
      (∀ t : Fin (n + 1), ‖X t - (-lam / β) • ystar t‖ ≤ b0 * ell) := by
  have hsc : ∀ t, StrongConvexOn (Set.univ : Set E) mu (fenchelPotential (H1 t) c) := by
    intro t
    apply strongConvexOn_iff_convex.mpr
    convert! (strongConvexOn_iff_convex.mp (hscH t)) using 1
    funext z
    dsimp [fenchelPotential]
    ring
  have hd : ∀ t, Differentiable ℝ (fenchelPotential (H1 t) c) := by
    intro t
    exact (hdiffH t).sub (((differentiable_id : Differentiable ℝ (fun z : E => z)).norm_sq ℝ).const_mul (c / 2))
  have href := fun t => fenchel_reference (H1 t) β c lam (ystar t)
    hβ hrel (hdiffH t) (hminH t)
  have hdelta : ∀ t z,
      |delta (fenchelPotential (H0 t) c) (fenchelPotential (H1 t) c) (m0 t) (m1 t) z| ≤ M := by
    intro t z
    convert hdeltaH t z using 1
    congr 1
    dsimp [delta, fenchelPotential]
    ring
  exact exact_relay_stationarity n β lam mu a sigma reward M C ell radius b0 eps
    (fun t => fenchelPotential (H0 t) c) (fun t => fenchelPotential (H1 t) c) m0 m1
    (fun t => (-lam / β) • ystar t) ystar theta hβ ha hsigma hell hmu hM hC hradius
    hsc hd (fun t => (href t).1) (fun t => (href t).2) htheta hanti hderiv hunit
    hreward hdelta hsmall hwidth hclose Y S hmax X hdiffValue hstationary

end
end FangqingRelayStationarity
end

section
-- Source component: RelayBlockGeometry.lean

open scoped BigOperators

namespace FangqingRelayBlockGeometry

noncomputable section

abbrev Joint (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin 3 × Fin (n + 1) => E)
abbrev Pair (E : Type*) := WithLp 2 (E × E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairMap {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f g : D →L[ℝ] E) : D →L[ℝ] Pair E :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ E E).symm.toContinuousLinearMap.comp (f.prod g)

def coord (n : ℕ) (axis : Fin 3) (t : Fin (n + 1)) : Joint n E →L[ℝ] E :=
  PiLp.proj 2 (fun _ : Fin 3 × Fin (n + 1) => E) (axis, t)

def packet (n : ℕ) (t : Fin (n + 1)) : Joint n E →L[ℝ] Pair E :=
  pairMap (coord n 0 t) (coord n 1 t)

def relay (n : ℕ) (t : Fin (n + 1)) : Joint n E →L[ℝ] Pair E :=
  pairMap (coord n 0 t) (coord n 2 t)

def link (n : ℕ) (j : Fin n) : Joint n E →L[ℝ] Pair E :=
  pairMap (coord n 2 j.castSucc) (coord n 1 j.succ)

theorem pairMap_norm_sq {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (f g : D →L[ℝ] E) (z : D) :
    ‖pairMap f g z‖ ^ 2 = ‖f z‖ ^ 2 + ‖g z‖ ^ 2 := by
  simpa [pairMap] using WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (f z, g z))

theorem joint_norm_sq (n : ℕ) (z : Joint n E) :
    ‖z‖ ^ 2 =
      (∑ t, ‖z (0, t)‖ ^ 2) + (∑ t, ‖z (1, t)‖ ^ 2) + (∑ t, ‖z (2, t)‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [Fintype.sum_prod_type]
  rw [Fin.sum_univ_three]

theorem packet_energy (n : ℕ) (z : Joint n E) :
    (∑ t, ‖packet n t z‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have h2 : 0 ≤ ∑ t : Fin (n + 1), ‖z (2, t)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [packet, pairMap_norm_sq]
  rw [Finset.sum_add_distrib, joint_norm_sq]
  simp only [coord, PiLp.proj_apply]
  linarith only [h2]

theorem relay_energy (n : ℕ) (z : Joint n E) :
    (∑ t, ‖relay n t z‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have h1 : 0 ≤ ∑ t : Fin (n + 1), ‖z (1, t)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp_rw [relay, pairMap_norm_sq]
  rw [Finset.sum_add_distrib, joint_norm_sq]
  simp only [coord, PiLp.proj_apply]
  linarith only [h1]

theorem link_energy (n : ℕ) (z : Joint n E) :
    (∑ j, ‖link n j z‖ ^ 2) ≤ ‖z‖ ^ 2 := by
  have hx : 0 ≤ ∑ t : Fin (n + 1), ‖z (0, t)‖ ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hy0 := sq_nonneg ‖z (1, (0 : Fin (n + 1)))‖
  have hslast := sq_nonneg ‖z (2, Fin.last n)‖
  have hy : (∑ t : Fin (n + 1), ‖z (1, t)‖ ^ 2) =
      ‖z (1, (0 : Fin (n + 1)))‖ ^ 2 + ∑ j : Fin n, ‖z (1, j.succ)‖ ^ 2 :=
    Fin.sum_univ_succ _
  have hs : (∑ t : Fin (n + 1), ‖z (2, t)‖ ^ 2) =
      (∑ j : Fin n, ‖z (2, j.castSucc)‖ ^ 2) + ‖z (2, Fin.last n)‖ ^ 2 :=
    Fin.sum_univ_castSucc _
  simp_rw [link, pairMap_norm_sq]
  rw [Finset.sum_add_distrib, joint_norm_sq, hy, hs]
  simp only [coord, PiLp.proj_apply]
  linarith only [hx, hy0, hslast]

end
end FangqingRelayBlockGeometry
end

section
-- Source component: RelayAnalyticAssembly.lean

open scoped BigOperators ContDiff

set_option maxHeartbeats 1200000

namespace FangqingRelayAnalyticAssembly

open FangqingRelayBlockGeometry FangqingRelayStationarity FangqingDisjointBlockBounds

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def localPacket (n : ℕ) (β lam : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) :
    Fin (n + 1) → Pair E → ℝ :=
  Fin.cases (fun p => endpoint β lam (h1 0) (m1 0) p.fst p.snd)
    (fun j p => endpoint β lam (h0 j.succ) (m0 j.succ) p.fst p.snd)

def localRelay (a sigma : ℝ) (p : Pair E) : ℝ :=
  -sigma / 2 * ‖p.snd - a • p.fst‖ ^ 2

def localLink (n : ℕ) (reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (j : Fin n) (p : Pair E) : ℝ :=
  gate j p.fst * (delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) p.snd - reward)

def assembled (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (z : Joint n E) : ℝ :=
  blockSum (packet n) (localPacket n β lam h0 h1 m0 m1) z +
  blockSum (relay n) (fun _ : Fin (n + 1) => localRelay a sigma) z +
  blockSum (link n) (localLink n reward h0 h1 m0 m1 gate) z

theorem assembled_eq_family (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (z : Joint n E) :
    assembled n β lam a sigma reward h0 h1 m0 m1 gate z =
      family n β lam a sigma reward h0 h1 m0 m1 gate
        (fun t => z (0, t)) (fun t => z (1, t)) (fun t => z (2, t)) := by
  have hp : blockSum (packet n) (localPacket n β lam h0 h1 m0 m1) z =
      endpoint β lam (h1 0) (m1 0) (z (0, 0)) (z (1, 0)) +
      ∑ j : Fin n, endpoint β lam (h0 j.succ) (m0 j.succ) (z (0, j.succ)) (z (1, j.succ)) := by
    unfold blockSum
    rw [Fin.sum_univ_succ]
    simp [localPacket, packet, pairMap, coord]
  have hr : blockSum (relay n) (fun _ : Fin (n + 1) => localRelay a sigma) z =
      -sigma / 2 * ∑ t, ‖z (2, t) - a • z (0, t)‖ ^ 2 := by
    simp [blockSum, localRelay, relay, pairMap, coord, Finset.mul_sum]
  have hg : blockSum (link n) (localLink n reward h0 h1 m0 m1 gate) z =
      (∑ j : Fin n, gate j (z (2, j.castSucc)) *
        delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) (z (1, j.succ))) -
      reward * ∑ j : Fin n, gate j (z (2, j.castSucc)) := by
    simp [blockSum, localLink, link, pairMap, coord, mul_sub, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_comm, sub_mul]
  have hd : ∀ j : Fin n,
      endpoint β lam (h1 j.succ) (m1 j.succ) (z (0, j.succ)) (z (1, j.succ)) -
      endpoint β lam (h0 j.succ) (m0 j.succ) (z (0, j.succ)) (z (1, j.succ)) =
      delta (h0 j.succ) (h1 j.succ) (m0 j.succ) (m1 j.succ) (z (1, j.succ)) := by
    intro j
    dsimp [endpoint, delta]
    ring
  unfold assembled
  rw [hp, hr, hg, family_eq_paper]
  simp_rw [hd]
  rw [Finset.sum_add_distrib]
  ring

theorem sum3_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g h : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (hh : ContDiff ℝ 3 h)
    (j : ℕ) (hj : (j : ℕ∞ω) ≤ 3) (x : X) (A B C : ℝ)
    (hA : ‖iteratedFDeriv ℝ j f x‖ ≤ A) (hB : ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (hC : ‖iteratedFDeriv ℝ j h x‖ ≤ C) :
    ‖iteratedFDeriv ℝ j (fun z => f z + g z + h z) x‖ ≤ A + B + C := by
  rw [fun_iteratedFDeriv_add_apply (((hf.add hg).of_le hj).contDiffAt) ((hh.of_le hj).contDiffAt),
    fun_iteratedFDeriv_add_apply ((hf.of_le hj).contDiffAt) ((hg.of_le hj).contDiffAt)]
  exact (norm_add_le _ _).trans
    (add_le_add ((norm_add_le _ _).trans (add_le_add hA hB)) hC)


end
end FangqingRelayAnalyticAssembly
end

section
-- Source component: RelayJointReindexing.lean

open scoped BigOperators

namespace FangqingRelayJointReindexing

noncomputable section

abbrev Outer (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin (n + 1) => E)
abbrev Dual (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin 2 × Fin (n + 1) => E)
abbrev ProductJoint (n : ℕ) (E : Type*) := WithLp 2 (Outer n E × Dual n E)
abbrev FlatJoint (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin 3 × Fin (n + 1) => E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def toFlat (n : ℕ) (z : ProductJoint n E) : FlatJoint n E :=
  WithLp.toLp 2 (fun i : Fin 3 × Fin (n + 1) => Fin.cases (z.fst i.2) (fun j => z.snd (j, i.2)) i.1)

def fromFlat (n : ℕ) (w : FlatJoint n E) : ProductJoint n E :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun t => w (0, t)),
    WithLp.toLp 2 (fun i : Fin 2 × Fin (n + 1) => Fin.cases (w (1, i.2)) (fun _ => w (2, i.2)) i.1))

theorem fromFlat_toFlat (n : ℕ) (z : ProductJoint n E) : fromFlat n (toFlat n z) = z := by
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    funext t
    rfl
  · apply (WithLp.ext_iff 2).mpr
    funext i
    rcases i with ⟨j, t⟩
    fin_cases j <;> rfl

theorem toFlat_fromFlat (n : ℕ) (w : FlatJoint n E) : toFlat n (fromFlat n w) = w := by
  apply (WithLp.ext_iff 2).mpr
  funext i
  rcases i with ⟨j, t⟩
  fin_cases j <;> rfl

def linearEquiv (n : ℕ) : ProductJoint n E ≃ₗ[ℝ] FlatJoint n E where
  toFun := toFlat n
  invFun := fromFlat n
  left_inv := fromFlat_toFlat n
  right_inv := toFlat_fromFlat n
  map_add' := by
    intro z w
    apply (WithLp.ext_iff 2).mpr
    funext i
    rcases i with ⟨j, t⟩
    fin_cases j <;> rfl
  map_smul' := by
    intro r z
    apply (WithLp.ext_iff 2).mpr
    funext i
    rcases i with ⟨j, t⟩
    fin_cases j <;> rfl

theorem toFlat_norm_sq (n : ℕ) (z : ProductJoint n E) : ‖toFlat n z‖ ^ 2 = ‖z‖ ^ 2 := by
  have hf : ‖toFlat n z‖ ^ 2 = (∑ t, ‖z.fst t‖ ^ 2) +
      (∑ t, ‖z.snd (0, t)‖ ^ 2) + (∑ t, ‖z.snd (1, t)‖ ^ 2) := by
    rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Fin.sum_univ_three]
    rfl
  have hp := WithLp.prod_norm_sq_eq_of_L2 z
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, Fin.sum_univ_two] at hp
  linarith only [hf, hp]

def flatten (n : ℕ) : ProductJoint n E ≃ₗᵢ[ℝ] FlatJoint n E :=
  { linearEquiv n with
    norm_map' := by
      intro z
      change ‖toFlat n z‖ = ‖z‖
      have hh := toFlat_norm_sq n z
      nlinarith only [hh, norm_nonneg (toFlat n z), norm_nonneg z] }

theorem flatten_x (n : ℕ) (z : ProductJoint n E) (t : Fin (n + 1)) : flatten n z (0, t) = z.fst t := rfl

theorem flatten_y (n : ℕ) (z : ProductJoint n E) (t : Fin (n + 1)) : flatten n z (1, t) = z.snd (0, t) := rfl

theorem flatten_s (n : ℕ) (z : ProductJoint n E) (t : Fin (n + 1)) : flatten n z (2, t) = z.snd (1, t) := rfl

end
end FangqingRelayJointReindexing
end

section
-- Source component: RelayFenchelInterfaces.lean

namespace FangqingRelayFenchelInterfaces

open FangqingRelayStationarity FangqingFenchelEndpointClass

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def reduced (H : E → ℝ) (c : ℝ) (y : E) : ℝ := H y - c / 2 * ‖y‖ ^ 2

theorem endpoint_from_H (H : E → ℝ) (beta c lam m : ℝ) (p : FangqingFenchelEndpointClass.Joint E) :
    endpoint beta lam (reduced H c) m p.fst p.snd = jointEndpoint H beta c lam m p := by
  dsimp [endpoint, reduced, jointEndpoint, quadratic]
  ring

theorem delta_from_H (H0 H1 : E → ℝ) (c m0 m1 : ℝ) (y : E) :
    delta (reduced H0 c) (reduced H1 c) m0 m1 y = H0 y - H1 y + m1 - m0 := by
  dsimp [delta, reduced]
  ring

theorem delta_from_actual_minima (H0 H1 : E → ℝ) (c : ℝ) (z0 z1 y : E) :
    delta (reduced H0 c) (reduced H1 c) (H0 z0) (H1 z1) y =
      H0 y - H1 y + H1 z1 - H0 z0 := delta_from_H H0 H1 c _ _ y

theorem reduced_strongConvex (H : E → ℝ) (nu c : ℝ)
    (hs : StrongConvexOn (Set.univ : Set E) nu H) :
    StrongConvexOn (Set.univ : Set E) (nu - c) (reduced H c) := by
  apply strongConvexOn_iff_convex.mpr
  have heq : (fun y => reduced H c y - (nu - c) / 2 * ‖y‖ ^ 2) =
      (fun y => H y - nu / 2 * ‖y‖ ^ 2) := by
    funext y
    dsimp [reduced]
    ring
  rw [heq]
  exact strongConvexOn_iff_convex.mp hs

end
end FangqingRelayFenchelInterfaces
end

section
-- Source component: RelayJointClassTransport.lean

open scoped ContDiff NNReal

namespace FangqingRelayJointClassTransport

open FangqingRelayJointReindexing FangqingRelayStationarity FangqingRelayAnalyticAssembly
  FangqingJetToRegularity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def productFamily (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (z : ProductJoint n E) : ℝ :=
  family n beta lam a sigma reward h0 h1 m0 m1 gate z.fst.ofLp
    (fun t => z.snd (0, t)) (fun t => z.snd (1, t))

theorem productFamily_eq_pullback (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ) :
    productFamily n beta lam a sigma reward h0 h1 m0 m1 gate =
      assembled n beta lam a sigma reward h0 h1 m0 m1 gate ∘ (flatten n).toContinuousLinearEquiv.toContinuousLinearMap := by
  funext z
  change family n beta lam a sigma reward h0 h1 m0 m1 gate z.fst.ofLp
    (fun t => z.snd (0, t)) (fun t => z.snd (1, t)) =
      assembled n beta lam a sigma reward h0 h1 m0 m1 gate (flatten n z)
  rw [assembled_eq_family]
  simp only [flatten_x, flatten_y, flatten_s]

theorem flatten_clm_norm_le (n : ℕ) : ‖(flatten (E := E) n).toContinuousLinearEquiv.toContinuousLinearMap‖ ≤ 1 := by
  refine ((flatten (E := E) n).toContinuousLinearEquiv.toContinuousLinearMap).opNorm_le_bound (by norm_num) ?_
  intro z
  simpa only [one_mul] using! le_of_eq ((flatten (E := E) n).norm_map z)

theorem actual_product_joint_class (n : ℕ) (beta lam a sigma reward L rho : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hJ : ContDiff ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) z‖ ≤ L)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) x -
      iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) y‖ ≤ rho * ‖x - y‖) :
    let F := productFamily n beta lam a sigma reward h0 h1 m0 m1 gate
    ContDiff ℝ 2 F ∧
    (∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) ∧
    FangqingFenchelEndpointClass.HessianRate F rho := by
  intro F
  let P := (flatten (E := E) n).toContinuousLinearEquiv.toContinuousLinearMap
  let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
  have heq : F = J ∘ P := productFamily_eq_pullback n beta lam a sigma reward h0 h1 m0 m1 gate
  have hFc : ContDiff ℝ 2 F := by rw [heq]; exact hJ.comp P.contDiff
  have hF2 : ∀ z, ‖iteratedFDeriv ℝ 2 F z‖ ≤ L := by
    intro z
    rw [heq]
    exact (FangqingRelayProductBounds.norm_iterated_comp_contraction J P 2 hJ (flatten_clm_norm_le n) z 2 le_rfl).trans (h2 _)
  have hF2Lip : ∀ x y, ‖iteratedFDeriv ℝ 2 F x - iteratedFDeriv ℝ 2 F y‖ ≤ rho * ‖x - y‖ := by
    intro x y
    rw [heq]
    have hh := (FangqingFenchelEndpointClass.second_jet_pullback_difference_bound J hJ P (flatten_clm_norm_le n) x y).trans (hLip (P x) (P y))
    have hnorm : ‖P x - P y‖ = ‖x - y‖ := by
      rw [← map_sub]
      exact (flatten (E := E) n).norm_map (x - y)
    rw [hnorm] at hh
    exact hh
  let Ln : ℝ≥0 := ⟨L, hL⟩
  have hgrad := gradient_lipschitz_from_second_jet F hFc Ln hF2
  exact ⟨hFc, fun x y => hgrad.norm_sub_le x y, fun x y =>
    (hessian_difference_norm_le_second_jet F x y).trans (hF2Lip x y)⟩

end
end FangqingRelayJointClassTransport
end

section
-- Source component: SmoothDescent.lean

namespace OriginalAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem smooth_descent_upper
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x s : E) :
    f (x + s) ≤ f x + inner ℝ (gradient f x) s + L / 2 * ‖s‖ ^ 2 := by
  let a : ℝ → E := fun t => x + t • s
  let p : ℝ → ℝ := fun t =>
    f (a t) - f x - t * inner ℝ (gradient f x) s - L / 2 * t ^ 2 * ‖s‖ ^ 2
  let p' : ℝ → ℝ := fun t =>
    inner ℝ (gradient f (a t)) s - inner ℝ (gradient f x) s -
      L / 2 * (2 * t) * ‖s‖ ^ 2
  have ha : ∀ t : ℝ, HasDerivAt a s t := by
    intro t
    simpa only [a, one_smul, id_eq] using
      (((hasDerivAt_id t).smul_const s).const_add x)
  have hp : ∀ t : ℝ, HasDerivAt p (p' t) t := by
    intro t
    have hf : HasDerivAt (fun t => f (a t)) (inner ℝ (gradient f (a t)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (a t)).hasFDerivAt.comp_hasDerivAt t (ha t))
    have hlin : HasDerivAt (fun t : ℝ => t * inner ℝ (gradient f x) s)
        (inner ℝ (gradient f x) s) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient f x) s)
    have hquad : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖s‖ ^ 2)
        (L / 2 * (2 * t) * ‖s‖ ^ 2) t := by
      have ht := (((hasDerivAt_id t).pow 2).const_mul (L / 2)).mul_const (‖s‖ ^ 2)
      convert ht using 1 <;> first | rfl | simp
    simpa only [p, p', Pi.sub_def] using ((hf.sub_const (f x)).sub hlin).sub hquad
  have hpnonpos : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), p' t ≤ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (interior_subset ht).1
    have hl := hlip (a t) x
    have hnorm : ‖a t - x‖ = t * ‖s‖ := by
      simp [a, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    rw [hnorm] at hl
    have hi := real_inner_le_norm (gradient f (a t) - gradient f x) s
    rw [inner_sub_left] at hi
    have hm := mul_le_mul_of_nonneg_right hl (norm_nonneg s)
    dsimp [p']
    nlinarith only [hi, hm]
  have hm : AntitoneOn p (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
      (fun t _ => (hp t).continuousAt.continuousWithinAt)
      (fun t _ => (hp t).hasDerivWithinAt) hpnonpos
  have h := hm (by constructor <;> norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by constructor <;> norm_num : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  have h' := h
  dsimp [p, a] at h'
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_pow, zero_pow (by omega : 2 ≠ 0)] at h'
  linarith

theorem gradient_step_descent
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x : E) :
    f (x - L⁻¹ • gradient f x) ≤ f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
  have h := smooth_descent_upper f L hL hdiff hlip x (- (L⁻¹ • gradient f x))
  rw [inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)] at h
  have hn : L ≠ 0 := ne_of_gt hL
  have heq : f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
      L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 =
      f x - ‖gradient f x‖ ^ 2 / (2 * L) := by
    field_simp
    <;> ring
  have h' : f (x - L⁻¹ • gradient f x) ≤
      f x - L⁻¹ * ‖gradient f x‖ ^ 2 +
        L / 2 * (L⁻¹ * ‖gradient f x‖) ^ 2 := by
    simpa only [sub_eq_add_neg] using h
  rwa [heq] at h'


theorem exists_small_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  by_contra hgoal
  have hlarge : ∀ x : E, δ < ‖gradient f x‖ := by
    intro x
    exact lt_of_not_ge (fun hx => hgoal ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := hbelow
  let c : ℝ := δ ^ 2 / (2 * L)
  have hc : 0 < c := by dsimp [c]; positivity
  let x : ℕ → E := fun n =>
    Nat.rec (0 : E) (fun _ z => z - L⁻¹ • gradient f z) n
  have hx (n : ℕ) : x (n + 1) = x n - L⁻¹ • gradient f (x n) := by rfl
  have hstep (n : ℕ) : f (x (n + 1)) ≤ f (x n) - c := by
    have hsq : δ ^ 2 ≤ ‖gradient f (x n)‖ ^ 2 :=
      (sq_le_sq₀ hδ.le (norm_nonneg _)).2 (hlarge (x n)).le
    have hquot : c ≤ ‖gradient f (x n)‖ ^ 2 / (2 * L) := by
      dsimp [c]
      exact div_le_div_of_nonneg_right hsq (by positivity)
    rw [hx n]
    exact le_trans (gradient_step_descent f L hL hdiff hlip (x n))
      (sub_le_sub_left hquot (f (x n)))
  have hvalues : ∀ n : ℕ, f (x n) ≤ f (x 0) - (n : ℝ) * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hs := hstep n
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hncast]
      linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((f (x 0) - b) / c)
  have hnprod : f (x 0) - b < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have hv := hvalues n
  have hb' := hb (x n)
  linarith


theorem not_uniform_positive_gradient_lower_bound
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ ∀ x : E, δ ≤ ‖gradient f x‖ := by
  intro hlarge
  obtain ⟨x, hx⟩ := exists_small_gradient f L hL hdiff hlip hbelow (δ / 2) (by positivity)
  have hh := hlarge x
  linarith


theorem lipschitz_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L) :
    ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖ := by
  intro x y
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ (Set.univ : Set E)) => hgrad_diff z)
    (fun z (_ : z ∈ (Set.univ : Set E)) => hbound z)
    (convex_univ : Convex ℝ (Set.univ : Set E))
    (Set.mem_univ y) (Set.mem_univ x)


theorem exists_small_gradient_of_bounded_fderiv_gradient
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hgrad_diff : Differentiable ℝ (gradient f))
    (hbound : ∀ x : E, ‖fderiv ℝ (gradient f) x‖ ≤ L)
    (hbelow : ∃ b : ℝ, ∀ x : E, b ≤ f x)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ x : E, ‖gradient f x‖ ≤ δ := by
  exact exists_small_gradient f L hL hdiff
    (lipschitz_gradient_of_bounded_fderiv_gradient f L hgrad_diff hbound) hbelow δ hδ

end OriginalAudit
end

section
-- Source component: SaddleValueRegularity.lean

namespace OriginalSaddleRegularity

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem gradient_neg_of_differentiable
    (f : E → ℝ) (hdiff : Differentiable ℝ f) (x : E) :
    gradient (fun y => -f y) x = -gradient f x := by
  have h : HasGradientAt (fun y => -f y) (-gradient f x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    convert ((hdiff x).hasGradientAt.hasFDerivAt.neg) using 1 <;>
      first | rfl | simp only [map_neg, Pi.neg_def]
  exact (hdiff.neg x).hasGradientAt.unique h

theorem convex_of_global_support
    (g : E → ℝ) (v : E → E)
    (hsupport : ∀ x y : E, g x + inner ℝ (v x) (y - x) ≤ g y) :
    ConvexOn ℝ (Set.univ : Set E) g := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hzero : a • (x - z) + b • (y - z) = 0 := by
    calc
      a • (x - z) + b • (y - z) = a • x + b • y - (a + b) • z := by
        simp only [smul_sub, add_smul]
        abel
      _ = 0 := by rw [hab, one_smul]; exact sub_self z
  have hi := congrArg (fun w : E => inner ℝ (v z) w) hzero
  simp only [inner_add_right, inner_smul_right, inner_zero_right] at hi
  have h1 := mul_le_mul_of_nonneg_left (hsupport z x) ha
  have h2 := mul_le_mul_of_nonneg_left (hsupport z y) hb
  change g z ≤ a * g x + b * g y
  calc
    g z = (a + b) * g z := by rw [hab, one_mul]
    _ = a * (g z + inner ℝ (v z) (x - z)) +
        b * (g z + inner ℝ (v z) (y - z)) := by nlinarith only [hi]
    _ ≤ a * g x + b * g y := add_le_add h1 h2

theorem smooth_gradient_lower_support
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖)
    (x y : E) :
    f x + inner ℝ (gradient f x) (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  have hneg : ∀ a b : E,
      ‖gradient (fun t => -f t) a - gradient (fun t => -f t) b‖ ≤ L * ‖a - b‖ := by
    intro a b
    rw [gradient_neg_of_differentiable f hdiff a,
      gradient_neg_of_differentiable f hdiff b]
    simpa only [neg_sub_neg, norm_sub_rev] using hlip a b
  have h := OriginalAudit.smooth_descent_upper (fun t => -f t) L hL hdiff.neg hneg x (y - x)
  rw [gradient_neg_of_differentiable f hdiff x, inner_neg_left] at h
  have hxy : x + (y - x) = y := by abel
  rw [hxy] at h
  linarith

theorem smooth_function_weakly_convex
    (f : E → ℝ) (L : ℝ) (hL : 0 < L)
    (hdiff : Differentiable ℝ f)
    (hlip : ∀ x y : E, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) :
    StrongConvexOn (Set.univ : Set E) (-L) f := by
  apply strongConvexOn_iff_convex.mpr
  apply convex_of_global_support _ (fun x => gradient f x + L • x)
  intro x y
  have h := smooth_gradient_lower_support f L hL hdiff hlip x y
  rw [norm_sub_sq_real] at h
  have hsym : inner ℝ y x = inner ℝ x y := real_inner_comm _ _
  rw [hsym] at h
  simp only [inner_sub_right] at h
  simp only [inner_add_left, real_inner_smul_left, inner_sub_right,
    real_inner_self_eq_norm_sq]
  nlinarith only [h]

noncomputable def value (f : E → F → ℝ) (Y : E → F) (x : E) : ℝ := f x (Y x)

theorem value_weakly_convex_from_actual_maxima
    (f : E → F → ℝ) (L : ℝ)
    (hweak : ∀ y : F, StrongConvexOn (Set.univ : Set E) (-L) (fun x => f x y))
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x)) :
    StrongConvexOn (Set.univ : Set E) (-L) (value f Y) := by
  apply strongConvexOn_iff_convex.mpr
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  let z := a • x + b • y
  have hc := (strongConvexOn_iff_convex.mp (hweak (Y z))).2
    (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  have h1 := mul_le_mul_of_nonneg_left (hY x (Y z)) ha
  have h2 := mul_le_mul_of_nonneg_left (hY y (Y z)) hb
  simp only [smul_eq_mul] at hc ⊢
  dsimp only [value, z] at *
  nlinarith only [hc, h1, h2]

theorem exists_inner_maximum
    [FiniteDimensional ℝ F]
    (f : E → F → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiff : ∀ x : E, Differentiable ℝ (f x)) (x : E) :
    ∃ y : F, ∀ z : F, f x z ≤ f x y := by
  obtain ⟨y, hy⟩ := PacketCore.exists_inner_maximizer_finiteDimensional
    (fun y => -f x y) μ 0 0 0 0 hμ (by simpa using hsc x) (hdiff x).neg (0 : F)
  refine ⟨y, ?_⟩
  intro z
  simpa [PacketCore.saddleValue] using hy z

theorem inner_maximum_quadratic_gap
    (f : E → F → ℝ) (μ : ℝ)
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hdiff : ∀ x : E, Differentiable ℝ (f x))
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x : E) (y : F) :
    f x y ≤ f x (Y x) - μ / 2 * ‖y - Y x‖ ^ 2 := by
  have hzero : gradient (fun y => -f x y) (Y x) = 0 :=
    PacketCore.gradient_eq_zero_at_global_min _ _ (fun z => neg_le_neg (hY x z))
  have hs := PacketCore.strongConvex_support (fun y => -f x y) μ
    (hsc x) (hdiff x).neg (Y x) y
  rw [hzero, inner_zero_left] at hs
  linarith

theorem value_quadratic_error_bounds
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x z : E) :
    -(L / 2 * ‖z - x‖ ^ 2) ≤
      value f Y z - value f Y x - inner ℝ (gradient (fun t => f t (Y x)) x) (z - x) ∧
    value f Y z - value f Y x - inner ℝ (gradient (fun t => f t (Y x)) x) (z - x) ≤
      (L / 2 + L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by
  have hlo := smooth_gradient_lower_support (fun t => f t (Y x)) L hL
    (hdiffX (Y x)) (hxx (Y x)) x z
  have hmax := hY z (Y x)
  have hu := OriginalAudit.smooth_descent_upper (fun t => f t (Y z)) L hL
    (hdiffX (Y z)) (hxx (Y z)) x (z - x)
  have hxz : x + (z - x) = z := by abel
  rw [hxz] at hu
  have hgap := inner_maximum_quadratic_gap f μ hsc hdiffY Y hY x (Y z)
  have hi := real_inner_le_norm
    (gradient (fun t => f t (Y z)) x - gradient (fun t => f t (Y x)) x) (z - x)
  rw [inner_sub_left] at hi
  have him := mul_le_mul_of_nonneg_right (hxy x (Y z) (Y x)) (norm_nonneg (z - x))
  have hyoung := PacketCore.scalar_young μ (L * ‖z - x‖) (‖Y z - Y x‖) hμ
  have heq : (L * ‖z - x‖) ^ 2 / (2 * μ) =
      (L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by ring
  rw [heq] at hyoung
  dsimp only [value]
  constructor
  · linarith only [hlo, hmax]
  · nlinarith only [hu, hgap, hi, him, hyoung]

theorem value_hasGradientAt
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x))
    (x : E) :
    HasGradientAt (value f Y) (gradient (fun t => f t (Y x)) x) x := by
  apply PacketCore.hasGradientAt_of_quadratic_remainder _ _ _ (L / 2 + L ^ 2 / (2 * μ))
  intro z
  have h := value_quadratic_error_bounds f L μ hL hμ hdiffX hdiffY hsc hxx hxy Y hY x z
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hp : 0 ≤ (L ^ 2 / (2 * μ)) * ‖z - x‖ ^ 2 := by positivity
    nlinarith only [h.1, hp]
  · exact h.2

theorem value_differentiable_and_weakly_convex
    (f : E → F → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 < μ)
    (hdiffX : ∀ y : F, Differentiable ℝ (fun x => f x y))
    (hdiffY : ∀ x : E, Differentiable ℝ (f x))
    (hsc : ∀ x : E, StrongConvexOn (Set.univ : Set F) μ (fun y => -f x y))
    (hxx : ∀ y : F, ∀ x z : E,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t y) z‖ ≤ L * ‖x - z‖)
    (hxy : ∀ x : E, ∀ y z : F,
      ‖gradient (fun t => f t y) x - gradient (fun t => f t z) x‖ ≤ L * ‖y - z‖)
    (Y : E → F) (hY : ∀ x : E, ∀ y : F, f x y ≤ f x (Y x)) :
    Differentiable ℝ (value f Y) ∧ StrongConvexOn (Set.univ : Set E) (-L) (value f Y) := by
  constructor
  · intro x
    exact (value_hasGradientAt f L μ hL hμ hdiffX hdiffY hsc hxx hxy Y hY x).differentiableAt
  · exact value_weakly_convex_from_actual_maxima f L
      (fun y => smooth_function_weakly_convex (fun x => f x y) L hL (hdiffX y) (hxx y)) Y hY

end OriginalSaddleRegularity
end

section
-- Source component: JointSliceRegularity.lean

namespace JointSliceRegularity

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev JointSpace (E F : Type*) := WithLp 2 (E × F)

noncomputable def axisX : E →ₗᵢ[ℝ] JointSpace E F where
  toFun x := WithLp.toLp 2 (x, (0 : F))
  map_add' x x' := by
    apply (WithLp.ext_iff 2).mpr
    change (x + x', (0 : F)) = (x, (0 : F)) + (x', (0 : F))
    simp
  map_smul' r x := by
    apply (WithLp.ext_iff 2).mpr
    change (r • x, (0 : F)) = r • (x, (0 : F))
    simp
  norm_map' x := WithLp.norm_toLp_fst 2 E F x

noncomputable def axisY : F →ₗᵢ[ℝ] JointSpace E F where
  toFun y := WithLp.toLp 2 ((0 : E), y)
  map_add' y y' := by
    apply (WithLp.ext_iff 2).mpr
    change ((0 : E), y + y') = ((0 : E), y) + ((0 : E), y')
    simp
  map_smul' r y := by
    apply (WithLp.ext_iff 2).mpr
    change ((0 : E), r • y) = r • ((0 : E), y)
    simp
  norm_map' y := WithLp.norm_toLp_snd 2 E F y

noncomputable def point (x : E) (y : F) : JointSpace E F := axisX x + axisY y

noncomputable def curry (J : JointSpace E F → ℝ) (x : E) (y : F) : ℝ := J (point x y)


theorem point_eq_toLp (x : E) (y : F) : point x y = WithLp.toLp 2 (x, y) := by
  apply (WithLp.ext_iff 2).mpr
  change (x, (0 : F)) + ((0 : E), y) = (x, y)
  simp


theorem norm_axisX (x : E) : ‖axisX (F := F) x‖ = ‖x‖ :=
  (axisX (E := E) (F := F)).norm_map x


theorem norm_axisY (y : F) : ‖axisY (E := E) y‖ = ‖y‖ :=
  (axisY (E := E) (F := F)).norm_map y


theorem norm_fst_projection (z : JointSpace E F) : ‖z.fst‖ ≤ ‖z‖ :=
  WithLp.norm_fst_le E z


theorem norm_snd_projection (z : JointSpace E F) : ‖z.snd‖ ≤ ‖z‖ :=
  WithLp.norm_snd_le E z


theorem norm_fst_projection_sub (z w : JointSpace E F) : ‖z.fst - w.fst‖ ≤ ‖z - w‖ := by
  simpa only [WithLp.sub_fst] using norm_fst_projection (z - w)


theorem norm_snd_projection_sub (z w : JointSpace E F) : ‖z.snd - w.snd‖ ≤ ‖z - w‖ := by
  simpa only [WithLp.sub_snd] using norm_snd_projection (z - w)


theorem point_sub_same_y (x x' : E) (y : F) :
    point x y - point x' y = axisX (F := F) (x - x') := by
  dsimp [point]
  rw [map_sub]
  abel


theorem point_sub_same_x (x : E) (y y' : F) :
    point x y - point x y' = axisY (E := E) (y - y') := by
  dsimp [point]
  rw [map_sub]
  abel


theorem norm_point_sub_same_y (x x' : E) (y : F) :
    ‖point x y - point x' y‖ = ‖x - x'‖ := by
  rw [point_sub_same_y, norm_axisX]


theorem norm_point_sub_same_x (x : E) (y y' : F) :
    ‖point x y - point x y'‖ = ‖y - y'‖ := by
  rw [point_sub_same_x, norm_axisY]


theorem inner_axisX (z : JointSpace E F) (v : E) :
    inner ℝ z (axisX v) = inner ℝ z.fst v := by
  change inner ℝ z.fst v + inner ℝ z.snd (0 : F) = _
  simp


theorem inner_axisY (z : JointSpace E F) (v : F) :
    inner ℝ z (axisY v) = inner ℝ z.snd v := by
  change inner ℝ z.fst (0 : E) + inner ℝ z.snd v = _
  simp


theorem point_hasFDerivAt_x (x : E) (y : F) :
    HasFDerivAt (fun u : E => point u y)
      (axisX (E := E) (F := F)).toContinuousLinearMap x := by
  exact (axisX (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.add_const (axisY y)


theorem point_hasFDerivAt_y (x : E) (y : F) :
    HasFDerivAt (fun v : F => point x v)
      (axisY (E := E) (F := F)).toContinuousLinearMap y := by
  exact (axisY (E := E) (F := F)).toContinuousLinearMap.hasFDerivAt.const_add (axisX x)


theorem differentiable_x_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (y : F) :
    Differentiable ℝ (fun x : E => curry J x y) := by
  intro x
  exact (hJ (point x y)).comp x (point_hasFDerivAt_x x y).differentiableAt


theorem differentiable_y_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) :
    Differentiable ℝ (curry J x) := by
  intro y
  exact (hJ (point x y)).comp y (point_hasFDerivAt_y x y).differentiableAt


theorem gradient_x_slice_eq_projection
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) (y : F) :
    gradient (fun u : E => curry J u y) x = (gradient J (point x y)).fst := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hs := (hJ (point x y)).hasFDerivAt.comp x (point_hasFDerivAt_x x y)
  have hs' : HasFDerivAt (fun u : E => curry J u y)
      ((fderiv ℝ J (point x y)).comp (axisX (E := E) (F := F)).toContinuousLinearMap) x := by
    simpa only [Function.comp_def, curry] using hs
  rw [hs'.fderiv]
  change (fderiv ℝ J (point x y)) (axisX v) = _
  rw [← inner_gradient_left, inner_axisX]


theorem gradient_y_slice_eq_projection
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) (y : F) :
    gradient (curry J x) y = (gradient J (point x y)).snd := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have hs := (hJ (point x y)).hasFDerivAt.comp y (point_hasFDerivAt_y x y)
  have hs' : HasFDerivAt (curry J x)
      ((fderiv ℝ J (point x y)).comp (axisY (E := E) (F := F)).toContinuousLinearMap) y := by
    convert! hs using 1 <;> rfl
  rw [hs'.fderiv]
  change (fderiv ℝ J (point x y)) (axisY v) = _
  rw [← inner_gradient_left, inner_axisY]


theorem gradient_x_lipschitz_in_x
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖ := by
  rw [gradient_x_slice_eq_projection J hJ, gradient_x_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x' y)‖ := norm_fst_projection_sub _ _
    _ ≤ L * ‖point x y - point x' y‖ := hLip _ _
    _ = L * ‖x - x'‖ := by rw [norm_point_sub_same_y]


theorem gradient_x_lipschitz_in_y
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖ := by
  rw [gradient_x_slice_eq_projection J hJ, gradient_x_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x y')‖ := norm_fst_projection_sub _ _
    _ ≤ L * ‖point x y - point x y'‖ := hLip _ _
    _ = L * ‖y - y'‖ := by rw [norm_point_sub_same_x]


theorem gradient_y_lipschitz_in_x
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x x' : E) (y : F) :
    ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖ := by
  rw [gradient_y_slice_eq_projection J hJ, gradient_y_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x' y)‖ := norm_snd_projection_sub _ _
    _ ≤ L * ‖point x y - point x' y‖ := hLip _ _
    _ = L * ‖x - x'‖ := by rw [norm_point_sub_same_y]


theorem gradient_y_lipschitz_in_y
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (x : E) (y y' : F) :
    ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖ := by
  rw [gradient_y_slice_eq_projection J hJ, gradient_y_slice_eq_projection J hJ]
  calc
    _ ≤ ‖gradient J (point x y) - gradient J (point x y')‖ := norm_snd_projection_sub _ _
    _ ≤ L * ‖point x y - point x y'‖ := hLip _ _
    _ = L * ‖y - y'‖ := by rw [norm_point_sub_same_x]


theorem contDiff2_x_slice
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (y : F) :
    ContDiff ℝ 2 (fun x : E => curry J x y) := by
  have haxis : ContDiff ℝ 2 (fun u : E => axisX (F := F) u) :=
    (axisX (E := E) (F := F)).toContinuousLinearMap.contDiff
  have hp : ContDiff ℝ 2 (fun u : E => point u y) := haxis.add contDiff_const
  exact hJ.comp hp


theorem contDiff2_y_slice
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (x : E) :
    ContDiff ℝ 2 (curry J x) := by
  have haxis : ContDiff ℝ 2 (fun v : F => axisY (E := E) v) :=
    (axisY (E := E) (F := F)).toContinuousLinearMap.contDiff
  have hp : ContDiff ℝ 2 (fun v : F => point x v) := contDiff_const.add haxis
  exact hJ.comp hp


theorem strongConvex_negative_y_slice
    (J : JointSpace E F → ℝ) (μ : ℝ)
    (hconcave : ∀ x : E, StrongConcaveOn (Set.univ : Set F) μ (curry J x)) (x : E) :
    StrongConvexOn (Set.univ : Set F) μ (fun y => - curry J x y) := by
  exact UniformConcaveOn.neg (hconcave x)


theorem differentiable_joint_of_contDiff2
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) : Differentiable ℝ J := by
  exact hJ.differentiable (by norm_num)


theorem differentiable_negative_y_slice
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (x : E) :
    Differentiable ℝ (fun y : F => - curry J x y) := by
  exact (differentiable_y_slice J hJ x).neg


theorem joint_to_slice_conditions
    (J : JointSpace E F → ℝ) (hJ : Differentiable ℝ J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    (∀ y : F, Differentiable ℝ (fun x : E => curry J x y)) ∧
    (∀ x : E, Differentiable ℝ (curry J x)) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖) := by
  exact ⟨differentiable_x_slice J hJ, differentiable_y_slice J hJ,
    gradient_x_lipschitz_in_x J hJ L hLip, gradient_x_lipschitz_in_y J hJ L hLip,
    gradient_y_lipschitz_in_x J hJ L hLip, gradient_y_lipschitz_in_y J hJ L hLip⟩


theorem contDiff2_joint_to_slice_conditions
    (J : JointSpace E F → ℝ) (hJ : ContDiff ℝ 2 J) (L : ℝ)
    (hLip : ∀ z w : JointSpace E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖) :
    (∀ y : F, Differentiable ℝ (fun x : E => curry J x y)) ∧
    (∀ x : E, Differentiable ℝ (curry J x)) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y) x'‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (fun u => curry J u y) x - gradient (fun u => curry J u y') x‖ ≤ L * ‖y - y'‖) ∧
    (∀ (x x' : E) (y : F),
      ‖gradient (curry J x) y - gradient (curry J x') y‖ ≤ L * ‖x - x'‖) ∧
    (∀ (x : E) (y y' : F),
      ‖gradient (curry J x) y - gradient (curry J x) y'‖ ≤ L * ‖y - y'‖) := by
  exact joint_to_slice_conditions J (differentiable_joint_of_contDiff2 J hJ) L hLip

end JointSliceRegularity
end

section
-- Source component: RelayValueBridge.lean

namespace FangqingRelayValueBridge

open FangqingRelayStationarity

noncomputable section

abbrev Dual (n : ℕ) (E : Type*) := PiLp 2 (fun _ : Fin 2 × Fin (n + 1) => E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def curryF (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (X : Blocks n E) (Z : Dual n E) : ℝ :=
  family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp (fun t => Z (0, t)) (fun t => Z (1, t))

def jointF (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (W : JointSliceRegularity.JointSpace (Blocks n E) (Dual n E)) : ℝ :=
  curryF n β lam a sigma reward h0 h1 m0 m1 gate W.fst W.snd

def packDual (n : ℕ) (y s : Fin (n + 1) → E) : Dual n E :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin (n + 1) => if p.1 = 0 then y p.2 else s p.2)

theorem curry_jointF (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (X : Blocks n E) (Z : Dual n E) :
    JointSliceRegularity.curry (jointF n β lam a sigma reward h0 h1 m0 m1 gate) X Z =
      curryF n β lam a sigma reward h0 h1 m0 m1 gate X Z := by
  unfold JointSliceRegularity.curry
  rw [JointSliceRegularity.point_eq_toLp]
  rfl

/- Starting from actual joint-class hypotheses for the full relay,
   derive both of the interfaces missing from the earlier conditional
   stationarity proof.  Neither maximizing selections nor differentiable
   value functions are assumed. -/
theorem actual_joint_class_supplies_value_interfaces [FiniteDimensional ℝ E]
    (n : ℕ) (β lam a sigma reward L mu : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (hJ : ContDiff ℝ 2 (jointF n β lam a sigma reward h0 h1 m0 m1 gate))
    (hLip : ∀ z w : JointSliceRegularity.JointSpace (Blocks n E) (Dual n E),
      ‖gradient (jointF n β lam a sigma reward h0 h1 m0 m1 gate) z -
        gradient (jointF n β lam a sigma reward h0 h1 m0 m1 gate) w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ X : Blocks n E, StrongConvexOn (Set.univ : Set (Dual n E)) mu
      (fun Z => -curryF n β lam a sigma reward h0 h1 m0 m1 gate X Z)) :
    ∃ Y S : Blocks n E → (Fin (n + 1) → E),
      (∀ (X : Blocks n E) (yy ss : Fin (n + 1) → E),
        family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
          family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp (Y X) (S X)) ∧
      Differentiable ℝ (exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S) := by
  let f := JointSliceRegularity.curry (jointF n β lam a sigma reward h0 h1 m0 m1 gate)
  have hcond := JointSliceRegularity.contDiff2_joint_to_slice_conditions
    (jointF n β lam a sigma reward h0 h1 m0 m1 gate) hJ L hLip
  have heq : f = curryF n β lam a sigma reward h0 h1 m0 m1 gate := by
    funext X Z
    exact curry_jointF n β lam a sigma reward h0 h1 m0 m1 gate X Z
  have hs : ∀ X : Blocks n E, StrongConvexOn (Set.univ : Set (Dual n E)) mu (fun Z => -f X Z) := by
    rw [heq]
    exact hsc
  have hex : ∀ X : Blocks n E, ∃ Z : Dual n E, ∀ W : Dual n E, f X W ≤ f X Z := by
    intro X
    exact OriginalSaddleRegularity.exists_inner_maximum f mu hmu hs hcond.2.1 X
  choose Z hZ using hex
  let Y : Blocks n E → (Fin (n + 1) → E) := fun X t => Z X (0, t)
  let S : Blocks n E → (Fin (n + 1) → E) := fun X t => Z X (1, t)
  have hmax : ∀ (X : Blocks n E) (yy ss : Fin (n + 1) → E),
      family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
        family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp (Y X) (S X) := by
    intro X yy ss
    have hh := hZ X (packDual n yy ss)
    rw [heq] at hh
    simpa only [curryF, packDual, PiLp.toLp_apply, if_pos rfl, show (1 : Fin 2) ≠ 0 by decide,
      if_false, ite_true, ite_false, Y, S] using hh
  have hxx : ∀ (W : Dual n E) (X V : Blocks n E),
      ‖gradient (fun T => f T W) X - gradient (fun T => f T W) V‖ ≤ L * ‖X - V‖ :=
    fun W X V => hcond.2.2.1 X V W
  have hxy : ∀ (X : Blocks n E) (U V : Dual n E),
      ‖gradient (fun T => f T U) X - gradient (fun T => f T V) X‖ ≤ L * ‖U - V‖ :=
    hcond.2.2.2.1
  have hdiff : Differentiable ℝ (OriginalSaddleRegularity.value f Z) := by
    intro X
    exact (OriginalSaddleRegularity.value_hasGradientAt f L mu hL hmu hcond.1 hcond.2.1 hs
      hxx hxy Z hZ X).differentiableAt
  have hvalue : exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S =
      OriginalSaddleRegularity.value f Z := by
    funext X
    rw [OriginalSaddleRegularity.value, heq]
    rfl
  refine ⟨Y, S, hmax, ?_⟩
  rw [hvalue]
  exact hdiff


theorem exactValue_eq_actual_sSup (n : ℕ) (β lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (Y S : Blocks n E → (Fin (n + 1) → E))
    (hmax : ∀ (X : Blocks n E) (yy ss : Fin (n + 1) → E),
      family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
        family n β lam a sigma reward h0 h1 m0 m1 gate X.ofLp (Y X) (S X)) (X : Blocks n E) :
    exactValue n β lam a sigma reward h0 h1 m0 m1 gate Y S X =
      sSup (Set.range (curryF n β lam a sigma reward h0 h1 m0 m1 gate X)) := by
  symm
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨packDual n (Y X) (S X), ?_⟩
    simp [curryF, packDual, exactValue]
  · intro v hv
    rcases hv with ⟨Z, rfl⟩
    exact hmax X (fun t => Z (0, t)) (fun t => Z (1, t))

end
end FangqingRelayValueBridge
end

section
-- Source component: RelayValueJointClass.lean

open scoped ContDiff

namespace FangqingRelayValueJointClass

open FangqingRelayJointClassTransport FangqingRelayAnalyticAssembly FangqingRelayStationarity

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem productFamily_eq_value_joint (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ) :
    productFamily n beta lam a sigma reward h0 h1 m0 m1 gate =
      FangqingRelayValueBridge.jointF n beta lam a sigma reward h0 h1 m0 m1 gate := rfl

theorem actual_flat_class_gives_value_layout (n : ℕ) (beta lam a sigma reward L rho : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (hL : 0 ≤ L) (hrho : 0 ≤ rho)
    (hJ : ContDiff ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate))
    (h2 : ∀ z, ‖iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) z‖ ≤ L)
    (hLip : ∀ x y, ‖iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) x -
      iteratedFDeriv ℝ 2 (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) y‖ ≤ rho * ‖x - y‖) :
    let F := FangqingRelayValueBridge.jointF n beta lam a sigma reward h0 h1 m0 m1 gate
    ContDiff ℝ 2 F ∧
    (∀ x y, ‖gradient F x - gradient F y‖ ≤ L * ‖x - y‖) ∧
    FangqingFenchelEndpointClass.HessianRate F rho := by
  intro F
  have hh := actual_product_joint_class n beta lam a sigma reward L rho h0 h1 m0 m1 gate hL hrho hJ h2 hLip
  simpa only [productFamily_eq_value_joint] using! hh

end
end FangqingRelayValueJointClass
end

section
-- Source component: LateGateLeakageKernel.lean

namespace FangqingLateGateLeakageKernel

open FangqingRelayStationarity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem three_direction_residual_norm
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (r alpha beta : ℝ) :
    ‖r • v 0 - alpha • v 1 - beta • v 2‖ ^ 2 = r ^ 2 + alpha ^ 2 + beta ^ 2 := by
  calc
    _ = inner ℝ (r • v 0 - alpha • v 1 - beta • v 2)
        (r • v 0 - alpha • v 1 - beta • v 2) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = _ := by
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, orthonormal_iff_ite.mp hv]
      norm_num [Fin.ext_iff]
      ring

theorem known_query_radial_argument
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (p : E)
    (a ell r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell)
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0) :
    ‖a • (p + r • v 0) - a • (p + alpha • v 1 + beta • v 2)‖ ^ 2 / (a ^ 2 * ell ^ 2) = t0 := by
  have he : a • (p + r • v 0) - a • (p + alpha • v 1 + beta • v 2) =
      a • (r • v 0 - alpha • v 1 - beta • v 2) := by module
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_pow,
    three_direction_residual_norm v hv r alpha beta, hsphere]
  field_simp [ne_of_gt ha, ne_of_gt hell]

theorem known_query_gate_gradient
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (p : E)
    (a ell r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell)
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0) :
    gradient (radialGate theta a ell (p + alpha • v 1 + beta • v 2)) (a • (p + r • v 0)) =
      (2 * deriv theta t0 / (a ^ 2 * ell ^ 2)) •
        (a • (p + r • v 0) - a • (p + alpha • v 1 + beta • v 2)) := by
  have hg := (radialGate_hasGradientAt theta a ell (p + alpha • v 1 + beta • v 2)
    (a • (p + r • v 0)) htheta).gradient
  have harg := known_query_radial_argument v hv p a ell r alpha beta t0 ha hell hsphere
  simpa only [eta, harg, neg_div, neg_neg] using hg

theorem unrevealed_orientation_changes_true_gate_gradient
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (p : E)
    (a ell r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell) (hbeta : beta ≠ 0)
    (hderiv : deriv theta t0 ≠ 0)
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0) :
    gradient (radialGate theta a ell (p + alpha • v 1 + beta • v 2)) (a • (p + r • v 0)) ≠
      gradient (radialGate theta a ell (p + alpha • v 1 + (-beta) • v 2)) (a • (p + r • v 0)) := by
  let C := 2 * deriv theta t0 / (a ^ 2 * ell ^ 2)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hderiv)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (pow_ne_zero 2 (ne_of_gt hell)))
  have hg0 := known_query_gate_gradient theta htheta v hv p a ell r alpha beta t0 ha hell hsphere
  have hg1 := known_query_gate_gradient theta htheta v hv p a ell r alpha (-beta) t0 ha hell
    (by simpa only [neg_sq] using hsphere)
  have hdiff : gradient (radialGate theta a ell (p + alpha • v 1 + beta • v 2)) (a • (p + r • v 0)) -
      gradient (radialGate theta a ell (p + alpha • v 1 + (-beta) • v 2)) (a • (p + r • v 0)) =
        (-2 * a * beta * C) • v 2 := by
    rw [hg0, hg1]
    change C • (a • (p + r • v 0) - a • (p + alpha • v 1 + beta • v 2)) -
      C • (a • (p + r • v 0) - a • (p + alpha • v 1 + (-beta) • v 2)) = _
    module
  have hv2 : v 2 ≠ 0 := by
    intro hz
    have hn := hv.norm_eq_one (2 : Fin 3)
    rw [hz, norm_zero] at hn
    norm_num at hn
  have hcoef : -2 * a * beta * C ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt ha)) hbeta) hC
  intro heq
  have hz := sub_eq_zero.mpr heq
  rw [hdiff] at hz
  exact smul_ne_zero hcoef hv2 hz

theorem recover_second_tail_from_actual_gate_gradient
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (v : Fin 3 → E) (hv : Orthonormal ℝ v) (p : E)
    (a ell r alpha beta t0 : ℝ) (ha : 0 < a) (hell : 0 < ell) (hbeta : beta ≠ 0)
    (hderiv : deriv theta t0 ≠ 0)
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0) :
    v 2 = beta⁻¹ • (a⁻¹ • (a • (p + r • v 0) -
      (2 * deriv theta t0 / (a ^ 2 * ell ^ 2))⁻¹ •
        gradient (radialGate theta a ell (p + alpha • v 1 + beta • v 2)) (a • (p + r • v 0))) -
      p - alpha • v 1) := by
  let C := 2 * deriv theta t0 / (a ^ 2 * ell ^ 2)
  have hC : C ≠ 0 := div_ne_zero (mul_ne_zero (by norm_num) hderiv)
    (mul_ne_zero (pow_ne_zero 2 (ne_of_gt ha)) (pow_ne_zero 2 (ne_of_gt hell)))
  have hg := known_query_gate_gradient theta htheta v hv p a ell r alpha beta t0 ha hell hsphere
  change v 2 = beta⁻¹ • (a⁻¹ • (a • (p + r • v 0) - C⁻¹ •
    gradient (radialGate theta a ell (p + alpha • v 1 + beta • v 2)) (a • (p + r • v 0))) - p - alpha • v 1)
  rw [hg, smul_smul, inv_mul_cancel₀ hC, one_smul]
  have hc : a • (p + r • v 0) - (a • (p + r • v 0) - a • (p + alpha • v 1 + beta • v 2)) =
      a • (p + alpha • v 1 + beta • v 2) := by module
  rw [hc, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]
  have ht : p + alpha • v 1 + beta • v 2 - p - alpha • v 1 = beta • v 2 := by module
  rw [ht, smul_smul, inv_mul_cancel₀ hbeta, one_smul]

end FangqingLateGateLeakageKernel
end

section
-- Source component: LateGateRelaySlice.lean

namespace FangqingLateGateRelaySlice

open FangqingRelayStationarity FangqingLateGateLeakageKernel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem family_s_update (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (z : E) :
    family n bet lam a sigma reward h0 h1 m0 m1 gate x y (Function.update s i z) =
      family n bet lam a sigma reward h0 h1 m0 m1 gate x y s +
      coefficient n reward h0 h1 m0 m1 y i *
        (gateExt n gate i z - gateExt n gate i (s i)) -
      sigma / 2 * (‖z - a • x i‖ ^ 2 - ‖s i - a • x i‖ ^ 2) := by
  have hh := family_s_vary n bet lam a sigma reward h0 h1 m0 m1 gate x y s i (z - s i) 1
  have he : s i + (1 : ℝ) • (z - s i) = z := by module
  simpa only [vary, he] using hh

theorem actual_relay_s_slice_hasGradientAt
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (p : E) (hp : HasGradientAt (gateExt n gate i) p (s i)) :
    HasGradientAt
      (fun z => family n bet lam a sigma reward h0 h1 m0 m1 gate x y (Function.update s i z))
      (coefficient n reward h0 h1 m0 m1 y i • p - sigma • (s i - a • x i)) (s i) := by
  have hg := ((hp.hasFDerivAt.sub_const (gateExt n gate i (s i))).const_mul
    (coefficient n reward h0 h1 m0 m1 y i)).const_add
      (family n bet lam a sigma reward h0 h1 m0 m1 gate x y s)
  have hn := ((((hasFDerivAt_id (s i)).sub_const (a • x i)).norm_sq).sub_const
    (‖s i - a • x i‖ ^ 2)).const_mul (sigma / 2)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert! hg.sub hn using 1
  · funext z
    exact family_s_update n bet lam a sigma reward h0 h1 m0 m1 gate x y s i z
  · ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply_apply,
      InnerProductSpace.toDual_apply_apply, real_inner_smul_left, inner_sub_left, smul_eq_mul,
      id_eq]
    ring

theorem actual_relay_s_slice_gradient
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (i : Fin (n + 1)) (p : E) (hp : HasGradientAt (gateExt n gate i) p (s i)) :
    gradient (fun z => family n bet lam a sigma reward h0 h1 m0 m1 gate x y
      (Function.update s i z)) (s i) =
      coefficient n reward h0 h1 m0 m1 y i • p - sigma • (s i - a • x i) :=
  (actual_relay_s_slice_hasGradientAt n bet lam a sigma reward h0 h1 m0 m1 gate x y s i p hp).gradient

theorem actual_relay_recovers_private_center
    (n : ℕ) (bet lam a sigma reward ell : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (star : Fin n → E) (x y s : Fin (n + 1) → E) (i : Fin n)
    (ha : a ≠ 0)
    (hcoef : coefficient n reward h0 h1 m0 m1 y i.castSucc ≠ 0)
    (heta : eta theta a ell (star i) (s i.castSucc) ≠ 0) :
    star i = a⁻¹ • (s i.castSucc +
      (coefficient n reward h0 h1 m0 m1 y i.castSucc *
        eta theta a ell (star i) (s i.castSucc))⁻¹ •
        (gradient (fun z => family n bet lam a sigma reward h0 h1 m0 m1
          (fun j => radialGate theta a ell (star j)) x y (Function.update s i.castSucc z))
            (s i.castSucc) + sigma • (s i.castSucc - a • x i.castSucc))) := by
  have hgrad : HasGradientAt
      (gateExt n (fun j => radialGate theta a ell (star j)) i.castSucc)
      (-eta theta a ell (star i) (s i.castSucc) • (s i.castSucc - a • star i))
        (s i.castSucc) := by
    simpa only [gateExt, Fin.lastCases_castSucc] using
      radialGate_hasGradientAt theta a ell (star i) (s i.castSucc) htheta
  rw [actual_relay_s_slice_gradient n bet lam a sigma reward h0 h1 m0 m1
    (fun j => radialGate theta a ell (star j)) x y s i.castSucc _ hgrad]
  have hcancel :
      coefficient n reward h0 h1 m0 m1 y i.castSucc •
        (-eta theta a ell (star i) (s i.castSucc) • (s i.castSucc - a • star i)) -
        sigma • (s i.castSucc - a • x i.castSucc) +
        sigma • (s i.castSucc - a • x i.castSucc) =
      -(coefficient n reward h0 h1 m0 m1 y i.castSucc *
        eta theta a ell (star i) (s i.castSucc)) • (s i.castSucc - a • star i) := by module
  rw [hcancel, smul_smul, mul_neg, inv_mul_cancel₀ (mul_ne_zero hcoef heta), neg_one_smul]
  have he : s i.castSucc - (s i.castSucc - a • star i) = a • star i := by module
  rw [← sub_eq_add_neg, he, smul_smul, inv_mul_cancel₀ ha, one_smul]

section BundledProjection

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def coordinateIsometry (i : I) : E →ₗᵢ[ℝ] PiLp 2 (fun _ : I => E) where
  toFun v := PiLp.single 2 i v
  map_add' v w := PiLp.single_add 2 i
  map_smul' c v := by
    ext j
    by_cases hj : j = i <;> simp [PiLp.single_apply, hj]
  norm_map' v := PiLp.norm_single 2 (fun _ : I => E) i v

theorem coordinate_inner (G : PiLp 2 (fun _ : I => E)) (i : I) (v : E) :
    inner ℝ G (coordinateIsometry i v) = inner ℝ (G i) v := by
  classical
  simp [coordinateIsometry, PiLp.inner_apply, PiLp.single_apply, apply_ite]

theorem actual_bundle_coordinate_slice_gradient
    (G : PiLp 2 (fun _ : I => E) → ℝ) (hG : Differentiable ℝ G)
    (Z : PiLp 2 (fun _ : I => E)) (i : I) :
    gradient (fun z : E => G (WithLp.toLp 2 (Function.update Z i z))) (Z i) =
      gradient G Z i := by
  let C := coordinateIsometry (E := E) i
  have he : (fun z : E => WithLp.toLp 2 (Function.update Z i z)) =
      (fun z : E => Z + C (z - Z i)) := by
    funext z
    ext j
    by_cases hj : j = i
    · subst j
      simp [C, coordinateIsometry, PiLp.single_apply]
    · simp [C, coordinateIsometry, PiLp.single_apply, Function.update_of_ne hj, hj]
  have hc := C.toContinuousLinearMap.hasFDerivAt.comp (Z i)
    ((hasFDerivAt_id (Z i)).sub_const (Z i))
  have hc' : HasFDerivAt (fun z : E => Z + C (z - Z i)) C.toContinuousLinearMap (Z i) := by
    convert! hc.const_add Z using 1 <;>
      simp only [Function.comp_def, ContinuousLinearMap.comp_id, id_eq]
  have hz : Z + C (Z i - Z i) = Z := by simp
  have hGz : DifferentiableAt ℝ G (Z + C (Z i - Z i)) := by simpa only [hz] using hG Z
  have hh := hGz.hasFDerivAt.comp (Z i) hc'
  have hs : HasFDerivAt (fun z : E => G (WithLp.toLp 2 (Function.update Z i z)))
      ((fderiv ℝ G Z).comp C.toContinuousLinearMap) (Z i) := by
    have hfun : (fun z : E => G (WithLp.toLp 2 (Function.update Z i z))) =
        (fun z : E => G (Z + C (z - Z i))) := by
      funext z
      exact congrArg G (congrFun he z)
    rw [hfun]
    convert! hh using 1 <;> simp only [hz, Function.comp_def]
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left, hs.fderiv]
  change (fderiv ℝ G Z) (C v) = inner ℝ (gradient G Z i) v
  rw [← inner_gradient_left]
  exact coordinate_inner (gradient G Z) i v

end BundledProjection

end FangqingLateGateRelaySlice
end

section
-- Source component: LateGateBundledOracle.lean

namespace FangqingLateGateBundledOracle

open FangqingRelayStationarity FangqingRelayValueBridge FangqingLateGateRelaySlice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem packDual_update_s (n : ℕ) (y s : Fin (n + 1) → E) (i : Fin (n + 1)) (z : E) :
    packDual n y (Function.update s i z) =
      WithLp.toLp 2 (Function.update (packDual n y s) (1, i) z) := by
  ext k
  rcases k with ⟨r, j⟩
  fin_cases r <;> by_cases hj : j = i <;>
    simp [packDual, Function.update_apply, hj]

theorem full_joint_gradient_s_coordinate
    (n : ℕ) (bet lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ)
    (hJ : Differentiable ℝ (jointF n bet lam a sigma reward h0 h1 m0 m1 gate))
    (X : Blocks n E) (y s : Fin (n + 1) → E) (i : Fin (n + 1)) :
    gradient (fun z => family n bet lam a sigma reward h0 h1 m0 m1 gate
      X.ofLp y (Function.update s i z)) (s i) =
    (gradient (jointF n bet lam a sigma reward h0 h1 m0 m1 gate)
      (JointSliceRegularity.point X (packDual n y s))).snd (1, i) := by
  let J := jointF n bet lam a sigma reward h0 h1 m0 m1 gate
  have he : (fun z : E => JointSliceRegularity.curry J X
      (WithLp.toLp 2 (Function.update (packDual n y s) (1, i) z))) =
      (fun z : E => family n bet lam a sigma reward h0 h1 m0 m1 gate
        X.ofLp y (Function.update s i z)) := by
    funext z
    rw [← packDual_update_s]
    rw [show J = jointF n bet lam a sigma reward h0 h1 m0 m1 gate from rfl,
      curry_jointF]
    simp [curryF, packDual]
  have hp := actual_bundle_coordinate_slice_gradient
    (JointSliceRegularity.curry J X)
    (JointSliceRegularity.differentiable_y_slice J hJ X) (packDual n y s) (1, i)
  rw [he, JointSliceRegularity.gradient_y_slice_eq_projection J hJ X (packDual n y s)] at hp
  simpa only [packDual, PiLp.toLp_apply, show (1 : Fin 2) ≠ 0 by decide, if_false] using hp

theorem actual_full_gradient_recovers_private_center
    (n : ℕ) (bet lam a sigma reward ell : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (star : Fin n → E)
    (hJ : Differentiable ℝ (jointF n bet lam a sigma reward h0 h1 m0 m1
      (fun j => radialGate theta a ell (star j))))
    (X : Blocks n E) (y s : Fin (n + 1) → E) (i : Fin n)
    (ha : a ≠ 0)
    (hcoef : coefficient n reward h0 h1 m0 m1 y i.castSucc ≠ 0)
    (heta : eta theta a ell (star i) (s i.castSucc) ≠ 0) :
    star i = a⁻¹ • (s i.castSucc +
      (coefficient n reward h0 h1 m0 m1 y i.castSucc *
        eta theta a ell (star i) (s i.castSucc))⁻¹ •
        ((gradient (jointF n bet lam a sigma reward h0 h1 m0 m1
          (fun j => radialGate theta a ell (star j)))
            (JointSliceRegularity.point X (packDual n y s))).snd (1, i.castSucc) +
              sigma • (s i.castSucc - a • X i.castSucc))) := by
  have hh := actual_relay_recovers_private_center n bet lam a sigma reward ell h0 h1 m0 m1
    theta htheta star X.ofLp y s i ha hcoef heta
  rw [full_joint_gradient_s_coordinate n bet lam a sigma reward h0 h1 m0 m1
    (fun j => radialGate theta a ell (star j)) hJ X y s i.castSucc] at hh
  exact hh

end FangqingLateGateBundledOracle
end

section
-- Source component: GaussianSphereAux.lean

/- Actual Gaussian calculations for a future spherical-cap proof.
No Haar-frame or conditional residual-law theorem is imported as an axiom. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace FangqingGaussianSphere

theorem gaussian_square_laplace_integrable (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : ℝ => Real.exp (-a * x ^ 2 / 2)) (gaussianReal 0 1) := by
  apply (integrable_const (1 : ℝ)).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg x]

theorem gaussian_square_laplace (a : ℝ) (ha : 0 ≤ a) :
    ∫ x : ℝ, Real.exp (-a * x ^ 2 / 2) ∂gaussianReal 0 1 =
      (Real.sqrt (1 + a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have heq : (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (-a * x ^ 2 / 2)) =
      (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-((1 + a) / 2) * x ^ 2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq, integral_const_mul, integral_gaussian]
  have harg : Real.pi / ((1 + a) / 2) = (2 * Real.pi) / (1 + a) := by field_simp
  rw [harg, Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi) (1 + a)]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

theorem standard_gaussian_subgaussian :
    HasSubgaussianMGF (fun x : ℝ => x) 1 (gaussianReal 0 1) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by simp [mgf_fun_id_gaussianReal]

theorem standard_gaussian_abs_tail (t : ℝ) (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x : ℝ | t ≤ |x|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  have hpos := standard_gaussian_subgaussian.measure_ge_le ht
  have hneg := standard_gaussian_subgaussian.neg.measure_ge_le ht
  have hpos' : (gaussianReal 0 1).real {x : ℝ | t ≤ x} ≤ Real.exp (-t ^ 2 / 2) := by
    simpa using hpos
  have hneg' : (gaussianReal 0 1).real {x : ℝ | t ≤ -x} ≤ Real.exp (-t ^ 2 / 2) := by
    simpa using hneg
  have heq : {x : ℝ | t ≤ |x|} = {x : ℝ | t ≤ x} ∪ {x : ℝ | t ≤ -x} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro h
      by_cases hx : 0 ≤ x
      · exact Or.inl (by simpa only [abs_of_nonneg hx] using h)
      · exact Or.inr (by simpa only [abs_of_neg (lt_of_not_ge hx)] using h)
    · rintro (h | h)
      · exact le_trans h (le_abs_self _)
      · exact le_trans h (neg_le_abs _)
  rw [heq]
  exact (measureReal_union_le _ _).trans (by linarith)

theorem gaussian_square_sum_laplace (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ∫ x : Fin n → ℝ, Real.exp (-a * (∑ i, (x i) ^ 2) / 2)
      ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      ((Real.sqrt (1 + a))⁻¹) ^ n := by
  have heq : (fun x : Fin n → ℝ => Real.exp (-a * (∑ i, (x i) ^ 2) / 2)) =
      (fun x : Fin n → ℝ => ∏ i, Real.exp (-a * (x i) ^ 2 / 2)) := by
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div, Finset.mul_sum]
  rw [heq]
  calc
    _ = (∫ x : ℝ, Real.exp (-a * x ^ 2 / 2) ∂gaussianReal 0 1) ^ n := by
      simpa only [Fintype.card_fin] using!
        (integral_fintype_prod_eq_pow (ι := Fin n) (μ := gaussianReal 0 1)
          (fun x : ℝ => Real.exp (-a * x ^ 2 / 2)))
    _ = _ := congrArg (fun x : ℝ => x ^ n) (gaussian_square_laplace a ha)

theorem gaussian_square_sum_laplace_integrable (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    Integrable (fun x : Fin n → ℝ => Real.exp (-a * (∑ i, (x i) ^ 2) / 2))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hc : Continuous (fun x : Fin n → ℝ => Real.exp (-a * (∑ i, (x i) ^ 2) / 2)) := by
    fun_prop
  apply (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_one_iff.mpr
  have hs : 0 ≤ ∑ i : Fin n, (x i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

theorem cone_section_subset (u S : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hS : 0 ≤ S) :
    {x : ℝ | u * Real.sqrt (x ^ 2 + S) < |x|} ⊆
      {x : ℝ | Real.sqrt (u ^ 2 / (1 - u ^ 2) * S) ≤ |x|} := by
  intro x hx
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  apply (Real.sqrt_le_left (abs_nonneg x)).mpr
  rw [sq_abs]
  have hsq := mul_self_le_mul_self
    (mul_nonneg hu (Real.sqrt_nonneg _)) hx.le
  rw [← sq, mul_pow, Real.sq_sqrt (by nlinarith : 0 ≤ x ^ 2 + S), ← sq, sq_abs] at hsq
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith

theorem gaussian_cone_section (u S : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) (hS : 0 ≤ S) :
    (gaussianReal 0 1).real {x : ℝ | u * Real.sqrt (x ^ 2 + S) < |x|} ≤
      2 * Real.exp (-(u ^ 2 / (1 - u ^ 2) * S) / 2) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have ha : 0 ≤ u ^ 2 / (1 - u ^ 2) * S := by positivity
  have hbound := standard_gaussian_abs_tail (Real.sqrt (u ^ 2 / (1 - u ^ 2) * S))
    (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt ha] at hbound
  exact (measureReal_mono (cone_section_subset u S hu hu1 hS)).trans hbound

theorem gaussian_product_cone_bound (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)).real
      {p : (Fin n → ℝ) × ℝ | u * Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) < |p.2|} ≤
      2 * ((Real.sqrt (1 + u ^ 2 / (1 - u ^ 2)))⁻¹) ^ n := by
  let ν := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let A : Set ((Fin n → ℝ) × ℝ) :=
    {p | u * Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) < |p.2|}
  let a := u ^ 2 / (1 - u ^ 2)
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have ha : 0 ≤ a := by positivity
  have hA : MeasurableSet A := by
    apply measurableSet_lt <;> fun_prop
  have hp : Integrable (A.indicator (fun _ => (1 : ℝ))) (ν.prod (gaussianReal 0 1)) :=
    (integrable_const (1 : ℝ)).indicator hA
  have hslice (y : Fin n → ℝ) :
      (∫ x : ℝ, A.indicator (fun _ => (1 : ℝ)) (y, x) ∂gaussianReal 0 1) =
        (gaussianReal 0 1).real {x : ℝ | u * Real.sqrt (x ^ 2 + ∑ i, (y i) ^ 2) < |x|} := by
    have hs : MeasurableSet {x : ℝ | u * Real.sqrt (x ^ 2 + ∑ i, (y i) ^ 2) < |x|} := by
      apply measurableSet_lt <;> fun_prop
    simpa only [A, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := gaussianReal 0 1) (1 : ℝ) hs)
  calc
    (ν.prod (gaussianReal 0 1)).real A =
        ∫ p, A.indicator (fun _ => (1 : ℝ)) p ∂(ν.prod (gaussianReal 0 1)) := by
      simpa only [smul_eq_mul, mul_one] using
        (integral_indicator_const (μ := ν.prod (gaussianReal 0 1)) (1 : ℝ) hA).symm
    _ = ∫ y, ∫ x : ℝ, A.indicator (fun _ => (1 : ℝ)) (y, x)
        ∂gaussianReal 0 1 ∂ν := integral_prod _ hp
    _ ≤ ∫ y : Fin n → ℝ, 2 * Real.exp (-a * (∑ i, (y i) ^ 2) / 2) ∂ν := by
      apply integral_mono_ae hp.integral_prod_left
        ((gaussian_square_sum_laplace_integrable n a ha).const_mul 2)
      filter_upwards [] with y
      rw [hslice y]
      simpa only [a, neg_mul] using!
        gaussian_cone_section u (∑ i, (y i) ^ 2) hu hu1
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = 2 * ((Real.sqrt (1 + a))⁻¹) ^ n := by
      rw [integral_const_mul, gaussian_square_sum_laplace n a ha]

theorem gaussian_product_cone_exp_bound (n : ℕ) (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) :
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)).real
      {p : (Fin n → ℝ) × ℝ | u * Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) < |p.2|} ≤
      2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  have hden : 0 < 1 - u ^ 2 := by nlinarith
  have harg : 1 + u ^ 2 / (1 - u ^ 2) = (1 - u ^ 2)⁻¹ := by
    field_simp
    ring
  have he : (Real.exp (-u ^ 2 / 2)) ^ 2 = Real.exp (-u ^ 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hbase : Real.sqrt (1 - u ^ 2) ≤ Real.exp (-u ^ 2 / 2) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.exp_pos _).le).mp
    rw [Real.sq_sqrt hden.le, he]
    linarith only [Real.add_one_le_exp (-u ^ 2)]
  calc
    _ ≤ 2 * ((Real.sqrt (1 + u ^ 2 / (1 - u ^ 2)))⁻¹) ^ n :=
      gaussian_product_cone_bound n u hu hu1
    _ = 2 * (Real.sqrt (1 - u ^ 2)) ^ n := by
      rw [harg, Real.sqrt_inv, inv_inv]
    _ ≤ 2 * (Real.exp (-u ^ 2 / 2)) ^ n := by
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hbase n) (by norm_num)
    _ = 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 2
      ring

noncomputable def normalizedLast (n : ℕ) (p : (Fin n → ℝ) × ℝ) : ℝ :=
  p.2 / Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2)

theorem normalized_event_eq_cone (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    {p : (Fin n → ℝ) × ℝ | u < |normalizedLast n p|} =
      {p : (Fin n → ℝ) × ℝ | u * Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) < |p.2|} := by
  ext p
  simp only [Set.mem_setOf_eq, normalizedLast, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs : 0 ≤ ∑ i : Fin n, (p.1 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hnorm : Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) = 0
  · have hx : p.2 = 0 := by
      have hsq := Real.sq_sqrt (by nlinarith : 0 ≤ p.2 ^ 2 + ∑ i, (p.1 i) ^ 2)
      rw [hnorm] at hsq
      nlinarith [sq_nonneg p.2]
    rw [hnorm, hx]
    simp [not_lt.mpr hu]
  · exact lt_div_iff₀ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hnorm))

theorem cone_event_empty_of_one_le (n : ℕ) (u : ℝ) (hu : 1 ≤ u) :
    {p : (Fin n → ℝ) × ℝ | u * Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) < |p.2|} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hs : 0 ≤ ∑ i : Fin n, (p.1 i) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hnorm : |p.2| ≤ Real.sqrt (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (by nlinarith : 0 ≤ p.2 ^ 2 + ∑ i, (p.1 i) ^ 2)]
    linarith
  have hmul := mul_le_mul_of_nonneg_right hu
    (Real.sqrt_nonneg (p.2 ^ 2 + ∑ i, (p.1 i) ^ 2))
  exact (not_lt_of_ge (le_trans hnorm (by simpa only [one_mul] using hmul))) hp

theorem normalized_gaussian_last_tail (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)).real
      {p : (Fin n → ℝ) × ℝ | u < |normalizedLast n p|} ≤
      2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  rw [normalized_event_eq_cone n u hu]
  by_cases hsmall : u < 1
  · exact gaussian_product_cone_exp_bound n u hu hsmall
  · rw [cone_event_empty_of_one_le n u (le_of_not_gt hsmall), measureReal_empty]
    positivity

end FangqingGaussianSphere
end

section
-- Source component: GaussianDirectionLaw.lean

/- Actual normalization and orthogonal invariance of standard Gaussian law.
This file does not assume or certify identification with Haar Stiefel law. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingGaussianDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def normalize (x : E) : E := ‖x‖⁻¹ • x

theorem measurable_normalize : Measurable (normalize (E := E)) := by
  exact measurable_norm.inv.smul measurable_id

theorem normalize_isometry (f : E ≃ₗᵢ[ℝ] E) (x : E) :
    normalize (f x) = f (normalize x) := by
  simp only [normalize, f.norm_map, map_smul]

noncomputable def directionLaw : Measure E := (stdGaussian E).map normalize

instance directionLaw_probability : IsProbabilityMeasure (directionLaw (E := E)) :=
  Measure.isProbabilityMeasure_map measurable_normalize.aemeasurable

theorem directionLaw_isometry (f : E ≃ₗᵢ[ℝ] E) :
    (directionLaw (E := E)).map f = directionLaw := by
  unfold directionLaw
  rw [Measure.map_map f.continuous.measurable measurable_normalize]
  have hcomp : (f : E → E) ∘ normalize = normalize ∘ f := by
    funext x
    exact (normalize_isometry f x).symm
  rw [hcomp, ← Measure.map_map measurable_normalize f.continuous.measurable,
    stdGaussian_map f]

theorem stdGaussian_singleton_zero [Nontrivial E] : (stdGaussian E) {0} = 0 := by
  let i : Fin (Module.finrank ℝ E) := ⟨0, Module.finrank_pos⟩
  haveI : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  rw [stdGaussian, Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : E))]
  apply measure_mono_null (t := {x : Fin (Module.finrank ℝ E) → ℝ | x i = 0})
  · intro x hx
    have hx0 : (∑ j, x j • stdOrthonormalBasis ℝ E j) = 0 := hx
    have hinner := (stdOrthonormalBasis ℝ E).orthonormal.inner_right_fintype x i
    rw [hx0, inner_zero_right] at hinner
    exact hinner.symm
  · exact Measure.pi_hyperplane _ i 0

theorem stdGaussian_normalize_norm [Nontrivial E] :
    ∀ᵐ x ∂stdGaussian E, ‖normalize x‖ = 1 := by
  have hae : ∀ᵐ x ∂stdGaussian E, x ≠ 0 := by
    rw [ae_iff]
    simpa using stdGaussian_singleton_zero (E := E)
  filter_upwards [hae] with x hx
  simp [normalize, norm_smul, hx]

theorem directionLaw_unit_norm [Nontrivial E] :
    ∀ᵐ x ∂directionLaw (E := E), ‖x‖ = 1 := by
  rw [directionLaw, ae_map_iff measurable_normalize.aemeasurable
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  exact stdGaussian_normalize_norm

end FangqingGaussianDirection
end

section
-- Source component: InvariantOrbitLaw.lean

/- A genuine invariant-probability uniqueness lemma for transitive actions.
Instantiation on the sphere and on Stiefel fibers remains a separate task. -/

open MeasureTheory MeasureTheory.Measure Set Function
open scoped ENNReal

namespace FangqingInvariantOrbit

variable {G X : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
  [MeasurableSpace X] [MulAction G X] [MeasurableSMul₂ G X]

theorem invariant_probability_eq_orbit_of_support
    (haar : Measure G) [IsProbabilityMeasure haar] [IsMulRightInvariant haar]
    (ν : Measure X) [IsProbabilityMeasure ν] [SMulInvariantMeasure G X ν]
    (x₀ : X) (htrans : ∀ᵐ x ∂ν, ∃ g : G, g • x₀ = x) :
    ν = haar.map (fun g : G => g • x₀) := by
  ext A hA
  let f : X → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hfixed (g : G) : ∫⁻ x, f (g • x) ∂ν = ν A := by
    rw [(measurePreserving_smul g ν).lintegral_comp hf]
    simp [f, lintegral_indicator hA]
  have horbit : ∀ᵐ x ∂ν,
      (∫⁻ g : G, f (g • x) ∂haar) = ∫⁻ g : G, f (g • x₀) ∂haar := by
    filter_upwards [htrans] with x hx
    obtain ⟨h, rfl⟩ := hx
    simp_rw [← mul_smul]
    exact lintegral_mul_right_eq_self (fun g : G => f (g • x₀)) h
  have hmeas : Measurable (uncurry (fun g : G => fun x : X => f (g • x))) :=
    hf.comp measurable_smul
  calc
    ν A = ∫⁻ g : G, ∫⁻ x : X, f (g • x) ∂ν ∂haar := by
      simp_rw [hfixed]
      simp
    _ = ∫⁻ x : X, ∫⁻ g : G, f (g • x) ∂haar ∂ν :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ g : G, f (g • x₀) ∂haar := by
      calc
        _ = ∫⁻ _ : X, ∫⁻ g : G, f (g • x₀) ∂haar ∂ν := lintegral_congr_ae horbit
        _ = _ := by simp
    _ = (haar.map (fun g : G => g • x₀)) A := by
      rw [← lintegral_map hf (measurable_smul_const x₀)]
      simp [f, lintegral_indicator hA]

theorem invariant_probability_eq_orbit
    (haar : Measure G) [IsProbabilityMeasure haar] [IsMulRightInvariant haar]
    (ν : Measure X) [IsProbabilityMeasure ν] [SMulInvariantMeasure G X ν]
    (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) :
    ν = haar.map (fun g : G => g • x₀) :=
  invariant_probability_eq_orbit_of_support haar ν x₀ (Filter.Eventually.of_forall htrans)

theorem invariant_probability_unique
    (haar : Measure G) [IsProbabilityMeasure haar] [IsMulRightInvariant haar]
    (ν₁ ν₂ : Measure X) [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    [SMulInvariantMeasure G X ν₁] [SMulInvariantMeasure G X ν₂]
    (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) : ν₁ = ν₂ := by
  exact (invariant_probability_eq_orbit haar ν₁ x₀ htrans).trans
    (invariant_probability_eq_orbit haar ν₂ x₀ htrans).symm

end FangqingInvariantOrbit
end

section
-- Source component: OrthogonalHaarLaw.lean

/- Compiled after GaussianDirectionLaw and InvariantOrbitLaw.
The genuine compact orthogonal-group Haar probability is constructed here;
the original adaptive frame-conditional theorem is still a later interface. -/

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace Metric
open scoped NNReal ENNReal Topology

namespace FangqingOrthogonalHaar

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

abbrev Group := unitary (E →L[ℝ] E)

instance groupMeasurableSpace : MeasurableSpace (Group E) := borel _
instance groupBorelSpace : BorelSpace (Group E) := ⟨rfl⟩

instance groupCompactSpace : CompactSpace (Group E) := by
  apply isCompact_iff_compactSpace.mp
  apply isCompact_of_isClosed_isBounded isClosed_unitary
  apply (isBounded_closedBall : Bornology.IsBounded (closedBall (0 : E →L[ℝ] E) 1)).subset
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_coe_unitary (⟨u, hu⟩ : unitary (E →L[ℝ] E))).le

instance groupContinuousAction : ContinuousSMul (Group E) E where
  continuous_smul := (continuous_subtype_val.comp continuous_fst).clm_apply continuous_snd

instance groupMeasurableAction : MeasurableSMul₂ (Group E) E where
  measurable_smul := continuous_smul.measurable

noncomputable def groupUniv : PositiveCompacts (Group E) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

noncomputable def rightHaar : Measure (Group E) := (haarMeasure (groupUniv E)).inv

instance rightHaar_probability : IsProbabilityMeasure (rightHaar E) := by
  haveI : IsProbabilityMeasure (haarMeasure (groupUniv E)) := by
    constructor
    have hself := haarMeasure_self (K₀ := groupUniv E)
    change (haarMeasure (groupUniv E)) Set.univ = 1 at hself
    exact hself
  change IsProbabilityMeasure ((haarMeasure (groupUniv E)).map Inv.inv)
  exact Measure.isProbabilityMeasure_map continuous_inv.measurable.aemeasurable

instance rightHaar_rightInvariant : IsMulRightInvariant (rightHaar E) := by
  unfold rightHaar
  infer_instance

instance gaussianDirection_invariant :
    SMulInvariantMeasure (Group E) E (FangqingGaussianDirection.directionLaw (E := E)) where
  measure_preimage_smul u A hA := by
    have h := FangqingGaussianDirection.directionLaw_isometry (Unitary.linearIsometryEquiv u)
    have hAeq := congrArg (fun μ : Measure E => μ A) h
    rw [Measure.map_apply (Unitary.linearIsometryEquiv u).continuous.measurable hA] at hAeq
    exact hAeq

theorem unit_orbit (x₀ x : E) (hx₀ : ‖x₀‖ = 1) (hx : ‖x‖ = 1) :
    ∃ u : Group E, u • x₀ = x := by
  let f := (ℝ ∙ (x₀ - x))ᗮ.reflection
  refine ⟨Unitary.linearIsometryEquiv.symm f, ?_⟩
  exact Submodule.reflection_sub (hx₀.trans hx.symm)

theorem gaussianDirection_eq_haar_orbit (x₀ : E) (hx₀ : ‖x₀‖ = 1) :
    FangqingGaussianDirection.directionLaw (E := E) =
      (rightHaar E).map (fun u : Group E => u • x₀) := by
  letI : MeasurableSMul₂ (Group E) E := groupMeasurableAction E
  letI : SMulInvariantMeasure (Group E) E
      (FangqingGaussianDirection.directionLaw (E := E)) := gaussianDirection_invariant E
  refine @FangqingInvariantOrbit.invariant_probability_eq_orbit_of_support
    (Group E) E inferInstance (groupMeasurableSpace E) inferInstance
    ‹MeasurableSpace E› inferInstance (groupMeasurableAction E)
    (rightHaar E) (rightHaar_probability E) (rightHaar_rightInvariant E)
    (FangqingGaussianDirection.directionLaw (E := E)) inferInstance
    (gaussianDirection_invariant E) x₀ ?_
  filter_upwards [FangqingGaussianDirection.directionLaw_unit_norm (E := E)] with x hx
  exact unit_orbit E x₀ x hx₀ hx

theorem invariant_unit_law_unique (ν : Measure E) [IsProbabilityMeasure ν]
    [SMulInvariantMeasure (Group E) E ν] (hunit : ∀ᵐ x ∂ν, ‖x‖ = 1)
    (x₀ : E) (hx₀ : ‖x₀‖ = 1) :
    ν = FangqingGaussianDirection.directionLaw (E := E) := by
  have horbit : ν = (rightHaar E).map (fun u : Group E => u • x₀) := by
    refine @FangqingInvariantOrbit.invariant_probability_eq_orbit_of_support
      (Group E) E inferInstance (groupMeasurableSpace E) inferInstance
      ‹MeasurableSpace E› inferInstance (groupMeasurableAction E)
      (rightHaar E) (rightHaar_probability E) (rightHaar_rightInvariant E)
      ν inferInstance inferInstance x₀ ?_
    filter_upwards [hunit] with x hx
    exact unit_orbit E x₀ x hx₀ hx
  exact horbit.trans (gaussianDirection_eq_haar_orbit E x₀ hx₀).symm

end

end FangqingOrthogonalHaar
end

section
-- Source component: HaarSphereTail.lean
open MeasureTheory.Measure
/- Compiled after GaussianSphereAux, GaussianDirectionLaw, InvariantOrbitLaw,
and OrthogonalHaarLaw. This file develops actual sphere-tail correspondence;
it does not yet certify adaptive Haar-frame conditional law. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingHaarSphereTail

abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

def splitFirst (n : ℕ) (x : Fin (n + 1) → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i => x i.succ, x 0)

theorem splitFirst_preserves (n : ℕ) :
    MeasurePreserving (splitFirst n) (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)) := by
  have h := measurePreserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => gaussianReal 0 1) (0 : Fin (n + 1))
  convert! measurePreserving_swap.comp h using 1

theorem normalized_first_eq (n : ℕ) (x : Fin (n + 1) → ℝ) :
    FangqingGaussianDirection.normalize (WithLp.toLp 2 x : Vec n) 0 =
      FangqingGaussianSphere.normalizedLast n (splitFirst n x) := by
  rw [FangqingGaussianDirection.normalize]
  simp only [PiLp.smul_apply, smul_eq_mul, EuclideanSpace.norm_eq,
    Real.norm_eq_abs, sq_abs, Fin.sum_univ_succ,
    FangqingGaussianSphere.normalizedLast, splitFirst]
  ring

theorem gaussian_direction_first_tail (n : ℕ) (u : ℝ) (hu : 0 ≤ u) :
    (FangqingGaussianDirection.directionLaw (E := Vec n)).real
      {v : Vec n | u < |v 0|} ≤ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  let A : Set (Vec n) := {v | u < |v 0|}
  let B : Set ((Fin n → ℝ) × ℝ) :=
    {p | u < |FangqingGaussianSphere.normalizedLast n p|}
  have hA : MeasurableSet A := by
    exact isOpen_lt continuous_const (by fun_prop) |>.measurableSet
  have hB : MeasurableSet B := by
    apply measurableSet_lt measurable_const
    exact Measurable.abs (by
      unfold FangqingGaussianSphere.normalizedLast
      fun_prop)
  have hto : Measurable (WithLp.toLp 2 : (Fin (n + 1) → ℝ) → Vec n) := by fun_prop
  have heq : (FangqingGaussianDirection.directionLaw (E := Vec n)) A =
      ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)) B := by
    unfold FangqingGaussianDirection.directionLaw
    rw [← map_pi_eq_stdGaussian, Measure.map_map
      FangqingGaussianDirection.measurable_normalize hto,
      Measure.map_apply (FangqingGaussianDirection.measurable_normalize.comp hto) hA]
    have hset : (FangqingGaussianDirection.normalize ∘ WithLp.toLp 2) ⁻¹' A =
        splitFirst n ⁻¹' B := by
      ext x
      simp only [Set.mem_preimage, A, B, Set.mem_setOf_eq, Function.comp_apply]
      rw [normalized_first_eq]
    rw [hset]
    exact (splitFirst_preserves n).measure_preimage hB.nullMeasurableSet
  change (FangqingGaussianDirection.directionLaw (E := Vec n)).real A ≤ _
  have hre := congrArg ENNReal.toReal heq
  change (FangqingGaussianDirection.directionLaw (E := Vec n)).real A =
    ((Measure.pi (fun _ : Fin n => gaussianReal 0 1)).prod (gaussianReal 0 1)).real B at hre
  rw [hre]
  exact FangqingGaussianSphere.normalized_gaussian_last_tail n u hu

theorem invariant_sphere_first_tail (n : ℕ) (ν : Measure (Vec n)) [IsProbabilityMeasure ν]
    [SMulInvariantMeasure (FangqingOrthogonalHaar.Group (Vec n)) (Vec n) ν]
    (hunit : ∀ᵐ v ∂ν, ‖v‖ = 1) (u : ℝ) (hu : 0 ≤ u) :
    ν.real {v : Vec n | u < |v 0|} ≤ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  let e₀ := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  have he₀ : ‖e₀‖ = 1 := (EuclideanSpace.basisFun _ ℝ).orthonormal.norm_eq_one 0
  rw [FangqingOrthogonalHaar.invariant_unit_law_unique (Vec n) ν hunit e₀ he₀]
  exact gaussian_direction_first_tail n u hu

theorem invariant_sphere_unit_direction_tail (n : ℕ) (ν : Measure (Vec n))
    [IsProbabilityMeasure ν]
    [SMulInvariantMeasure (FangqingOrthogonalHaar.Group (Vec n)) (Vec n) ν]
    (hunit : ∀ᵐ v ∂ν, ‖v‖ = 1) (z : Vec n) (hz : ‖z‖ = 1) (s : ℝ) (hs : 0 ≤ s) :
    ν.real {v : Vec n | s < |inner ℝ v z|} ≤ 2 * Real.exp (-(n : ℝ) * s ^ 2 / 2) := by
  let e₀ := EuclideanSpace.basisFun (Fin (n + 1)) ℝ 0
  have he₀ : ‖e₀‖ = 1 := (EuclideanSpace.basisFun _ ℝ).orthonormal.norm_eq_one 0
  obtain ⟨u, hu⟩ := FangqingOrthogonalHaar.unit_orbit (Vec n) e₀ z he₀ hz
  have hinner (v : Vec n) : inner ℝ (u • v) z = v 0 := by
    rw [← hu]
    simpa only [e₀, EuclideanSpace.inner_basisFun_real] using! (Unitary.inner_map_map u v e₀)
  have hset : (fun v : Vec n => u • v) ⁻¹' {v : Vec n | s < |inner ℝ v z|} =
      {v : Vec n | s < |v 0|} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, hinner]
  have hmeasure := measure_preimage_smul ν u {v : Vec n | s < |inner ℝ v z|}
  rw [hset] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  change ν.real {v : Vec n | s < |v 0|} = ν.real {v : Vec n | s < |inner ℝ v z|} at hreal
  rw [← hreal]
  exact invariant_sphere_first_tail n ν hunit s hs

theorem invariant_sphere_cap_tail (n : ℕ) (ν : Measure (Vec n)) [IsProbabilityMeasure ν]
    [SMulInvariantMeasure (FangqingOrthogonalHaar.Group (Vec n)) (Vec n) ν]
    (hunit : ∀ᵐ v ∂ν, ‖v‖ = 1) (z : Vec n) (R s : ℝ) (hR : 0 < R)
    (hs : 0 ≤ s) (hzR : ‖z‖ ≤ R) :
    ν.real {v : Vec n | s < |inner ℝ v z|} ≤
      2 * Real.exp (-(n : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  by_cases hz0 : z = 0
  · subst z
    have he : {v : Vec n | s < |inner ℝ v (0 : Vec n)|} = ∅ := by
      ext v
      simp [not_lt.mpr hs]
    rw [he, measureReal_empty]
    positivity
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let zunit : Vec n := ‖z‖⁻¹ • z
    have hzu : ‖zunit‖ = 1 := by simp [zunit, norm_smul, hz0]
    have hscale : z = ‖z‖ • zunit := by
      simp [zunit, smul_smul, hn.ne']
    have he : {v : Vec n | s < |inner ℝ v z|} =
        {v : Vec n | s / ‖z‖ < |inner ℝ v zunit|} := by
      ext v
      simp only [Set.mem_setOf_eq]
      have hi : inner ℝ v z = ‖z‖ * inner ℝ v zunit := by
        calc
          inner ℝ v z = inner ℝ v (‖z‖ • zunit) := congrArg (inner ℝ v) hscale
          _ = _ := by rw [real_inner_smul_right]
      rw [hi, abs_mul, abs_of_pos hn, mul_comm ‖z‖ |inner ℝ v zunit|]
      exact (div_lt_iff₀ hn).symm
    rw [he]
    have hb := invariant_sphere_unit_direction_tail n ν hunit zunit hzu (s / ‖z‖)
      (div_nonneg hs hn.le)
    apply hb.trans
    have hratio : s / R ≤ s / ‖z‖ := div_le_div_of_nonneg_left hs hn hzR
    have hsq := pow_le_pow_left₀ (div_nonneg hs hR.le) hratio 2
    have hmul := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
    have he : -(n : ℝ) * (s / ‖z‖) ^ 2 / 2 ≤ -(n : ℝ) * (s / R) ^ 2 / 2 := by
      linarith only [hmul]
    convert! he using 1 <;> field_simp <;> ring

theorem haar_orbit_first_tail (n : ℕ) (x₀ : Vec n) (hx₀ : ‖x₀‖ = 1)
    (u : ℝ) (hu : 0 ≤ u) :
    ((FangqingOrthogonalHaar.rightHaar (Vec n)).map
      (fun g : FangqingOrthogonalHaar.Group (Vec n) => g • x₀)).real
      {v : Vec n | u < |v 0|} ≤ 2 * Real.exp (-(n : ℝ) * u ^ 2 / 2) := by
  rw [← FangqingOrthogonalHaar.gaussianDirection_eq_haar_orbit (Vec n) x₀ hx₀]
  exact gaussian_direction_first_tail n u hu

end FangqingHaarSphereTail
end

section
-- Source component: GaussianDirectionTransport.lean

/- Isometric transport of the actual Gaussian direction law. Compiled after
the immutable GaussianDirectionLaw and HaarSphereTail dependencies. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingDirectionTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem normalize_equiv (f : E ≃ₗᵢ[ℝ] F) (x : E) :
    FangqingGaussianDirection.normalize (f x) = f (FangqingGaussianDirection.normalize x) := by
  simp only [FangqingGaussianDirection.normalize, f.norm_map, map_smul]

theorem directionLaw_map_equiv (f : E ≃ₗᵢ[ℝ] F) :
    (FangqingGaussianDirection.directionLaw (E := E)).map f =
      FangqingGaussianDirection.directionLaw (E := F) := by
  unfold FangqingGaussianDirection.directionLaw
  rw [Measure.map_map f.continuous.measurable FangqingGaussianDirection.measurable_normalize]
  have hc : (f : E → F) ∘ FangqingGaussianDirection.normalize =
      FangqingGaussianDirection.normalize ∘ f := by
    funext x
    exact (normalize_equiv f x).symm
  rw [hc, ← Measure.map_map FangqingGaussianDirection.measurable_normalize f.continuous.measurable,
    stdGaussian_map f]

theorem direction_cap_general (n : ℕ) (hdim : Module.finrank ℝ E = n + 1)
    (z : E) (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s) (hz : ‖z‖ ≤ R) :
    (FangqingGaussianDirection.directionLaw (E := E)).real {v : E | s < |inner ℝ v z|} ≤
      2 * Real.exp (-(n : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let b : OrthonormalBasis (Fin (n + 1)) ℝ E :=
    (stdOrthonormalBasis ℝ E).reindex (finCongr hdim)
  let f : E ≃ₗᵢ[ℝ] FangqingHaarSphereTail.Vec n := b.repr
  let ν := FangqingGaussianDirection.directionLaw (E := FangqingHaarSphereTail.Vec n)
  haveI : SMulInvariantMeasure
      (FangqingOrthogonalHaar.Group (FangqingHaarSphereTail.Vec n))
      (FangqingHaarSphereTail.Vec n) ν :=
    FangqingOrthogonalHaar.gaussianDirection_invariant (FangqingHaarSphereTail.Vec n)
  have hf : MeasurePreserving f (FangqingGaussianDirection.directionLaw (E := E)) ν :=
    ⟨f.continuous.measurable, directionLaw_map_equiv f⟩
  have hm : MeasurableSet {v : FangqingHaarSphereTail.Vec n | s < |inner ℝ v (f z)|} := by
    exact (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have he := hf.measure_preimage hm.nullMeasurableSet
  have hset : f ⁻¹' {v : FangqingHaarSphereTail.Vec n | s < |inner ℝ v (f z)|} =
      {v : E | s < |inner ℝ v z|} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_setOf_eq, f.inner_map_map]
  rw [hset] at he
  have hre := congrArg ENNReal.toReal he
  change (FangqingGaussianDirection.directionLaw (E := E)).real
    {v : E | s < |inner ℝ v z|} = ν.real
    {v : FangqingHaarSphereTail.Vec n | s < |inner ℝ v (f z)|} at hre
  rw [hre]
  exact FangqingHaarSphereTail.invariant_sphere_cap_tail n ν
    FangqingGaussianDirection.directionLaw_unit_norm (f z) R s hR hs (by simpa using hz)

theorem haar_orbit_cap_general (n : ℕ) (hdim : Module.finrank ℝ E = n + 1)
    [Nontrivial E] (x₀ : E) (hx₀ : ‖x₀‖ = 1)
    (z : E) (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s) (hz : ‖z‖ ≤ R) :
    ((FangqingOrthogonalHaar.rightHaar E).map
      (fun u : FangqingOrthogonalHaar.Group E => u • x₀)).real
      {v : E | s < |inner ℝ v z|} ≤
      2 * Real.exp (-(n : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  rw [← FangqingOrthogonalHaar.gaussianDirection_eq_haar_orbit E x₀ hx₀]
  exact direction_cap_general n hdim z R s hR hs hz

end FangqingDirectionTransport
end

section
-- Source component: ResidualBlockEmbedding.lean

namespace FangqingResidualBlock

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

abbrev Group (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] := unitary (H →L[ℝ] H)

noncomputable def blockIsometry (S : Submodule ℝ E) (u : Group S) : E ≃ₗᵢ[ℝ] E :=
  S.orthogonalDecomposition.trans
    ((LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv u)
      (LinearIsometryEquiv.refl ℝ Sᗮ)).trans S.orthogonalDecomposition.symm)

theorem blockIsometry_one (S : Submodule ℝ E) :
    blockIsometry S 1 = 1 := by
  ext x
  simp [blockIsometry]

theorem blockIsometry_mul (S : Submodule ℝ E) (u v : Group S) :
    blockIsometry S (u * v) = blockIsometry S u * blockIsometry S v := by
  ext x
  change S.orthogonalDecomposition.symm
      ((LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv (u * v))
        (LinearIsometryEquiv.refl ℝ Sᗮ)) (S.orthogonalDecomposition x)) =
    S.orthogonalDecomposition.symm
      ((LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv u)
        (LinearIsometryEquiv.refl ℝ Sᗮ))
        (S.orthogonalDecomposition (S.orthogonalDecomposition.symm
          ((LinearIsometryEquiv.withLpProdCongr 2 (Unitary.linearIsometryEquiv v)
            (LinearIsometryEquiv.refl ℝ Sᗮ)) (S.orthogonalDecomposition x)))))
  rw [S.orthogonalDecomposition.apply_symm_apply]
  congr 1

noncomputable def blockHom (S : Submodule ℝ E) : Group S →* (E ≃ₗᵢ[ℝ] E) where
  toFun := blockIsometry S
  map_one' := blockIsometry_one S
  map_mul' := blockIsometry_mul S

noncomputable def embed (S : Submodule ℝ E) : Group S →* Group E :=
  Unitary.linearIsometryEquiv.symm.toMonoidHom.comp (blockHom S)

theorem embed_clm_formula (S : Submodule ℝ E) (u : Group S) :
    ((embed S u : Group E) : E →L[ℝ] E) =
      S.subtypeL.comp ((u : S →L[ℝ] S).comp S.orthogonalProjectionOnto) +
        Sᗮ.subtypeL.comp Sᗮ.orthogonalProjectionOnto := by
  ext x
  change blockIsometry S u x =
    ((u : S →L[ℝ] S) (S.orthogonalProjectionOnto x) : E) +
      (Sᗮ.orthogonalProjectionOnto x : E)
  simp [blockIsometry, Submodule.orthogonalDecomposition_apply] <;> rfl

theorem continuous_embed (S : Submodule ℝ E) : Continuous (embed S) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun u : Group S => ((embed S u : Group E) : E →L[ℝ] E))
  have heq : (fun u : Group S => ((embed S u : Group E) : E →L[ℝ] E)) =
      fun u : Group S => S.subtypeL.comp ((u : S →L[ℝ] S).comp S.orthogonalProjectionOnto) +
        Sᗮ.subtypeL.comp Sᗮ.orthogonalProjectionOnto := by
    funext u
    exact embed_clm_formula S u
  rw [heq]
  exact (continuous_const.clm_comp (continuous_subtype_val.clm_comp continuous_const)).add continuous_const

theorem embed_apply_subtype (S : Submodule ℝ E) (u : Group S) (w : S) :
    (embed S u) • (w : E) = ((u • w : S) : E) := by
  change (((embed S u : Group E) : E →L[ℝ] E) (w : E)) = _
  rw [embed_clm_formula]
  simp <;> rfl

theorem embed_fix_orthogonal (S : Submodule ℝ E) (u : Group S) (x : E)
    (hx : x ∈ Sᗮ) : (embed S u) • x = x := by
  change (((embed S u : Group E) : E →L[ℝ] E) x) = x
  rw [embed_clm_formula]
  have hp : S.orthogonalProjectionOnto x = 0 := by
    exact (Submodule.orthogonalProjectionOnto_eq_zero_iff).mpr hx
  have hq : (Sᗮ.orthogonalProjectionOnto x : E) = x := by
    have he := Sᗮ.orthogonalProjectionOnto_mem_subspace_eq_self (⟨x, hx⟩ : Sᗮ)
    exact congrArg (fun w : Sᗮ => (w : E)) he
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, hp,
    map_zero, add_zero, zero_add]
  exact hq

theorem embed_injective (S : Submodule ℝ E) : Function.Injective (embed S) := by
  intro u v huv
  apply Subtype.ext
  ext w
  have he := congrArg (fun g : Group E => ((g : E →L[ℝ] E) (w : E))) huv
  rw [embed_clm_formula, embed_clm_formula] at he
  simpa using he

end

end FangqingResidualBlock
end

section
-- Source component: ResidualHaarCap.lean

/- Actual residual block-Haar spherical cap, compiled after the genuine
sphere-tail development and ResidualBlockEmbedding. No conditional cap
bound is an input to the theorem below. -/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace FangqingResidualHaarCap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

theorem residual_orbit_cap (S : Submodule ℝ E) [Nontrivial S]
    (n : ℕ) (hdim : Module.finrank ℝ S = n + 1) (w : S) (hw : ‖w‖ = 1)
    (g : FangqingOrthogonalHaar.Group E) (z : E) (R s : ℝ)
    (hR : 0 < R) (hs : 0 ≤ s) (hz : ‖z‖ ≤ R) :
    (FangqingOrthogonalHaar.rightHaar S).real
      {u : FangqingOrthogonalHaar.Group S |
        s < |inner ℝ ((g * FangqingResidualBlock.embed S u) • (w : E)) z|} ≤
      2 * Real.exp (-(n : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let f := Unitary.linearIsometryEquiv g
  let pz : S := S.orthogonalProjectionOnto (f.symm z)
  have hpz : ‖pz‖ ≤ R := by
    calc
      ‖pz‖ ≤ ‖f.symm z‖ := S.norm_orthogonalProjectionOnto_apply_le _
      _ = ‖z‖ := f.symm.norm_map z
      _ ≤ R := hz
  have hinner (u : FangqingOrthogonalHaar.Group S) :
      inner ℝ ((g * FangqingResidualBlock.embed S u) • (w : E)) z =
        inner ℝ (u • w) pz := by
    rw [mul_smul, FangqingResidualBlock.embed_apply_subtype]
    calc
      inner ℝ (g • ((u • w : S) : E)) z = inner ℝ ((u • w : S) : E) (f.symm z) := by
        simpa only [f, LinearIsometryEquiv.apply_symm_apply] using!
          (Unitary.linearIsometryEquiv g).inner_map_map ((u • w : S) : E) (f.symm z)
      _ = _ := (S.inner_orthogonalProjectionOnto_eq_of_mem_left (u • w) (f.symm z)).symm
  let B : Set S := {v : S | s < |inner ℝ v pz|}
  have hB : MeasurableSet B := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  haveI : MeasurableSMul₂ (FangqingOrthogonalHaar.Group S) S :=
    FangqingOrthogonalHaar.groupMeasurableAction S
  have hmap : ((FangqingOrthogonalHaar.rightHaar S).map
      (fun u : FangqingOrthogonalHaar.Group S => u • w)).real B =
      (FangqingOrthogonalHaar.rightHaar S).real ((fun u => u • w) ⁻¹' B) := by
    rw [measureReal_def, Measure.map_apply (measurable_smul_const w) hB]
    rfl
  have hcap := FangqingDirectionTransport.haar_orbit_cap_general n hdim w hw pz R s hR hs hpz
  change ((FangqingOrthogonalHaar.rightHaar S).map
    (fun u : FangqingOrthogonalHaar.Group S => u • w)).real B ≤ _ at hcap
  rw [hmap] at hcap
  have heq : {u : FangqingOrthogonalHaar.Group S |
      s < |inner ℝ ((g * FangqingResidualBlock.embed S u) • (w : E)) z|} =
      (fun u : FangqingOrthogonalHaar.Group S => u • w) ⁻¹' B := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, B, hinner]
  rw [heq]
  exact hcap

end FangqingResidualHaarCap
end

section
-- Source component: PrefixDisclosureProtocol.lean

open MeasureTheory

/- Predictable disclosure and exact information fibers. This file proves
the structural invariance needed by right-Haar averaging, not a tail bound. -/

namespace FangqingPrefixProtocol

variable {Seed E F : Type*} {m : ℕ}

def agreePrefix (k : ℕ) (V W : Fin m → E) : Prop :=
  ∀ i : Fin m, i.val < k → V i = W i

theorem agreePrefix_mono {j k : ℕ} {V W : Fin m → E}
    (h : agreePrefix k V W) (hjk : j ≤ k) : agreePrefix j V W :=
  fun i hi => h i (lt_of_lt_of_le hi hjk)

def count (D : ℕ → Seed → ℕ → (Fin m → E) → Bool) : ℕ → Seed → (Fin m → E) → ℕ
  | 0, _, _ => 0
  | n + 1, seed, V =>
      let k := count D n seed V
      if k < m ∧ D n seed k V = true then k + 1 else k

theorem count_step_mono (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (n : ℕ) (seed : Seed) (V : Fin m → E) :
    count D n seed V ≤ count D (n + 1) seed V := by
  simp only [count]
  split_ifs <;> omega

theorem count_le (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (n : ℕ) (seed : Seed) (V : Fin m → E) : count D n seed V ≤ m := by
  induction n with
  | zero => simp [count]
  | succ n ih =>
      simp only [count]
      split_ifs with h
      · omega
      · exact ih

theorem count_prefix_invariant
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (n : ℕ) (seed : Seed) (V W : Fin m → E) (k : ℕ)
    (hk : count D n seed V = k) (hVW : agreePrefix k V W) :
    count D n seed W = k := by
  induction n generalizing k with
  | zero => simpa only [count] using hk
  | succ n ih =>
      let j := count D n seed V
      have hj : j ≤ k := by
        rw [← hk]
        exact count_step_mono D n seed V
      have hsmall : agreePrefix j V W := agreePrefix_mono hVW hj
      have hcount : count D n seed W = j := ih j rfl hsmall
      have hdecision := hD n seed j V W hsmall
      have hnext : count D (n + 1) seed W = count D (n + 1) seed V := by
        simp only [count, hcount]
        change (if j < m ∧ D n seed j W = true then j + 1 else j) =
          (if j < m ∧ D n seed j V = true then j + 1 else j)
        rw [hdecision]
      exact hnext.trans hk

theorem measurable_count [MeasurableSpace Seed] [MeasurableSpace E]
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (n : ℕ) : Measurable (fun x : Seed × (Fin m → E) => count D n x.1 x.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hd : Measurable (fun x : Seed × (Fin m → E) => D n x.1 (count D n x.1 x.2) x.2) :=
        (hD n).comp (measurable_fst.prodMk (ih.prodMk measurable_snd))
      have hb : MeasurableSet {x : Seed × (Fin m → E) |
          D n x.1 (count D n x.1 x.2) x.2 = true} :=
        hd (measurableSet_singleton true)
      simpa only [count] using!
        Measurable.ite ((measurableSet_lt ih measurable_const).inter hb) (ih.add_const 1) ih

variable [Zero E]

def view (D : ℕ → Seed → ℕ → (Fin m → E) → Bool) (n : ℕ)
    (x : Seed × (Fin m → E)) : Seed × ℕ × (Fin m → E) :=
  (x.1, count D n x.1 x.2,
    fun i => if i.val < count D n x.1 x.2 then x.2 i else 0)

theorem measurable_view [MeasurableSpace Seed] [MeasurableSpace E]
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (n : ℕ) : Measurable (view D n) := by
  have hk := measurable_count D hD n
  apply measurable_fst.prodMk
  apply hk.prodMk
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_const hk)
    ((measurable_pi_apply i).comp measurable_snd) measurable_const

theorem view_prefix_invariant
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (n : ℕ) (seed : Seed) (V W : Fin m → E) (k : ℕ)
    (hk : count D n seed V = k) (hVW : agreePrefix k V W) :
    view D n (seed, V) = view D n (seed, W) := by
  have hcount := count_prefix_invariant D hD n seed V W k hk hVW
  simp only [view, hk, hcount]
  congr 2
  funext i
  by_cases hi : i.val < k
  · simp only [if_pos hi, hVW i hi]
  · simp only [if_neg hi]

theorem measurable_candidate_prefix_invariant
    [MeasurableSpace Seed] [MeasurableSpace E] [MeasurableSpace F] [MeasurableSingletonClass F]
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (n : ℕ) (Z : Seed × (Fin m → E) → F)
    (hZ : Measurable[MeasurableSpace.comap (view D n) inferInstance] Z)
    (seed : Seed) (V W : Fin m → E) (k : ℕ)
    (hk : count D n seed V = k) (hVW : agreePrefix k V W) : Z (seed, V) = Z (seed, W) := by
  exact hZ.factorsThrough (view_prefix_invariant D hD n seed V W k hk hVW)

theorem history_adds_no_information {X H : Type*} [MeasurableSpace H]
    (base : MeasurableSpace X) (U : X → H) (hU : Measurable[base] U) :
    base ⊔ MeasurableSpace.comap U inferInstance = base := by
  exact sup_eq_left.mpr hU.comap_le

end FangqingPrefixProtocol
end

section
-- Source component: RightHaarAveraging.lean

/- Exact Haar averaging, including an arbitrary independent seed space.
The later block-geometric cap and original transcript correspondence are
not assumptions of a claimed whole adaptive-Haar certificate here. -/

open MeasureTheory MeasureTheory.Measure Set Function
open scoped ENNReal

namespace FangqingRightHaarAveraging

variable {G H Seed : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]
  [MeasurableSpace H] [MeasurableSpace Seed]

theorem left_right_probability_equal
    (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsMulRightInvariant μ] [IsMulLeftInvariant ν] : ν = μ := by
  ext A hA
  let f : G → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  calc
    ν A = ∫⁻ g, ∫⁻ h, f (g * h) ∂ν ∂μ := by
      simp_rw [lintegral_mul_left_eq_self f]
      simp [f, lintegral_indicator hA]
    _ = ∫⁻ h, ∫⁻ g, f (g * h) ∂μ ∂ν :=
      lintegral_lintegral_swap (hf.comp measurable_mul).aemeasurable
    _ = μ A := by
      simp_rw [lintegral_mul_right_eq_self f]
      simp [f, lintegral_indicator hA]

theorem right_average
    (μ : Measure G) [IsProbabilityMeasure μ] [IsMulRightInvariant μ]
    (ν : Measure H) [IsProbabilityMeasure ν] (η : H → G) (hη : Measurable η)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ g, f g ∂μ) = ∫⁻ g, ∫⁻ h, f (g * η h) ∂ν ∂μ := by
  symm
  calc
    _ = ∫⁻ h, ∫⁻ g, f (g * η h) ∂μ ∂ν :=
      lintegral_lintegral_swap
        (hf.comp (measurable_fst.mul (hη.comp measurable_snd))).aemeasurable
    _ = ∫⁻ _ : H, ∫⁻ g, f g ∂μ ∂ν := by
      apply lintegral_congr
      intro h
      exact lintegral_mul_right_eq_self f (η h)
    _ = _ := by simp

theorem independent_seed_average
    (σ : Measure Seed) [SFinite σ]
    (μ : Measure G) [IsProbabilityMeasure μ] [IsMulRightInvariant μ]
    (ν : Measure H) [IsProbabilityMeasure ν] (η : H → G) (hη : Measurable η)
    (f : Seed × G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂σ.prod μ) =
      ∫⁻ seed, ∫⁻ g, ∫⁻ h, f (seed, g * η h) ∂ν ∂μ ∂σ := by
  rw [lintegral_prod _ hf.aemeasurable]
  apply lintegral_congr
  intro seed
  exact right_average μ ν η hη (fun g => f (seed, g))
    (hf.comp (measurable_const.prodMk measurable_id))

theorem event_seed_average
    (σ : Measure Seed) [SFinite σ]
    (μ : Measure G) [IsProbabilityMeasure μ] [IsMulRightInvariant μ]
    (ν : Measure H) [IsProbabilityMeasure ν] (η : H → G) (hη : Measurable η)
    (A : Set (Seed × G)) (hA : MeasurableSet A) :
    (σ.prod μ) A = ∫⁻ seed, ∫⁻ g, ∫⁻ h, A.indicator (1 : Seed × G → ℝ≥0∞) (seed, g * η h) ∂ν ∂μ ∂σ := by
  rw [← lintegral_indicator_one hA]
  exact independent_seed_average σ μ ν η hη (A.indicator (1 : Seed × G → ℝ≥0∞)) (measurable_const.indicator hA)

theorem invariant_masked_event_bound
    (σ : Measure Seed) [SFinite σ]
    (μ : Measure G) [IsProbabilityMeasure μ] [IsMulRightInvariant μ]
    (ν : Measure H) [IsProbabilityMeasure ν] (η : H → G) (hη : Measurable η)
    (A P : Set (Seed × G)) (hA : MeasurableSet A) (hP : MeasurableSet P)
    (hPinv : ∀ seed g h, (seed, g * η h) ∈ P ↔ (seed, g) ∈ P)
    (p : ℝ≥0∞)
    (hcap : ∀ seed g, (seed, g) ∈ P →
      (∫⁻ h, A.indicator (1 : Seed × G → ℝ≥0∞) (seed, g * η h) ∂ν) ≤ p) :
    (σ.prod μ) (A ∩ P) ≤ p * (σ.prod μ) P := by
  rw [event_seed_average σ μ ν η hη (A ∩ P) (hA.inter hP)]
  calc
    _ ≤ ∫⁻ seed, ∫⁻ g, p * P.indicator (1 : Seed × G → ℝ≥0∞) (seed, g) ∂μ ∂σ := by
      apply lintegral_mono
      intro seed
      apply lintegral_mono
      intro g
      dsimp only
      by_cases hp : (seed, g) ∈ P
      · rw [Set.indicator_of_mem hp]
        simp only [Pi.one_apply, mul_one]
        have heq : (fun h => (A ∩ P).indicator (1 : Seed × G → ℝ≥0∞) (seed, g * η h)) =
            (fun h => A.indicator (1 : Seed × G → ℝ≥0∞) (seed, g * η h)) := by
          funext h
          have hmem := (hPinv seed g h).mpr hp
          by_cases ha : (seed, g * η h) ∈ A
          · rw [Set.indicator_of_mem (Set.mem_inter ha hmem), Set.indicator_of_mem ha]
          · rw [Set.indicator_of_notMem (fun hm => ha hm.1), Set.indicator_of_notMem ha]
        rw [heq]
        exact hcap seed g hp
      · rw [Set.indicator_of_notMem hp, mul_zero]
        have heq : (fun h => (A ∩ P).indicator (1 : Seed × G → ℝ≥0∞) (seed, g * η h)) = 0 := by
          funext h
          have hnot : (seed, g * η h) ∉ P := (hPinv seed g h).not.mpr hp
          exact Set.indicator_of_notMem (fun hm => hnot hm.2) _
        rw [heq]
        simpa only [Pi.zero_apply] using! (le_of_eq (lintegral_zero (μ := ν)))
    _ = p * (σ.prod μ) P := by
      calc
        _ = ∫⁻ x : Seed × G, p * P.indicator (1 : Seed × G → ℝ≥0∞) x ∂σ.prod μ := by
          symm
          apply lintegral_prod
          exact (measurable_const.mul (measurable_const.indicator hP)).aemeasurable
        _ = _ := by
          have hm : Measurable (P.indicator (1 : Seed × G → ℝ≥0∞)) := measurable_const.indicator hP
          have hmul := lintegral_const_mul (μ := σ.prod μ) p hm
          calc
            _ = p * (∫⁻ x : Seed × G, P.indicator (1 : Seed × G → ℝ≥0∞) x ∂σ.prod μ) := by
              simpa using! hmul
            _ = _ := by rw [lintegral_indicator_one hP]

end FangqingRightHaarAveraging
end

section
-- Source component: FinitePrefixPartition.lean

open MeasureTheory Set Function
open scoped BigOperators

namespace FangqingFinitePrefixPartition

variable {Ω : Type*} [MeasurableSpace Ω]

theorem bounded_nat_partition_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → ℕ) (hK : Measurable K) (m : ℕ) (hKm : ∀ ω, K ω ≤ m)
    (A : Set Ω) (p : ℝ)
    (hbranch : ∀ k : Fin (m + 1),
      μ.real (A ∩ {ω | K ω = k.val}) ≤ p * μ.real {ω | K ω = k.val}) :
    μ.real A ≤ p := by
  let P (k : Fin (m + 1)) : Set Ω := {ω | K ω = k.val}
  have hP : ∀ k, MeasurableSet (P k) := fun k => hK (measurableSet_singleton k.val)
  have hdisj : Pairwise (Disjoint on P) := by
    intro k l hkl
    change Disjoint (P k) (P l)
    rw [Set.disjoint_left]
    intro ω hk hl
    apply hkl
    apply Fin.ext
    exact hk.symm.trans hl
  have hcover : (⋃ k, P k) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    exact Set.mem_iUnion.mpr ⟨⟨K ω, by have h := hKm ω; omega⟩, rfl⟩
  have hsum : ∑ k, μ.real (P k) = 1 := by
    rw [← measureReal_iUnion_fintype hdisj hP, hcover, probReal_univ]
  have hsplit : A = ⋃ k : Fin (m + 1), A ∩ P k := by
    rw [← Set.inter_iUnion, hcover, Set.inter_univ]
  calc
    μ.real A = μ.real (⋃ k : Fin (m + 1), A ∩ P k) := congrArg μ.real hsplit
    _ ≤ ∑ k : Fin (m + 1), μ.real (A ∩ P k) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ k : Fin (m + 1), p * μ.real (P k) := by
      exact Finset.sum_le_sum (fun k _ => hbranch k)
    _ = p := by rw [← Finset.mul_sum, hsum, mul_one]

end FangqingFinitePrefixPartition
end

section
-- Source component: AdaptiveHaarProductSpace.lean

/- Product-space Haar concentration assembled from actual residual geometry,
predictable disclosure, and exact right-Haar averaging. Dependencies are
compiled in the recorded source order; no spherical or conditional tail
inequality is an input to the principal concentration result. -/

open MeasureTheory ProbabilityTheory Set Function
open scoped BigOperators NNReal ENNReal

namespace FangqingAdaptiveHaarProduct

noncomputable section

open FangqingPrefixProtocol

variable {Seed E : Type*} [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {m : ℕ}

abbrev Group := FangqingOrthogonalHaar.Group E

def frame (b : Fin m → E) (g : Group (E := E)) : Fin m → E := fun i => g • b i

def pull (b : Fin m → E) (x : Seed × Group (E := E)) : Seed × (Fin m → E) :=
  (x.1, frame b x.2)

theorem measurable_frame (b : Fin m → E) : Measurable (frame b) := by
  letI := FangqingOrthogonalHaar.groupMeasurableAction E
  apply measurable_pi_lambda
  intro i
  exact measurable_smul_const (b i)

theorem measurable_pull (b : Fin m → E) : Measurable (pull (Seed := Seed) b) :=
  measurable_fst.prodMk ((measurable_frame b).comp measurable_snd)

theorem rotated_prefix_agree (b : Fin m → E) (k : ℕ) (g h : Group (E := E))
    (hfix : ∀ i : Fin m, i.val < k → h • b i = b i) :
    agreePrefix k (frame b g) (frame b (g * h)) := by
  intro i hi
  simp only [frame, mul_smul, hfix i hi]

theorem count_branch_rotation_invariant (b : Fin m → E)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (r : ℕ) (seed : Seed) (k : ℕ) (g h : Group (E := E))
    (hfix : ∀ i : Fin m, i.val < k → h • b i = b i) :
    count D r seed (frame b (g * h)) = k ↔ count D r seed (frame b g) = k := by
  have ha := rotated_prefix_agree b k g h hfix
  constructor
  · intro hk
    exact count_prefix_invariant D hD r seed (frame b (g * h)) (frame b g) k hk
      (fun i hi => (ha i hi).symm)
  · intro hk
    exact count_prefix_invariant D hD r seed (frame b g) (frame b (g * h)) k hk ha

theorem candidate_rotation_invariant (b : Fin m → E)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (r : ℕ) (Z : Seed × (Fin m → E) → E)
    (hZ : Measurable[MeasurableSpace.comap (view D r) inferInstance] Z)
    (seed : Seed) (k : ℕ) (g h : Group (E := E))
    (hk : count D r seed (frame b g) = k)
    (hfix : ∀ i : Fin m, i.val < k → h • b i = b i) :
    Z (seed, frame b g) = Z (seed, frame b (g * h)) :=
  measurable_candidate_prefix_invariant D hD r Z hZ seed _ _ k hk
    (rotated_prefix_agree b k g h hfix)

def bad (b : Fin m → E) (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (r : ℕ) (Z : Seed × (Fin m → E) → E) (s : ℝ) (i : Fin m) : Set (Seed × Group (E := E)) :=
  {x | count D r x.1 (frame b x.2) ≤ i.val ∧
    s < |inner ℝ (frame b x.2 i) (Z (pull b x))|}

theorem measurable_bad (b : Fin m → E)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (r : ℕ) (Z : Seed × (Fin m → E) → E)
    (hZ : Measurable[MeasurableSpace.comap (view D r) inferInstance] Z) (s : ℝ) (i : Fin m) :
    MeasurableSet (bad b D r Z s i) := by
  have hk := (measurable_count D hDmeas r).comp (measurable_pull b)
  have hz := (hZ.mono (measurable_view D hDmeas r).comap_le le_rfl).comp (measurable_pull b)
  have hv : Measurable (fun x : Seed × Group (E := E) => frame b x.2 i) :=
    (measurable_pi_apply i).comp ((measurable_frame b).comp measurable_snd)
  have hi : Measurable (fun x : Seed × Group (E := E) => |inner ℝ (frame b x.2 i) (Z (pull b x))|) := by
    exact (hv.inner hz).abs
  simpa only [bad, pull] using!
    (measurableSet_le hk measurable_const).inter (measurableSet_lt (measurable_const (a := s)) hi)

theorem single_candidate_column_bound
    (σ : Measure Seed) [IsProbabilityMeasure σ]
    (b : Fin m → E) (hb : ∀ i, ‖b i‖ = 1) (delta : ℕ)
    (S : Fin (m + 1) → Submodule ℝ E)
    (hfix : ∀ (k : Fin (m + 1)) (u : FangqingOrthogonalHaar.Group (S k)) (j : Fin m),
      j.val < k.val → FangqingResidualBlock.embed (S k) u • b j = b j)
    (hmem : ∀ (k : Fin (m + 1)) (i : Fin m), k.val ≤ i.val → b i ∈ S k)
    (hdim : ∀ (k : Fin (m + 1)) (i : Fin m), k.val ≤ i.val →
      delta + 1 ≤ Module.finrank ℝ (S k))
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (r : ℕ) (Z : Seed × (Fin m → E) → E)
    (hZ : Measurable[MeasurableSpace.comap (view D r) inferInstance] Z)
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s)
    (hZR : ∀ seed (g : Group (E := E)), ‖Z (seed, frame b g)‖ ≤ R) (i : Fin m) :
    (σ.prod (FangqingOrthogonalHaar.rightHaar E)).real (bad b D r Z s i) ≤
      2 * Real.exp (-(delta : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let μ := FangqingOrthogonalHaar.rightHaar E
  let A := bad b D r Z s i
  let K (x : Seed × Group (E := E)) := count D r x.1 (frame b x.2)
  let p := 2 * Real.exp (-(delta : ℝ) * s ^ 2 / (2 * R ^ 2))
  have hp : 0 ≤ p := by positivity
  have hA : MeasurableSet A := measurable_bad b D hDmeas r Z hZ s i
  have hK : Measurable K := (measurable_count D hDmeas r).comp (measurable_pull b)
  apply FangqingFinitePrefixPartition.bounded_nat_partition_bound (σ.prod μ) K hK m
    (fun x => count_le D r x.1 (frame b x.2)) A p
  intro k
  let P : Set (Seed × Group (E := E)) := {x | K x = k.val}
  change (σ.prod μ).real (A ∩ P) ≤ p * (σ.prod μ).real P
  have hP : MeasurableSet P := hK (measurableSet_singleton k.val)
  by_cases hik : k.val ≤ i.val
  · have hpos : 0 < Module.finrank ℝ (S k) := by have h := hdim k i hik; omega
    haveI : Nontrivial (S k) := Module.nontrivial_of_finrank_pos hpos
    let ν := FangqingOrthogonalHaar.rightHaar (S k)
    let η := FangqingResidualBlock.embed (S k)
    letI : MeasurableMul₂ (Group (E := E)) := ⟨continuous_mul.measurable⟩
    have hη : Measurable η := (FangqingResidualBlock.continuous_embed (S k)).measurable
    have hPinv : ∀ seed g u, (seed, g * η u) ∈ P ↔ (seed, g) ∈ P := by
      intro seed g u
      exact count_branch_rotation_invariant b D hD r seed k.val g (η u) (hfix k u)
    have hcap : ∀ seed g, (seed, g) ∈ P →
        (∫⁻ u, A.indicator (1 : Seed × Group (E := E) → ℝ≥0∞) (seed, g * η u) ∂ν)
          ≤ ENNReal.ofReal p := by
      intro seed g hpg
      have hkg : count D r seed (frame b g) = k.val := hpg
      let w : S k := ⟨b i, hmem k i hik⟩
      let C : Set (FangqingOrthogonalHaar.Group (S k)) :=
        {u | s < |inner ℝ ((g * η u) • (w : E)) (Z (seed, frame b g))|}
      let F (u : FangqingOrthogonalHaar.Group (S k)) : Seed × Group (E := E) := (seed, g * η u)
      have hF : Measurable F := measurable_const.prodMk (measurable_const.mul hη)
      have hevent : F ⁻¹' A = C := by
        ext u
        have hku := (hPinv seed g u).mpr hpg
        have hzu := candidate_rotation_invariant b D hD r Z hZ seed k.val g (η u) hkg (hfix k u)
        change (count D r seed (frame b (g * η u)) ≤ i.val ∧
            s < |inner ℝ (frame b (g * η u) i) (Z (seed, frame b (g * η u)))|) ↔
          s < |inner ℝ ((g * η u) • (w : E)) (Z (seed, frame b g))|
        rw [show count D r seed (frame b (g * η u)) = k.val from hku, ← hzu]
        simp only [hik, true_and, frame, w]
      have havg : (∫⁻ u, A.indicator (1 : Seed × Group (E := E) → ℝ≥0∞) (F u) ∂ν) = ν C := by
        have hm : Measurable (A.indicator (1 : Seed × Group (E := E) → ℝ≥0∞)) :=
          measurable_const.indicator hA
        calc
          _ = ∫⁻ x, A.indicator (1 : Seed × Group (E := E) → ℝ≥0∞) x ∂ν.map F := by
            simpa using! (lintegral_map (μ := ν) hm hF).symm
          _ = ν C := by rw [lintegral_indicator_one hA, Measure.map_apply hF hA, hevent]
      let n := Module.finrank ℝ (S k) - 1
      have hnk : Module.finrank ℝ (S k) = n + 1 := by dsimp only [n]; omega
      have hn : delta ≤ n := by have h := hdim k i hik; dsimp only [n]; omega
      have hc := FangqingResidualHaarCap.residual_orbit_cap (S k) n hnk w
        (by simpa only [w] using! hb i) g (Z (seed, frame b g)) R s hR hs
        (hZR seed g)
      change ν.real C ≤ _ at hc
      have hcast : (delta : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hmul := mul_le_mul_of_nonneg_right hcast
        (by positivity : 0 ≤ s ^ 2 / (2 * R ^ 2))
      have hreal : ν.real C ≤ p := hc.trans (by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        convert! (neg_le_neg hmul) using 1 <;> ring)
      rw [havg]
      have hle := ENNReal.ofReal_le_ofReal hreal
      simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top ν C)] using hle
    have hbound := FangqingRightHaarAveraging.invariant_masked_event_bound
      σ μ ν η hη A P hA hP hPinv (ENNReal.ofReal p) hcap
    have hr := ENNReal.toReal_mono (by finiteness) hbound
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hp] using! hr
  · have he : A ∩ P = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have ha : K x ≤ i.val := hx.1.1
      have hk : K x = k.val := hx.2
      omega
    rw [he, measureReal_empty]
    exact mul_nonneg hp measureReal_nonneg

theorem finite_candidates_bound
    (σ : Measure Seed) [IsProbabilityMeasure σ]
    (b : Fin m → E) (hb : ∀ i, ‖b i‖ = 1) (delta : ℕ)
    (S : Fin (m + 1) → Submodule ℝ E)
    (hfix : ∀ (k : Fin (m + 1)) (u : FangqingOrthogonalHaar.Group (S k)) (j : Fin m),
      j.val < k.val → FangqingResidualBlock.embed (S k) u • b j = b j)
    (hmem : ∀ (k : Fin (m + 1)) (i : Fin m), k.val ≤ i.val → b i ∈ S k)
    (hdim : ∀ (k : Fin (m + 1)) (i : Fin m), k.val ≤ i.val →
      delta + 1 ≤ Module.finrank ℝ (S k))
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (N J : ℕ) (time : Fin (N + 1) → ℕ)
    (Z : Fin (N + 1) → Fin J → Seed × (Fin m → E) → E)
    (hZ : ∀ n j, Measurable[MeasurableSpace.comap (view D (time n)) inferInstance] (Z n j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s)
    (hZR : ∀ n j seed (g : Group (E := E)), ‖Z n j (seed, frame b g)‖ ≤ R) :
    (σ.prod (FangqingOrthogonalHaar.rightHaar E)).real
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m, bad b D (time n) (Z n j) s i) ≤
      2 * J * (N + 1) * m * Real.exp (-(delta : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let μ := σ.prod (FangqingOrthogonalHaar.rightHaar E)
  let p := 2 * Real.exp (-(delta : ℝ) * s ^ 2 / (2 * R ^ 2))
  calc
    _ ≤ ∑ n : Fin (N + 1), μ.real (⋃ j : Fin J, ⋃ i : Fin m, bad b D (time n) (Z n j) s i) :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), ∑ j : Fin J, ∑ i : Fin m, μ.real (bad b D (time n) (Z n j) s i) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ∑ j : Fin J, μ.real (⋃ i : Fin m, bad b D (time n) (Z n j) s i) :=
          measureReal_iUnion_fintype_le _
        _ ≤ _ := Finset.sum_le_sum (fun j _ => measureReal_iUnion_fintype_le _)
    _ ≤ ∑ _ : Fin (N + 1), ∑ _ : Fin J, ∑ _ : Fin m, p := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact single_candidate_column_bound σ b hb delta S hfix hmem hdim D hD hDmeas
        (time n) (Z n j) (hZ n j) R s hR hs (hZR n j) i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, p]
      push_cast
      ring

end

end FangqingAdaptiveHaarProduct
end

section
-- Source component: PrefixBasisGeometry.lean

namespace FangqingPrefixBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {d : ℕ}

noncomputable def known (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (b '' {i : Fin d | i.val < k})

noncomputable def remaining (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ) : Submodule ℝ E :=
  (known b k)ᗮ

theorem basis_finrank (b : OrthonormalBasis (Fin d) ℝ E) : Module.finrank ℝ E = d := by
  simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b.toBasis

theorem known_eq_prefix_range (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ) (hk : k ≤ d) :
    known b k = Submodule.span ℝ (Set.range (fun j : Fin k => b (j.castLE hk))) := by
  unfold known
  congr 1
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨i.val, hi⟩, ?_⟩
    congr 1
  · rintro ⟨j, rfl⟩
    exact ⟨j.castLE hk, j.isLt, rfl⟩

theorem known_finrank (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ) (hk : k ≤ d) :
    Module.finrank ℝ (known b k) = k := by
  rw [known_eq_prefix_range b k hk]
  have hinj : Function.Injective (fun j : Fin k => j.castLE hk) := by
    intro i j hij
    exact Fin.ext (congrArg (fun q : Fin d => q.val) hij)
  have hlin := b.orthonormal.linearIndependent.comp (fun j : Fin k => j.castLE hk) hinj
  have hd := finrank_span_eq_card hlin
  rw [Fintype.card_fin] at hd
  convert! hd using 1 <;> first | rfl | simp only [Function.comp_def]

theorem remaining_finrank (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ) (hk : k ≤ d) :
    Module.finrank ℝ (remaining b k) = d - k := by
  have he := (known b k).finrank_add_finrank_orthogonal
  rw [known_finrank b k hk, basis_finrank b] at he
  unfold remaining
  omega

theorem prefix_mem_known (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ)
    (i : Fin d) (hi : i.val < k) : b i ∈ known b k := by
  exact Submodule.subset_span ⟨i, hi, rfl⟩

theorem prefix_mem_remaining_orthogonal (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ)
    (i : Fin d) (hi : i.val < k) : b i ∈ (remaining b k)ᗮ := by
  exact (Submodule.le_orthogonal_orthogonal (known b k)) (prefix_mem_known b k i hi)

theorem tail_mem_remaining (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ)
    (i : Fin d) (hi : k ≤ i.val) : b i ∈ remaining b k := by
  have hker : known b k ≤ LinearMap.ker (InnerProductSpace.toDual ℝ E (b i)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    change inner ℝ (b i) (b j) = 0
    have hij : i ≠ j := by
      intro heq
      subst j
      exact (not_lt_of_ge hi) hj
    rw [b.inner_eq_ite]
    simp only [hij, ↓reduceIte]
  apply ((known b k).mem_orthogonal' (b i)).mpr
  intro x hx
  exact hker hx

theorem residual_embed_fixes_prefix
    (b : OrthonormalBasis (Fin d) ℝ E) (k : ℕ)
    (u : FangqingResidualBlock.Group (remaining b k))
    (i : Fin d) (hi : i.val < k) :
    (FangqingResidualBlock.embed (remaining b k) u) • b i = b i :=
  FangqingResidualBlock.embed_fix_orthogonal (remaining b k) u (b i)
    (prefix_mem_remaining_orthogonal b k i hi)

theorem residual_dimension_lower_bound
    (b : OrthonormalBasis (Fin d) ℝ E) (m k : ℕ)
    (hmd : m ≤ d) (hkm : k < m) :
    d - m + 1 ≤ Module.finrank ℝ (remaining b k) := by
  rw [remaining_finrank b k (by omega)]
  omega

end FangqingPrefixBasis
end

section
-- Source component: AdaptiveHaarReduction.lean

/- Auxiliary probability reduction for lem:adaptive-haar-side.
The spherical cap estimate and the residual conditional Haar law are NOT
proved here.  Their required conditional estimate is an explicit premise
of the reduction and must never count as certification of the whole Claim. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace FangqingAdaptiveHaar

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

def badPair {N J m : ℕ} (V : Ω → Fin m → E)
    (Z : Fin (N + 1) → Fin J → Ω → E) (disclosed : Fin (N + 1) → Ω → ℕ)
    (s : ℝ) (n : Fin (N + 1)) (j : Fin J) (i : Fin m) : Set Ω :=
  {ω | disclosed n ω ≤ i.val ∧ s < |inner ℝ (V ω i) (Z n j ω)|}

theorem measurableSet_badPair {N J m : ℕ} (V : Ω → Fin m → E)
    (Z : Fin (N + 1) → Fin J → Ω → E) (disclosed : Fin (N + 1) → Ω → ℕ)
    (hV : ∀ i, Measurable (fun ω => V ω i))
    (hZ : ∀ n j, Measurable (Z n j)) (hk : ∀ n, Measurable (disclosed n))
    (s : ℝ) (n : Fin (N + 1)) (j : Fin J) (i : Fin m) :
    MeasurableSet (badPair V Z disclosed s n j i) := by
  have hinner : Measurable (fun ω => |inner ℝ (V ω i) (Z n j ω)|) := by
    fun_prop
  simpa only [badPair] using!
    (measurableSet_le (hk n) measurable_const).inter
      (measurableSet_lt (measurable_const (a := s)) hinner)

theorem event_bound_of_conditional_indicator
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : MeasurableSpace Ω)
    (hF : F ≤ mΩ) (A : Set Ω) (hA : MeasurableSet[mΩ] A) (p : ℝ)
    (hconditional : ∀ᵐ ω ∂μ, μ[A.indicator (fun _ => (1 : ℝ)) | F] ω ≤ p) :
    μ.real A ≤ p := by
  have htotal : ∫ ω, μ[A.indicator (fun _ => (1 : ℝ)) | F] ω ∂μ = μ.real A := by
    rw [integral_condExp (m₀ := mΩ) (μ := μ) hF]
    simpa only [smul_eq_mul, mul_one] using (integral_indicator_const (μ := μ) (1 : ℝ) hA)
  have hbound := integral_mono_ae
    (integrable_condExp (m := F) (f := A.indicator (fun _ => (1 : ℝ))))
    (integrable_const p) hconditional
  simpa only [htotal, integral_const, measureReal_univ_eq_one, one_smul] using hbound

theorem conditional_union_reduction
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N J m : ℕ)
    (F : Fin (N + 1) → MeasurableSpace Ω) (hF : ∀ n, F n ≤ mΩ)
    (A : Fin (N + 1) → Fin J → Fin m → Set Ω)
    (hA : ∀ n j i, MeasurableSet[mΩ] (A n j i)) (p : ℝ)
    (hconditional : ∀ n j i, ∀ᵐ ω ∂μ,
      μ[(A n j i).indicator (fun _ => (1 : ℝ)) | F n] ω ≤ p) :
    μ.real (⋃ n, ⋃ j, ⋃ i, A n j i) ≤ ((N + 1 : ℕ) : ℝ) * J * m * p := by
  calc
    μ.real (⋃ n, ⋃ j, ⋃ i, A n j i)
        ≤ ∑ n, μ.real (⋃ j, ⋃ i, A n j i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ n, ∑ j, ∑ i, μ.real (A n j i) := by
      apply Finset.sum_le_sum
      intro n hn
      calc
        μ.real (⋃ j, ⋃ i, A n j i) ≤ ∑ j : Fin J, μ.real (⋃ i, A n j i) :=
          measureReal_iUnion_fintype_le _
        _ ≤ ∑ j : Fin J, ∑ i : Fin m, μ.real (A n j i) := by
          apply Finset.sum_le_sum
          intro j hj
          exact measureReal_iUnion_fintype_le _
    _ ≤ ∑ n : Fin (N + 1), ∑ j : Fin J, ∑ i : Fin m, p := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro i hi
      exact event_bound_of_conditional_indicator μ (F n) (hF n) (A n j i)
        (hA n j i) p (hconditional n j i)
    _ = ((N + 1 : ℕ) : ℝ) * J * m * p := by simp; ring

theorem logarithmic_budget (B delta exponent : ℝ) (hB : 0 < B) (hd : 0 < delta)
    (hbudget : Real.log (B / delta) ≤ exponent) :
    B * Real.exp (-exponent) ≤ delta := by
  calc
    B * Real.exp (-exponent) ≤ B * Real.exp (-Real.log (B / delta)) := by
      gcongr
    _ = delta := by
      rw [Real.exp_neg, Real.exp_log (div_pos hB hd)]
      field_simp

theorem dimension_budget (B delta c D R s : ℝ)
    (hB : 0 < B) (hd : 0 < delta) (hc : 0 < c) (hR : 0 < R) (hs : 0 < s)
    (hD : R ^ 2 / (c * s ^ 2) * Real.log (B / delta) ≤ D) :
    B * Real.exp (-(c * D * s ^ 2 / R ^ 2)) ≤ delta := by
  have ha : 0 < c * s ^ 2 / R ^ 2 := by positivity
  have hb : Real.log (B / delta) / (c * s ^ 2 / R ^ 2) ≤ D := by
    convert hD using 1 <;> field_simp <;> ring
  have hscale := (div_le_iff₀ ha).mp hb
  apply logarithmic_budget B delta _ hB hd
  convert! hscale using 1 <;> ring

end FangqingAdaptiveHaar
end

section
-- Source component: AdaptiveHaarConcrete.lean

/- Concrete orthonormal-basis Haar frame, with no residual geometry or cap
bound left as a premise. Original-space information-factorization/transport
is proved in the separately recorded companion sources. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingAdaptiveHaarConcrete

noncomputable section

open FangqingPrefixProtocol FangqingAdaptiveHaarProduct

variable {Seed E : Type*} [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {d m : ℕ}

def basisPrefix (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) : Fin m → E :=
  fun i => b (i.castLE hmd)

theorem basis_haar_bound
    (σ : Measure Seed) [IsProbabilityMeasure σ]
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (N J : ℕ) (time : Fin (N + 1) → ℕ)
    (Z : Fin (N + 1) → Fin J → Seed × (Fin m → E) → E)
    (hZ : ∀ n j, Measurable[MeasurableSpace.comap (view D (time n)) inferInstance] (Z n j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s)
    (hZR : ∀ n j seed (g : FangqingOrthogonalHaar.Group E),
      ‖Z n j (seed, frame (basisPrefix b hmd) g)‖ ≤ R) :
    (σ.prod (FangqingOrthogonalHaar.rightHaar E)).real
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        bad (basisPrefix b hmd) D (time n) (Z n j) s i) ≤
      2 * J * (N + 1) * m * Real.exp (-((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let S (k : Fin (m + 1)) := FangqingPrefixBasis.remaining b k.val
  apply finite_candidates_bound σ (basisPrefix b hmd)
    (fun i => b.orthonormal.norm_eq_one (i.castLE hmd)) (d - m) S
    ?_ ?_ ?_ D hD hDmeas N J time Z hZ R s hR hs hZR
  · intro k u j hj
    exact FangqingPrefixBasis.residual_embed_fixes_prefix b k.val u (j.castLE hmd) hj
  · intro k i hi
    exact FangqingPrefixBasis.tail_mem_remaining b k.val (i.castLE hmd) hi
  · intro k i hi
    exact FangqingPrefixBasis.residual_dimension_lower_bound b m k.val hmd
      (lt_of_le_of_lt hi i.isLt)

theorem basis_haar_dimension_corollary
    (σ : Measure Seed) [IsProbabilityMeasure σ]
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (N J : ℕ) (hJ : 0 < J) (hm : 0 < m) (time : Fin (N + 1) → ℕ)
    (Z : Fin (N + 1) → Fin J → Seed × (Fin m → E) → E)
    (hZ : ∀ n j, Measurable[MeasurableSpace.comap (view D (time n)) inferInstance] (Z n j))
    (R s deltaProb : ℝ) (hR : 0 < R) (hs : 0 < s) (hdp : 0 < deltaProb)
    (hZR : ∀ n j seed (g : FangqingOrthogonalHaar.Group E),
      ‖Z n j (seed, frame (basisPrefix b hmd) g)‖ ≤ R)
    (hbudget : 2 * R ^ 2 / s ^ 2 * Real.log ((2 * J * (N + 1) * m) / deltaProb) ≤
      ((d - m : ℕ) : ℝ)) :
    (σ.prod (FangqingOrthogonalHaar.rightHaar E)).real
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        bad (basisPrefix b hmd) D (time n) (Z n j) s i) ≤ deltaProb := by
  have hb := basis_haar_bound σ b hmd D hD hDmeas N J time Z hZ R s hR hs.le hZR
  let B : ℝ := 2 * J * (N + 1) * m
  have hB : 0 < B := by dsimp only [B]; positivity
  have hscaled : R ^ 2 / ((1 / 2 : ℝ) * s ^ 2) * Real.log (B / deltaProb) ≤
      ((d - m : ℕ) : ℝ) := by
    convert! hbudget using 1 <;> field_simp <;> ring
  have hd := FangqingAdaptiveHaar.dimension_budget B deltaProb (1 / 2) ((d - m : ℕ) : ℝ)
    R s hB hdp (by norm_num) hR hs hscaled
  have he : -((1 / 2 : ℝ) * ((d - m : ℕ) : ℝ) * s ^ 2 / R ^ 2) =
      -((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2) := by ring
  rw [he] at hd
  exact hb.trans hd

end

end FangqingAdaptiveHaarConcrete
end

section
-- Source component: IndependentFrameTransport.lean

/- Genuine independence/product-law transport, including an arbitrary
external sigma field represented by the identity into its trimmed space. -/

open MeasureTheory ProbabilityTheory Set

namespace FangqingIndependentFrame

variable {Ω Seed Frame : Type*} [mΩ : MeasurableSpace Ω]
  [mSeed : MeasurableSpace Seed] [mFrame : MeasurableSpace Frame]

theorem independent_joint_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Seed) (V : Ω → Frame) (hX : Measurable X) (hV : Measurable V)
    (hind : IndepFun X V μ) (ν : Measure Frame) (hlaw : μ.map V = ν) :
    μ.map (fun ω => (X ω, V ω)) = (μ.map X).prod ν := by
  rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hV.aemeasurable, hlaw]

theorem independent_event_transport (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Seed) (V : Ω → Frame) (hX : Measurable X) (hV : Measurable V)
    (hind : IndepFun X V μ) (ν : Measure Frame) (hlaw : μ.map V = ν)
    (A : Set (Seed × Frame)) (hA : MeasurableSet A) :
    μ ((fun ω => (X ω, V ω)) ⁻¹' A) = ((μ.map X).prod ν) A := by
  rw [← independent_joint_law μ X V hX hV hind ν hlaw,
    Measure.map_apply (hX.prodMk hV) hA]

theorem independent_sigma_joint_law (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (V : Ω → Frame)
    (hV : @Measurable Ω Frame mΩ mFrame V)
    (hind : @Indep Ω G (mFrame.comap V) mΩ μ) (ν : Measure Frame)
    (hlaw : @Measure.map Ω Frame mΩ mFrame V μ = ν) :
    @Measure.map Ω (Ω × Frame) mΩ (G.prod mFrame) (fun ω => (ω, V ω)) μ =
      (μ.trim hG).prod ν := by
  have hId : @Measurable Ω Ω mΩ G id := by
    intro A hA
    exact hG A hA
  have hIndFun : @IndepFun Ω Ω Frame mΩ G mFrame id V μ := by
    change @Indep Ω (G.comap id) (mFrame.comap V) mΩ μ
    simpa only [MeasurableSpace.comap_id] using hind
  have hmap : @Measure.map Ω Ω mΩ G id μ = μ.trim hG := by
    ext A hA
    rw [Measure.map_apply hId hA, trim_measurableSet_eq hG hA]
    rfl
  have hjoint := hIndFun.map_prod_eq_prod_map_map hId.aemeasurable hV.aemeasurable
  rw [hmap, hlaw] at hjoint
  exact hjoint

end FangqingIndependentFrame
end

section
-- Source component: SideInformationFactorization.lean

/- Genuine measurable off-diagonal factorization for an arbitrary external
sigma field. Constancy on set fibers alone is deliberately insufficient. -/

open MeasureTheory

namespace FangqingSideFactorization

variable {Ω Y E : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y]
  [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

theorem external_prefix_sigma (G : MeasurableSpace Ω) (P : Ω → Y) :
    (G.prod mY).comap (fun ω => (ω, P ω)) = G ⊔ mY.comap P := by
  rw [MeasurableSpace.comap_prodMk]
  change G.comap id ⊔ mY.comap P = G ⊔ mY.comap P
  rw [MeasurableSpace.comap_id]

theorem external_prefix_measurable_factor (G : MeasurableSpace Ω) (P : Ω → Y)
    (Z : Ω → E) (hZ : @Measurable Ω E (G ⊔ mY.comap P) mE Z) :
    ∃ q : Ω × Y → E, @Measurable (Ω × Y) E (G.prod mY) mE q ∧
      Z = fun ω => q (ω, P ω) := by
  letI : MeasurableSpace (Ω × Y) := G.prod mY
  have hZ' : Measurable[(G.prod mY).comap (fun ω => (ω, P ω))] Z := by
    rw [external_prefix_sigma]
    exact hZ
  obtain ⟨q, hq, heq⟩ := hZ'.exists_eq_measurable_comp (f := fun ω => (ω, P ω))
  exact ⟨q, hq, heq⟩

theorem auxiliary_history_sigma {H : Type*} [MeasurableSpace H]
    (G : MeasurableSpace Ω) (P : Ω → Y) (U : Ω → H)
    (hU : @Measurable Ω H (G ⊔ mY.comap P) _ U) :
    (G ⊔ mY.comap P) ⊔ MeasurableSpace.comap U inferInstance = G ⊔ mY.comap P := by
  exact sup_eq_left.mpr hU.comap_le

theorem external_prefix_history_factor {H : Type*} [MeasurableSpace H]
    (G : MeasurableSpace Ω) (P : Ω → Y) (U : Ω → H)
    (hU : @Measurable Ω H (G ⊔ mY.comap P) _ U) (Z : Ω → E)
    (hZ : @Measurable Ω E
      ((G ⊔ mY.comap P) ⊔ MeasurableSpace.comap U inferInstance) mE Z) :
    ∃ q : Ω × Y → E, @Measurable (Ω × Y) E (G.prod mY) mE q ∧
      Z = fun ω => q (ω, P ω) := by
  rw [auxiliary_history_sigma G P U hU] at hZ
  exact external_prefix_measurable_factor G P Z hZ

end FangqingSideFactorization
end

section
-- Source component: AdaptiveHaarOriginalSpace.lean

/- Pullback to an arbitrary original probability space with an independent
side-information random variable and an actual Haar Stiefel-frame law. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingAdaptiveHaarOriginal

noncomputable section

open FangqingPrefixProtocol FangqingAdaptiveHaarProduct FangqingAdaptiveHaarConcrete

variable {Ω Seed E : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {m d : ℕ}

def rawBad (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (r : ℕ) (Z : Seed × (Fin m → E) → E) (s : ℝ) (i : Fin m) : Set (Seed × (Fin m → E)) :=
  {x | count D r x.1 x.2 ≤ i.val ∧ s < |inner ℝ (x.2 i) (Z x)|}

theorem measurable_rawBad
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (r : ℕ) (Z : Seed × (Fin m → E) → E)
    (hZ : Measurable[MeasurableSpace.comap (view D r) inferInstance] Z) (s : ℝ) (i : Fin m) :
    MeasurableSet (rawBad D r Z s i) := by
  have hk := measurable_count D hDmeas r
  have hz := hZ.mono (measurable_view D hDmeas r).comap_le le_rfl
  have hv : Measurable (fun x : Seed × (Fin m → E) => x.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hi : Measurable (fun x : Seed × (Fin m → E) => |inner ℝ (x.2 i) (Z x)|) := (hv.inner hz).abs
  simpa only [rawBad] using!
    (measurableSet_le hk measurable_const).inter (measurableSet_lt (measurable_const (a := s)) hi)

def frameLaw (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) : Measure (Fin m → E) :=
  (FangqingOrthogonalHaar.rightHaar E).map (frame (basisPrefix b hmd))

theorem rightHaar_standard_left : FangqingOrthogonalHaar.rightHaar E =
    Measure.haarMeasure (FangqingOrthogonalHaar.groupUniv E) := by
  letI : MeasurableMul₂ (FangqingOrthogonalHaar.Group E) := ⟨continuous_mul.measurable⟩
  haveI : IsProbabilityMeasure (Measure.haarMeasure (FangqingOrthogonalHaar.groupUniv E)) := by
    constructor
    have hself := Measure.haarMeasure_self (K₀ := FangqingOrthogonalHaar.groupUniv E)
    change (Measure.haarMeasure (FangqingOrthogonalHaar.groupUniv E)) Set.univ = 1 at hself
    exact hself
  exact (FangqingRightHaarAveraging.left_right_probability_equal
    (FangqingOrthogonalHaar.rightHaar E)
    (Measure.haarMeasure (FangqingOrthogonalHaar.groupUniv E))).symm

theorem frameLaw_standard_haar (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) :
    frameLaw b hmd = (Measure.haarMeasure (FangqingOrthogonalHaar.groupUniv E)).map
      (frame (basisPrefix b hmd)) := by
  unfold frameLaw
  rw [rightHaar_standard_left]

theorem frame_orthonormal (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (g : FangqingOrthogonalHaar.Group E) : Orthonormal ℝ (frame (basisPrefix b hmd) g) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hi : inner ℝ (g • basisPrefix b hmd i) (g • basisPrefix b hmd j) =
      inner ℝ (basisPrefix b hmd i) (basisPrefix b hmd j) := by
    simpa using! Unitary.inner_map_map g (basisPrefix b hmd i) (basisPrefix b hmd j)
  change inner ℝ (g • basisPrefix b hmd i) (g • basisPrefix b hmd j) = _
  rw [hi]
  simpa only [basisPrefix, Fin.castLE_inj] using b.inner_eq_ite (i.castLE hmd) (j.castLE hmd)

theorem pull_preserves (σ : Measure Seed) [SFinite σ]
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) :
    MeasurePreserving (pull (Seed := Seed) (basisPrefix b hmd))
      (σ.prod (FangqingOrthogonalHaar.rightHaar E)) (σ.prod (frameLaw b hmd)) := by
  have hframe : MeasurePreserving (frame (basisPrefix b hmd))
      (FangqingOrthogonalHaar.rightHaar E) (frameLaw b hmd) :=
    ⟨measurable_frame _, rfl⟩
  exact (MeasurePreserving.id σ).prod hframe

theorem independent_original_space_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → Seed) (V : Ω → (Fin m → E)) (hX : Measurable X) (hV : Measurable V)
    (hind : IndepFun X V μ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d) (hlaw : μ.map V = frameLaw b hmd)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool)
    (hD : ∀ n seed k V W, agreePrefix k V W → D n seed k V = D n seed k W)
    (hDmeas : ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => D n x.1 x.2.1 x.2.2))
    (N J : ℕ) (time : Fin (N + 1) → ℕ)
    (Z : Fin (N + 1) → Fin J → Seed × (Fin m → E) → E)
    (hZ : ∀ n j, Measurable[MeasurableSpace.comap (view D (time n)) inferInstance] (Z n j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s)
    (hZR : ∀ n j seed (g : FangqingOrthogonalHaar.Group E),
      ‖Z n j (seed, frame (basisPrefix b hmd) g)‖ ≤ R) :
    μ.real ((fun ω => (X ω, V ω)) ⁻¹'
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m, rawBad D (time n) (Z n j) s i)) ≤
      2 * J * (N + 1) * m * Real.exp (-((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2)) := by
  let σ := μ.map X
  haveI : IsProbabilityMeasure σ := Measure.isProbabilityMeasure_map hX.aemeasurable
  let A : Set (Seed × (Fin m → E)) :=
    ⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m, rawBad D (time n) (Z n j) s i
  have hA : MeasurableSet A := by
    exact MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun j =>
      MeasurableSet.iUnion (fun i => measurable_rawBad D hDmeas (time n) (Z n j) (hZ n j) s i)))
  have hleft := FangqingIndependentFrame.independent_event_transport μ X V hX hV hind
    (frameLaw b hmd) hlaw A hA
  have hright := (pull_preserves σ b hmd).measure_preimage hA.nullMeasurableSet
  have hset : (pull (Seed := Seed) (basisPrefix b hmd)) ⁻¹' A =
      ⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        bad (basisPrefix b hmd) D (time n) (Z n j) s i := by
    ext x
    simp only [A, Set.mem_preimage, Set.mem_iUnion, rawBad, bad, pull, Set.mem_setOf_eq]
  rw [hset] at hright
  have heq := hleft.trans hright.symm
  have hre := congrArg ENNReal.toReal heq
  change μ.real ((fun ω => (X ω, V ω)) ⁻¹' A) =
    (σ.prod (FangqingOrthogonalHaar.rightHaar E)).real
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        bad (basisPrefix b hmd) D (time n) (Z n j) s i) at hre
  rw [hre]
  exact basis_haar_bound σ b hmd D hD hDmeas N J time Z hZ R s hR hs hZR

end

end FangqingAdaptiveHaarOriginal
end

section
-- Source component: BoundedFactorExtension.lean

namespace FangqingBoundedFactor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def clip (R : ℝ) (z : E) : E :=
  if ‖z‖ ≤ R then z else (R / ‖z‖) • z

theorem clip_eq_self_of_norm_le (R : ℝ) (z : E) (hz : ‖z‖ ≤ R) :
    clip R z = z := by simp only [clip, hz, ↓reduceIte]

theorem measurable_clip (R : ℝ) : Measurable (clip (E := E) R) := by
  exact measurable_id.ite (measurableSet_le measurable_norm measurable_const)
    ((measurable_const.div measurable_norm).smul measurable_id)

theorem norm_clip_le (R : ℝ) (hR : 0 ≤ R) (z : E) : ‖clip R z‖ ≤ R := by
  by_cases hz : ‖z‖ ≤ R
  · rw [clip_eq_self_of_norm_le R z hz]
    exact hz
  · have hp : 0 < ‖z‖ := lt_of_le_of_lt hR (lt_of_not_ge hz)
    rw [clip, if_neg hz, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hR (norm_nonneg z)), div_mul_cancel₀ _ (ne_of_gt hp)]

noncomputable def boundedFactor {A : Type*} (R : ℝ) (q : A → E) : A → E :=
  fun a => clip R (q a)

theorem boundedFactor_properties {A : Type*} [MeasurableSpace A]
    (R : ℝ) (hR : 0 ≤ R) (q : A → E) (hq : Measurable q) :
    Measurable (boundedFactor R q) ∧ ∀ a, ‖boundedFactor R q a‖ ≤ R :=
  ⟨(measurable_clip R).comp hq, fun a => norm_clip_le R hR (q a)⟩

theorem boundedFactor_representation {Ω A : Type*}
    (R : ℝ) (q : A → E) (X : Ω → A) (Z : Ω → E)
    (hrep : ∀ ω, q (X ω) = Z ω) (hbound : ∀ ω, ‖Z ω‖ ≤ R) :
    ∀ ω, boundedFactor R q (X ω) = Z ω := by
  intro ω
  unfold boundedFactor
  rw [hrep ω]
  exact clip_eq_self_of_norm_le R (Z ω) (hbound ω)

theorem boundedFactor_representation_ae {Ω A : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (R : ℝ) (q : A → E) (X : Ω → A) (Z : Ω → E)
    (hrep : ∀ᵐ ω ∂μ, q (X ω) = Z ω) (hbound : ∀ᵐ ω ∂μ, ‖Z ω‖ ≤ R) :
    ∀ᵐ ω ∂μ, boundedFactor R q (X ω) = Z ω := by
  filter_upwards [hrep, hbound] with ω hω hb
  unfold boundedFactor
  rw [hω]
  exact clip_eq_self_of_norm_le R (Z ω) hb

end FangqingBoundedFactor
end

section
-- Source component: PrefixAdaptedModel.lean

/- Measurable factors on the actual side×prefix product are converted to
globally defined predictable protocols and bounded candidates. -/

open MeasureTheory

namespace FangqingPrefixAdaptedModel

open FangqingPrefixProtocol

variable {Seed E Ω : Type*} [Zero E] {m : ℕ}

def mask (k : ℕ) (V : Fin m → E) : Fin m → E :=
  fun i => if i.val < k then V i else 0

def maskInput (x : Seed × ℕ × (Fin m → E)) : Seed × ℕ × (Fin m → E) :=
  (x.1, x.2.1, mask x.2.1 x.2.2)

theorem mask_agree (k : ℕ) (V W : Fin m → E) (h : agreePrefix k V W) : mask k V = mask k W := by
  funext i
  by_cases hi : i.val < k
  · simp only [mask, if_pos hi, h i hi]
  · simp only [mask, if_neg hi]

theorem measurable_maskInput [MeasurableSpace Seed] [MeasurableSpace E] :
    Measurable (maskInput (Seed := Seed) (E := E) (m := m)) := by
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite
    (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd))
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)) measurable_const

def decision (q : ℕ → Seed × ℕ × (Fin m → E) → Bool)
    (n : ℕ) (seed : Seed) (k : ℕ) (V : Fin m → E) : Bool :=
  q n (seed, k, mask k V)

theorem decision_prefix (q : ℕ → Seed × ℕ × (Fin m → E) → Bool) :
    ∀ n seed k V W, agreePrefix k V W → decision q n seed k V = decision q n seed k W := by
  intro n seed k V W h
  simp only [decision, mask_agree k V W h]

theorem decision_measurable [MeasurableSpace Seed] [MeasurableSpace E]
    (q : ℕ → Seed × ℕ × (Fin m → E) → Bool) (hq : ∀ n, Measurable (q n)) :
    ∀ n, Measurable (fun x : Seed × ℕ × (Fin m → E) => decision q n x.1 x.2.1 x.2.2) := by
  intro n
  exact (hq n).comp measurable_maskInput

def candidate (q : Seed × ℕ × (Fin m → E) → E)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool) (r : ℕ) : Seed × (Fin m → E) → E :=
  q ∘ view D r

theorem candidate_measurable [MeasurableSpace Seed] [MeasurableSpace E]
    (q : Seed × ℕ × (Fin m → E) → E) (hq : Measurable q)
    (D : ℕ → Seed → ℕ → (Fin m → E) → Bool) (r : ℕ) :
    Measurable[MeasurableSpace.comap (view D r) inferInstance] (candidate q D r) := by
  exact hq.comp (comap_measurable (view D r))

theorem count_representation
    (X : Ω → Seed) (V : Ω → (Fin m → E)) (K : ℕ → Ω → ℕ) (d : ℕ → Ω → Bool)
    (hK0 : ∀ ω, K 0 ω = 0)
    (hKstep : ∀ n ω, K (n + 1) ω = if K n ω < m ∧ d n ω = true then K n ω + 1 else K n ω)
    (q : ℕ → Seed × ℕ × (Fin m → E) → Bool)
    (hfactor : ∀ n ω, q n (X ω, K n ω, mask (K n ω) (V ω)) = d n ω) :
    ∀ n ω, count (decision q) n (X ω) (V ω) = K n ω := by
  intro n
  induction n with
  | zero => intro ω; simp only [FangqingPrefixProtocol.count, hK0]
  | succ n ih =>
      intro ω
      rw [FangqingPrefixProtocol.count, ih ω, hKstep, decision, hfactor]

end FangqingPrefixAdaptedModel
end

section
-- Source component: AdaptiveHaarExternalSigma.lean

/- Original-space arbitrary external sigma field. Measurable Doob-Dynkin
factors are constructed on the genuine side×prefix product, then clipped
without changing the original bounded candidates. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal

namespace FangqingAdaptiveHaarExternal

noncomputable section

open FangqingPrefixProtocol FangqingPrefixAdaptedModel FangqingAdaptiveHaarOriginal

structure Side (Ω : Type*) (G : MeasurableSpace Ω) where
  val : Ω

instance sideMeasurableSpace {Ω : Type*} (G : MeasurableSpace Ω) : MeasurableSpace (Side Ω G) :=
  G.comap Side.val

theorem lift_comap {Ω : Type*} (G : MeasurableSpace Ω) :
    (inferInstance : MeasurableSpace (Side Ω G)).comap (Side.mk : Ω → Side Ω G) = G := by
  change (G.comap Side.val).comap Side.mk = G
  rw [MeasurableSpace.comap_comp]
  change G.comap id = G
  rw [MeasurableSpace.comap_id]

theorem measurable_lift {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) :
    @Measurable Ω (Side Ω G) mΩ inferInstance Side.mk := by
  apply Measurable.of_comap_le
  rw [lift_comap]
  exact hG

theorem measurable_down_pair {Ω P : Type*} (G : MeasurableSpace Ω) [mP : MeasurableSpace P] :
    @Measurable (Side Ω G × P) (Ω × P) inferInstance (G.prod mP)
      (fun x => (x.1.val, x.2)) := by
  have hdown : @Measurable (Side Ω G) Ω inferInstance G Side.val := comap_measurable Side.val
  exact hdown.prodMap measurable_id

variable {Ω E H : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E] [Nontrivial E] {m d : ℕ}

def prefixInfo (K : ℕ → Ω → ℕ) (V : Ω → (Fin m → E)) (n : ℕ) (ω : Ω) : ℕ × (Fin m → E) :=
  (K n ω, mask (K n ω) (V ω))

def HaarConclusion (prob : ℝ) (d m N J : ℕ) (R s : ℝ) : Prop :=
  prob ≤ 2 * J * (N + 1) * m * Real.exp (-((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2)) ∧
    ∀ deltaProb : ℝ, 0 < deltaProb → 0 < J → 0 < m → 0 < s →
      2 * R ^ 2 / s ^ 2 * Real.log ((2 * J * (N + 1) * m) / deltaProb) ≤
        ((d - m : ℕ) : ℝ) → prob ≤ deltaProb

theorem conclusion_of_bound (prob : ℝ) (d m N J : ℕ) (R s : ℝ) (hR : 0 < R)
    (hb : prob ≤ 2 * J * (N + 1) * m *
      Real.exp (-((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2))) :
    HaarConclusion prob d m N J R s := by
  refine ⟨hb, ?_⟩
  intro deltaProb hdp hJ hm hs hbudget
  let B : ℝ := 2 * J * (N + 1) * m
  have hB : 0 < B := by dsimp only [B]; positivity
  have hscaled : R ^ 2 / ((1 / 2 : ℝ) * s ^ 2) * Real.log (B / deltaProb) ≤
      ((d - m : ℕ) : ℝ) := by
    convert! hbudget using 1 <;> field_simp <;> ring
  have hd := FangqingAdaptiveHaar.dimension_budget B deltaProb (1 / 2) ((d - m : ℕ) : ℝ)
    R s hB hdp (by norm_num) hR hs hscaled
  have he : -((1 / 2 : ℝ) * ((d - m : ℕ) : ℝ) * s ^ 2 / R ^ 2) =
      -((d - m : ℕ) : ℝ) * s ^ 2 / (2 * R ^ 2) := by ring
  rw [he] at hd
  exact hb.trans hd

theorem empty_frame_conclusion (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d N J : ℕ) (R s : ℝ) (hR : 0 < R)
    (A : Fin (N + 1) → Fin J → Fin 0 → Set Ω) :
    HaarConclusion (μ.real (⋃ n, ⋃ j, ⋃ i, A n j i)) d 0 N J R s := by
  apply conclusion_of_bound _ d 0 N J R s hR
  simp

theorem arbitrary_external_sigma_complete
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (V : Ω → (Fin m → E)) (hV : @Measurable Ω (Fin m → E) mΩ inferInstance V)
    (hind : @Indep Ω G ((inferInstance : MeasurableSpace (Fin m → E)).comap V) mΩ μ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (hlaw : @Measure.map Ω (Fin m → E) mΩ inferInstance V μ = frameLaw b hmd)
    (K : ℕ → Ω → ℕ) (Dorig : ℕ → Ω → Bool) (U : ℕ → Ω → H)
    (hK0 : ∀ ω, K 0 ω = 0)
    (hKstep : ∀ n ω, K (n + 1) ω = if K n ω < m ∧ Dorig n ω = true then K n ω + 1 else K n ω)
    (hU : ∀ n, @Measurable Ω H
      (G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap (prefixInfo K V n)) _ (U n))
    (hDinfo : ∀ n, @Measurable Ω Bool
      ((G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap (prefixInfo K V n)) ⊔
        MeasurableSpace.comap (U n) inferInstance) inferInstance (Dorig n))
    (N J : ℕ) (time : Fin (N + 1) → ℕ) (Zorig : Fin (N + 1) → Fin J → Ω → E)
    (hZinfo : ∀ n j, @Measurable Ω E
      ((G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap (prefixInfo K V (time n))) ⊔
        MeasurableSpace.comap (U (time n)) inferInstance) mE (Zorig n j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s) (hZR : ∀ n j ω, ‖Zorig n j ω‖ ≤ R) :
    HaarConclusion
      (μ.real (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        {ω | K (time n) ω ≤ i.val ∧ s < |inner ℝ (V ω i) (Zorig n j ω)|})) d m N J R s := by
  classical
  letI : MeasurableSpace Ω := mΩ
  apply conclusion_of_bound _ d m N J R s hR
  have hexD : ∀ n, ∃ q : Ω × ℕ × (Fin m → E) → Bool,
      @Measurable (Ω × ℕ × (Fin m → E)) Bool
        (G.prod inferInstance) inferInstance q ∧
      Dorig n = fun ω => q (ω, prefixInfo K V n ω) := by
    intro n
    exact FangqingSideFactorization.external_prefix_history_factor G (prefixInfo K V n)
      (U n) (hU n) (Dorig n) (hDinfo n)
  choose qD hqD hrepD using hexD
  have hexZ : ∀ n j, ∃ q : Ω × ℕ × (Fin m → E) → E,
      @Measurable (Ω × ℕ × (Fin m → E)) E (G.prod inferInstance) mE q ∧
      Zorig n j = fun ω => q (ω, prefixInfo K V (time n) ω) := by
    intro n j
    exact FangqingSideFactorization.external_prefix_history_factor G (prefixInfo K V (time n))
      (U (time n)) (hU (time n)) (Zorig n j) (hZinfo n j)
  choose qZ hqZ hrepZ using hexZ
  let qDS (n : ℕ) (x : Side Ω G × ℕ × (Fin m → E)) := qD n (x.1.val, x.2)
  have hqDS : ∀ n, Measurable (qDS n) := fun n => (hqD n).comp (measurable_down_pair G)
  let D := decision qDS
  have hDP := decision_prefix qDS
  have hDM := decision_measurable qDS hqDS
  have hcount : ∀ n ω, count D n (Side.mk ω) (V ω) = K n ω := by
    apply count_representation (Side.mk : Ω → Side Ω G) V K Dorig hK0 hKstep qDS
    intro n ω
    exact (congrFun (hrepD n) ω).symm
  let qBound (n : Fin (N + 1)) (j : Fin J) := FangqingBoundedFactor.boundedFactor R (qZ n j)
  let qZS (n : Fin (N + 1)) (j : Fin J) (x : Side Ω G × ℕ × (Fin m → E)) :=
    qBound n j (x.1.val, x.2)
  have hqZS : ∀ n j, Measurable (qZS n j) := by
    intro n j
    have hqb : @Measurable (Ω × ℕ × (Fin m → E)) E (G.prod inferInstance) mE (qBound n j) :=
      (FangqingBoundedFactor.measurable_clip R).comp (hqZ n j)
    exact hqb.comp (measurable_down_pair G)
  let Z (n : Fin (N + 1)) (j : Fin J) := candidate (qZS n j) D (time n)
  have hZM : ∀ n j,
      Measurable[MeasurableSpace.comap (view D (time n)) inferInstance] (Z n j) :=
    fun n j => candidate_measurable (qZS n j) (hqZS n j) D (time n)
  have hZnorm : ∀ n j (seed : Side Ω G) (g : FangqingOrthogonalHaar.Group E),
      ‖Z n j (seed, FangqingAdaptiveHaarProduct.frame (FangqingAdaptiveHaarConcrete.basisPrefix b hmd) g)‖ ≤ R := by
    intro n j seed g
    exact FangqingBoundedFactor.norm_clip_le R hR.le _
  have hZrep : ∀ n j ω, Z n j (Side.mk ω, V ω) = Zorig n j ω := by
    intro n j ω
    change FangqingBoundedFactor.boundedFactor R (qZ n j)
      (ω, count D (time n) (Side.mk ω) (V ω),
        mask (count D (time n) (Side.mk ω) (V ω)) (V ω)) = Zorig n j ω
    rw [hcount]
    have hfac : qZ n j (ω, prefixInfo K V (time n) ω) = Zorig n j ω :=
      (congrFun (hrepZ n j) ω).symm
    unfold FangqingBoundedFactor.boundedFactor
    change FangqingBoundedFactor.clip R (qZ n j (ω, prefixInfo K V (time n) ω)) = Zorig n j ω
    rw [hfac]
    exact FangqingBoundedFactor.clip_eq_self_of_norm_le R _ (hZR n j ω)
  have hlift := measurable_lift G hG
  have hInd : IndepFun (Side.mk : Ω → Side Ω G) V μ := by
    change @Indep Ω
      ((inferInstance : MeasurableSpace (Side Ω G)).comap (Side.mk : Ω → Side Ω G))
      ((inferInstance : MeasurableSpace (Fin m → E)).comap V) mΩ μ
    rw [lift_comap]
    exact hind
  have hb := independent_original_space_bound μ Side.mk V hlift hV hInd b hmd hlaw
    D hDP hDM N J time Z hZM R s hR hs hZnorm
  have hevent : (fun ω => (Side.mk ω, V ω)) ⁻¹'
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m, rawBad D (time n) (Z n j) s i) =
      (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        {ω | K (time n) ω ≤ i.val ∧ s < |inner ℝ (V ω i) (Zorig n j ω)|}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, rawBad, Set.mem_setOf_eq]
    simp_rw [hcount, hZrep]
  rw [hevent] at hb
  exact hb

end

end FangqingAdaptiveHaarExternal
end

section
-- Source component: PrefixOracleReplay.lean

/- Actual finite oracle execution, predictable prefix disclosure, and
   deterministic real/virtual replay.  No concentration or chamber-
   avoidance conclusion is assumed to prove prefix measurability. -/

open MeasureTheory

namespace OriginalPrefixOracleReplay

variable {Seed E Q A : Type*} {m : ℕ}

abbrev State (A : Type*) := ℕ × (ℕ → A)
abbrev Query (Seed A Q : Type*) := ℕ → Seed → State A → Q
abbrev Decision (Seed A Q : Type*) := ℕ → Seed → State A → Q → Bool
abbrev Reply (Seed E A Q : Type*) (m : ℕ) :=
  ℕ → Seed → State A → ℕ → (Fin m → E) → Q → A

def advance (m k : ℕ) (b : Bool) : ℕ :=
  if k < m ∧ b = true then k + 1 else k

theorem advance_bounds (m k : ℕ) (b : Bool) :
    k ≤ advance m k b ∧ advance m k b ≤ k + 1 := by
  simp only [advance]
  split_ifs <;> omega

def transition (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (n : ℕ) (seed : Seed) (V : Fin m → E)
    (st : State A) : State A :=
  let z := q n seed st
  let k := advance m st.1 (d n seed st z)
  (k, Function.update st.2 n (r n seed st k V z))

def run [Zero A] (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) : ℕ → Seed → (Fin m → E) → State A
  | 0, _, _ => (0, 0)
  | n + 1, seed, V => transition q d r n seed V (run q d r n seed V)

theorem run_count_step_bounds [Zero A]
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (n : ℕ) (seed : Seed) (V : Fin m → E) :
    (run q d r n seed V).1 ≤ (run q d r (n + 1) seed V).1 ∧
      (run q d r (n + 1) seed V).1 ≤ (run q d r n seed V).1 + 1 := by
  exact advance_bounds m _ _

theorem run_count_le [Zero A]
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (n : ℕ) (seed : Seed) (V : Fin m → E) :
    (run q d r n seed V).1 ≤ m := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      change advance m _ _ ≤ m
      simp only [advance]
      split_ifs <;> omega

theorem run_count_growth [Zero A]
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (a t : ℕ) (seed : Seed) (V : Fin m → E) :
    (run q d r (a + t) seed V).1 ≤ (run q d r a seed V).1 + t := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hs := (run_count_step_bounds q d r (a + t) seed V).2
      simpa only [Nat.add_assoc] using hs.trans (Nat.add_le_add_right ih 1)

section Prefix

variable [Zero E] [Zero A]

def maskedReply (r : Reply Seed E A Q m) : Reply Seed E A Q m :=
  fun n seed st k V z => r n seed st k (FangqingPrefixAdaptedModel.mask k V) z

def virtualRun (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) := run q d (maskedReply r)

theorem agreePrefix_mask (k : ℕ) (V : Fin m → E) :
    FangqingPrefixProtocol.agreePrefix k V (FangqingPrefixAdaptedModel.mask k V) := by
  intro i hi
  simp only [FangqingPrefixAdaptedModel.mask, if_pos hi]

theorem virtual_state_prefix_invariant
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (n : ℕ) (seed : Seed) (V W : Fin m → E)
    (h : FangqingPrefixProtocol.agreePrefix (virtualRun q d r n seed V).1 V W) :
    virtualRun q d r n seed V = virtualRun q d r n seed W := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hmono := (run_count_step_bounds q d (maskedReply r) n seed V).1
      have hsmall : FangqingPrefixProtocol.agreePrefix (virtualRun q d r n seed V).1 V W :=
        FangqingPrefixProtocol.agreePrefix_mono h hmono
      have hp := ih hsmall
      have hm : FangqingPrefixAdaptedModel.mask (virtualRun q d r (n + 1) seed V).1 V =
          FangqingPrefixAdaptedModel.mask (virtualRun q d r (n + 1) seed V).1 W :=
        FangqingPrefixAdaptedModel.mask_agree _ V W h
      change transition q d (maskedReply r) n seed V (virtualRun q d r n seed V) =
        transition q d (maskedReply r) n seed W (virtualRun q d r n seed W)
      rw [← hp]
      dsimp only [transition, maskedReply]
      congr 2
      exact congrArg (fun U => r n seed (virtualRun q d r n seed V)
        (virtualRun q d r (n + 1) seed V).1 U (q n seed (virtualRun q d r n seed V))) hm

theorem virtual_state_replay_from_mask
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (n : ℕ) (seed : Seed) (V : Fin m → E) :
    virtualRun q d r n seed V = virtualRun q d r n seed
      (FangqingPrefixAdaptedModel.mask (virtualRun q d r n seed V).1 V) := by
  exact virtual_state_prefix_invariant q d r n seed V _ (agreePrefix_mask _ V)

def prefixView (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (n : ℕ) (x : Seed × (Fin m → E)) :
    Seed × ℕ × (Fin m → E) :=
  let k := (virtualRun q d r n x.1 x.2).1
  (x.1, k, FangqingPrefixAdaptedModel.mask k x.2)

def stateFactor (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (n : ℕ) (x : Seed × ℕ × (Fin m → E)) : State A :=
  virtualRun q d r n x.1 x.2.2

theorem stateFactor_representation
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (n : ℕ) (x : Seed × (Fin m → E)) :
    stateFactor q d r n (prefixView q d r n x) = virtualRun q d r n x.1 x.2 := by
  exact (virtual_state_replay_from_mask q d r n x.1 x.2).symm

end Prefix

section Measurability

variable [Zero E] [Zero A]
  [MeasurableSpace Seed] [MeasurableSpace E] [MeasurableSpace Q] [MeasurableSpace A]

theorem run_measurable
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × State A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Seed × State A × Q => d n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
    (n : ℕ) : Measurable (fun x : Seed × (Fin m → E) => run q d r n x.1 x.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hz := (hq n).comp (measurable_fst.prodMk ih)
      have hb := (hd n).comp (measurable_fst.prodMk (ih.prodMk hz))
      have hk : Measurable (fun x : Seed × (Fin m → E) =>
          advance m (run q d r n x.1 x.2).1 (d n x.1 (run q d r n x.1 x.2)
            (q n x.1 (run q d r n x.1 x.2)))) := by
        apply Measurable.ite
          ((measurableSet_lt (measurable_fst.comp ih) measurable_const).inter
            (hb (measurableSet_singleton true)))
          ((measurable_fst.comp ih).add_const 1) (measurable_fst.comp ih)
      have ha := (hr n).comp (measurable_fst.prodMk
        (ih.prodMk (hk.prodMk (measurable_snd.prodMk hz))))
      apply hk.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = n
      · subst i
        convert! ha using 1
        funext x
        simp [run, transition, Function.update_apply]
      · convert! ((measurable_pi_apply i).comp (measurable_snd.comp ih)) using 1
        funext x
        simp [run, transition, Function.update_apply, hi]

theorem maskedReply_measurable
    (r : Reply Seed E A Q m)
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2)) :
    ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      maskedReply r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  intro n
  have hm : Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      (x.1, x.2.1, x.2.2.1, FangqingPrefixAdaptedModel.mask x.2.2.1 x.2.2.2.1,
        x.2.2.2.2)) := by
    apply measurable_fst.prodMk
    apply (measurable_fst.comp measurable_snd).prodMk
    apply (measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      apply Measurable.ite
        (measurableSet_lt measurable_const
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
        ((measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))
        measurable_const
    · exact measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  convert! (hr n).comp hm using 1

theorem virtual_history_and_query_measurable_from_prefix
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × State A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Seed × State A × Q => d n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
    (n : ℕ) :
    Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => virtualRun q d r n x.1 x.2) ∧
    Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => q n x.1 (virtualRun q d r n x.1 x.2)) := by
  have hrun := run_measurable q d (maskedReply r) hq hd (maskedReply_measurable r hr) n
  have hf : Measurable (stateFactor q d r n) :=
    hrun.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hst := hf.comp (comap_measurable (prefixView q d r n))
  have hseed : Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => x.1) := by
    have hh := (measurable_fst : Measurable (fun x : Seed × ℕ × (Fin m → E) => x.1)).comp
      (comap_measurable (prefixView q d r n))
    convert! hh using 1
  have hstate : Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => virtualRun q d r n x.1 x.2) := by
    convert hst using 1
    funext x
    exact (stateFactor_representation q d r n x).symm
  exact ⟨hstate, (hq n).comp (hseed.prodMk hstate)⟩

theorem virtual_decision_and_terminal_measurable_from_prefix
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × State A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Seed × State A × Q => d n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
    (out : Seed → State A → Q)
    (hout : Measurable (fun x : Seed × State A => out x.1 x.2)) (n : ℕ) :
    Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => d n x.1 (virtualRun q d r n x.1 x.2)
        (q n x.1 (virtualRun q d r n x.1 x.2))) ∧
    Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => out x.1 (virtualRun q d r n x.1 x.2)) := by
  obtain ⟨hs, hqv⟩ := virtual_history_and_query_measurable_from_prefix q d r hq hd hr n
  have hx : Measurable[MeasurableSpace.comap (prefixView q d r n) inferInstance]
      (fun x : Seed × (Fin m → E) => x.1) := by
    convert! (measurable_fst : Measurable (fun x : Seed × ℕ × (Fin m → E) => x.1)).comp
      (comap_measurable (prefixView q d r n)) using 1
  exact ⟨(hd n).comp (hx.prodMk (hs.prodMk hqv)), hout.comp (hx.prodMk hs)⟩

def originalCount {Ω : Type*} (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (X : Ω → Seed) (V : Ω → (Fin m → E))
    (n : ℕ) (ω : Ω) : ℕ := (virtualRun q d r n (X ω) (V ω)).1

def originalDecision {Ω : Type*} (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (X : Ω → Seed) (V : Ω → (Fin m → E))
    (n : ℕ) (ω : Ω) : Bool :=
  let st := virtualRun q d r n (X ω) (V ω)
  d n (X ω) st (q n (X ω) st)

def originalPrefixInfo {Ω : Type*} (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (X : Ω → Seed) (V : Ω → (Fin m → E))
    (n : ℕ) (ω : Ω) : ℕ × (Fin m → E) :=
  (originalCount q d r X V n ω,
    FangqingPrefixAdaptedModel.mask (originalCount q d r X V n ω) (V ω))

theorem original_count_protocol {Ω : Type*}
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (X : Ω → Seed) (V : Ω → (Fin m → E)) :
    (∀ ω, originalCount q d r X V 0 ω = 0) ∧
    (∀ n ω, originalCount q d r X V (n + 1) ω =
      if originalCount q d r X V n ω < m ∧ originalDecision q d r X V n ω = true
      then originalCount q d r X V n ω + 1 else originalCount q d r X V n ω) := by
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem original_space_prequery_measurable
    {Ω : Type*} (G : MeasurableSpace Ω)
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × State A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Seed × State A × Q => d n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
    (X : Ω → Seed) (hX : @Measurable Ω Seed G inferInstance X)
    (V : Ω → (Fin m → E)) (n : ℕ) :
    let info := originalPrefixInfo q d r X V n
    let pre := G ⊔ MeasurableSpace.comap info inferInstance
    @Measurable Ω (State A) pre inferInstance (fun ω => virtualRun q d r n (X ω) (V ω)) ∧
    @Measurable Ω Q pre inferInstance
      (fun ω => q n (X ω) (virtualRun q d r n (X ω) (V ω))) ∧
    @Measurable Ω Bool pre inferInstance (originalDecision q d r X V n) := by
  dsimp only
  let info := originalPrefixInfo q d r X V n
  let pre := G ⊔ MeasurableSpace.comap info inferInstance
  have hXs : @Measurable Ω Seed pre inferInstance X := hX.mono le_sup_left le_rfl
  have hinfo : @Measurable Ω (ℕ × (Fin m → E)) pre inferInstance info :=
    (comap_measurable info).mono le_sup_right le_rfl
  have hv : @Measurable Ω (Seed × ℕ × (Fin m → E)) pre inferInstance
      (fun ω => (X ω, info ω)) := hXs.prodMk hinfo
  have hrun := run_measurable q d (maskedReply r) hq hd (maskedReply_measurable r hr) n
  have hf : Measurable (stateFactor q d r n) :=
    hrun.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have hs : @Measurable Ω (State A) pre inferInstance
      (fun ω => virtualRun q d r n (X ω) (V ω)) := by
    convert! hf.comp hv using 1
    funext ω
    change virtualRun q d r n (X ω) (V ω) = virtualRun q d r n (X ω)
      (FangqingPrefixAdaptedModel.mask (virtualRun q d r n (X ω) (V ω)).1 (V ω))
    exact (virtual_state_replay_from_mask q d r n (X ω) (V ω))
  have hquery := (hq n).comp (hXs.prodMk hs)
  exact ⟨hs, hquery, (hd n).comp (hXs.prodMk (hs.prodMk hquery))⟩

end Measurability

section Replay

variable [Zero E] [Zero A]

theorem real_virtual_execution_replay
    (q : Query Seed A Q) (d : Decision Seed A Q)
    (realReply virtualReply : Reply Seed E A Q m)
    (N : ℕ) (seed : Seed) (V : Fin m → E)
    (hlocal : ∀ n < N,
      let st := virtualRun q d virtualReply n seed V
      let z := q n seed st
      let k := advance m st.1 (d n seed st z)
      realReply n seed st k V z =
        virtualReply n seed st k (FangqingPrefixAdaptedModel.mask k V) z) :
    (∀ n ≤ N, run q d realReply n seed V = virtualRun q d virtualReply n seed V) ∧
      (∀ n < N, q n seed (run q d realReply n seed V) =
        q n seed (virtualRun q d virtualReply n seed V)) := by
  have hall : ∀ n ≤ N, run q d realReply n seed V = virtualRun q d virtualReply n seed V := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        have hp := ih (by omega)
        change transition q d realReply n seed V (run q d realReply n seed V) =
          transition q d (maskedReply virtualReply) n seed V
            (virtualRun q d virtualReply n seed V)
        rw [hp]
        dsimp only [transition, maskedReply]
        rw [hlocal n (by omega)]
  exact ⟨hall, fun n hn => congrArg (q n seed) (hall n (by omega))⟩

theorem terminal_output_replay
    (q : Query Seed A Q) (d : Decision Seed A Q)
    (realReply virtualReply : Reply Seed E A Q m)
    (out : Seed → State A → Q) (N : ℕ) (seed : Seed) (V : Fin m → E)
    (hlocal : ∀ n < N,
      let st := virtualRun q d virtualReply n seed V
      let z := q n seed st
      let k := advance m st.1 (d n seed st z)
      realReply n seed st k V z =
        virtualReply n seed st k (FangqingPrefixAdaptedModel.mask k V) z) :
    out seed (run q d realReply N seed V) = out seed (virtualRun q d virtualReply N seed V) := by
  exact congrArg (out seed)
    ((real_virtual_execution_replay q d realReply virtualReply N seed V hlocal).1 N le_rfl)

theorem chamber_hit_requires_serial_responses
    (q : Query Seed A Q) (d : Decision Seed A Q) (r : Reply Seed E A Q m)
    (seed : Seed) (V : Fin m → E) (a t threshold : ℕ)
    (hactivation : (virtualRun q d r a seed V).1 = 0)
    (hit : Q → Prop)
    (hseparation : ∀ n, hit (q n seed (virtualRun q d r n seed V)) →
      threshold ≤ (virtualRun q d r n seed V).1)
    (hhit : hit (q (a + t) seed (virtualRun q d r (a + t) seed V))) :
    threshold ≤ t := by
  have hg := run_count_growth q d (maskedReply r) a t seed V
  have hs := hseparation (a + t) hhit
  change (virtualRun q d r (a + t) seed V).1 ≤ (virtualRun q d r a seed V).1 + t at hg
  rw [hactivation, zero_add] at hg
  exact hs.trans hg

end Replay

section FirstHit

/- firstHitUntil N b scans the actual N query slots 0,...,N-1.
   It returns N when none of those slots is a hit. -/
def firstHitUntil : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 0
  | N + 1, b => if b 0 = true then 0 else firstHitUntil N (fun n => b (n + 1)) + 1

theorem firstHitUntil_le (N : ℕ) (b : ℕ → Bool) : firstHitUntil N b ≤ N := by
  induction N generalizing b with
  | zero => simp [firstHitUntil]
  | succ N ih =>
      simp only [firstHitUntil]
      split_ifs
      · omega
      · exact Nat.add_le_add_right (ih _) 1

theorem firstHitUntil_eq_of_queries_equal
    (N : ℕ) (b c : ℕ → Bool) (h : ∀ n < N, b n = c n) :
    firstHitUntil N b = firstHitUntil N c := by
  induction N generalizing b c with
  | zero => rfl
  | succ N ih =>
      have h0 := h 0 (by omega)
      simp only [firstHitUntil, h0]
      split_ifs
      · rfl
      · rw [ih (fun n => b (n + 1)) (fun n => c (n + 1))
          (fun n hn => h (n + 1) (by omega))]

theorem firstHitUntil_lower_bound
    (N a : ℕ) (b : ℕ → Bool) (ha : a ≤ N)
    (hno : ∀ n < a, b n = false) : a ≤ firstHitUntil N b := by
  induction N generalizing a b with
  | zero => simp_all [firstHitUntil]
  | succ N ih =>
      by_cases hz : a = 0
      · omega
      · have h0 := hno 0 (by omega)
        simp only [firstHitUntil, h0, Bool.false_eq_true, if_false]
        have hh := ih (a - 1) (fun n => b (n + 1)) (by omega)
          (fun n hn => hno (n + 1) (by omega))
        omega

theorem actual_activation_time_replay [Zero E] [Zero A]
    (q : Query Seed A Q) (d : Decision Seed A Q)
    (realReply virtualReply : Reply Seed E A Q m)
    (hit : Q → Bool) (N : ℕ) (seed : Seed) (V : Fin m → E)
    (hlocal : ∀ n < N,
      let st := virtualRun q d virtualReply n seed V
      let z := q n seed st
      let k := advance m st.1 (d n seed st z)
      realReply n seed st k V z =
        virtualReply n seed st k (FangqingPrefixAdaptedModel.mask k V) z) :
    firstHitUntil N (fun n => hit (q n seed (run q d realReply n seed V))) =
      firstHitUntil N (fun n => hit (q n seed (virtualRun q d virtualReply n seed V))) := by
  apply firstHitUntil_eq_of_queries_equal
  intro n hn
  exact congrArg hit ((real_virtual_execution_replay q d realReply virtualReply N seed V hlocal).2 n hn)

end FirstHit

end OriginalPrefixOracleReplay
end

section
-- Source component: PrefixOracleHaarBridge.lean

/- Haar concentration for candidates generated by the actual virtual
   execution. Prefix-adapted history/decisions are derived, not assumed.
   This is an execution/concentration bridge; actual packet geometry
   must still instantiate the reply and the candidate maps. -/

open MeasureTheory ProbabilityTheory

namespace OriginalPrefixOracleHaarBridge

open OriginalPrefixOracleReplay

variable {Ω Seed E Q A : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace Seed] [MeasurableSpace Q] [MeasurableSpace A] [Zero A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {m d : ℕ}

noncomputable def zeroClip (R : ℝ) (z : E) : E := if ‖z‖ ≤ R then z else 0

theorem zeroClip_measurable (R : ℝ) : Measurable (zeroClip (E := E) R) := by
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const) measurable_id measurable_const

theorem zeroClip_bound (R : ℝ) (hR : 0 ≤ R) (z : E) : ‖zeroClip R z‖ ≤ R := by
  by_cases hz : ‖z‖ ≤ R
  · simpa only [zeroClip, if_pos hz] using hz
  · simpa only [zeroClip, if_neg hz, norm_zero] using hR

theorem zeroClip_eq (R : ℝ) (z : E) (hz : ‖z‖ ≤ R) : zeroClip R z = z := by
  simp only [zeroClip, if_pos hz]

def queryOrTerminal (q : Query Seed A Q) (out : Seed → State A → Q)
    (N : ℕ) (n : Fin (N + 1)) (seed : Seed) (st : State A) : Q :=
  if n.val < N then q n.val seed st else out seed st

noncomputable def candidates (q : Query Seed A Q) (d : Decision Seed A Q)
    (r : Reply Seed E A Q m) (out : Seed → State A → Q)
    (X : Ω → Seed) (V : Ω → (Fin m → E))
    (N J : ℕ) (components : Fin J → Q → E) (R : ℝ)
    (n : Fin (N + 1)) (j : Fin J) (ω : Ω) : E :=
  zeroClip R (components j (queryOrTerminal q out N n (X ω)
    (virtualRun q d r n.val (X ω) (V ω))))

theorem generated_candidates_and_disclosure_haar_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (X : Ω → Seed) (hX : @Measurable Ω Seed G inferInstance X)
    (V : Ω → (Fin m → E))
    (hV : @Measurable Ω (Fin m → E) mΩ inferInstance V)
    (hind : @Indep Ω G ((inferInstance : MeasurableSpace (Fin m → E)).comap V) mΩ μ)
    (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (hlaw : @Measure.map Ω (Fin m → E) mΩ inferInstance V μ =
      FangqingAdaptiveHaarOriginal.frameLaw b hmd)
    (q : Query Seed A Q) (dec : Decision Seed A Q) (r : Reply Seed E A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × State A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Seed × State A × Q => dec n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable (fun x : Seed × State A × ℕ × (Fin m → E) × Q =>
      r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2))
    (out : Seed → State A → Q)
    (hout : Measurable (fun x : Seed × State A => out x.1 x.2))
    (N J : ℕ) (components : Fin J → Q → E) (hc : ∀ j, Measurable (components j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s) :
    FangqingAdaptiveHaarExternal.HaarConclusion
      (μ.real (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        {ω | originalCount q dec r X V n.val ω ≤ i.val ∧
          s < |inner ℝ (V ω i) (candidates q dec r out X V N J components R n j ω)|}))
      d m N J R s := by
  let K := originalCount q dec r X V
  let D := originalDecision q dec r X V
  let U (n : ℕ) (ω : Ω) := virtualRun q dec r n (X ω) (V ω)
  have hp := original_count_protocol q dec r X V
  have hinfo (n : ℕ) := original_space_prequery_measurable G q dec r hq hd hr X hX V n
  have hU : ∀ n, @Measurable Ω (State A)
      (G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap
        (FangqingAdaptiveHaarExternal.prefixInfo K V n)) inferInstance (U n) := by
    intro n
    exact (hinfo n).1
  have hD : ∀ n, @Measurable Ω Bool
      ((G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap
        (FangqingAdaptiveHaarExternal.prefixInfo K V n)) ⊔
        MeasurableSpace.comap (U n) inferInstance) inferInstance (D n) := by
    intro n
    exact ((hinfo n).2.2).mono le_sup_left le_rfl
  have hZ : ∀ n j, @Measurable Ω E
      ((G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap
        (FangqingAdaptiveHaarExternal.prefixInfo K V n.val)) ⊔
        MeasurableSpace.comap (U n.val) inferInstance) inferInstance
      (candidates q dec r out X V N J components R n j) := by
    intro n j
    let pre := G ⊔ (inferInstance : MeasurableSpace (ℕ × (Fin m → E))).comap
      (FangqingAdaptiveHaarExternal.prefixInfo K V n.val)
    have hx : @Measurable Ω Seed pre inferInstance X := hX.mono le_sup_left le_rfl
    have hz : @Measurable Ω Q pre inferInstance
        (fun ω => queryOrTerminal q out N n (X ω) (U n.val ω)) := by
      by_cases hn : n.val < N
      · simp only [queryOrTerminal, if_pos hn]
        convert! (hinfo n.val).2.1 using 1
      · have ho := hout.comp (hx.prodMk (hU n.val))
        simp only [queryOrTerminal, if_neg hn]
        convert! ho using 1
    exact ((zeroClip_measurable R).comp ((hc j).comp hz)).mono le_sup_left le_rfl
  exact FangqingAdaptiveHaarExternal.arbitrary_external_sigma_complete (mΩ := mΩ) μ G hG V hV hind b hmd hlaw
    K D U hp.1 hp.2 hU hD N J (fun n => n.val)
    (candidates q dec r out X V N J components R) hZ R s hR hs
    (fun _ _ _ => zeroClip_bound R hR.le _)

end OriginalPrefixOracleHaarBridge
end

section
-- Source component: TwoGroupPrefixExecution.lean

/- A single actual execution with a private A-handle and a separate
   W-tail. The algorithm receives only its seed and response history.
   Conditioning-side data is not an extra algorithm input. At the
   activation response only the handle is granted; subsequent responses
   grant one tail column unconditionally. -/

open MeasureTheory

namespace OriginalTwoGroupPrefixExecution

variable {Seed Side H W Q A : Type*} {m : ℕ}

abbrev History (A : Type*) := ℕ → A
abbrev State (A : Type*) := ℕ × ℕ × History A
abbrev Query (Seed A Q : Type*) := ℕ → Seed → History A → Q
abbrev Activation (Side A Q : Type*) := ℕ → Side → State A → Q → Bool
abbrev Reply (Seed Side H W A Q : Type*) (m : ℕ) :=
  ℕ → Seed → Side → State A → ℕ → ℕ → (Fin 1 → H) → (Fin m → W) → Q → A

def tailDecision (st : State A) : Bool := decide (0 < st.1)

def nextHandle (dec : Activation Side A Q) (n : ℕ) (side : Side) (st : State A) (z : Q) : ℕ :=
  OriginalPrefixOracleReplay.advance 1 st.1 (dec n side st z)

def nextTail (st : State A) : ℕ := OriginalPrefixOracleReplay.advance m st.2.1 (tailDecision st)

def step [Zero H] [Zero W]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (st : State A) : State A :=
  let z := q n seed st.2.2
  let kh := nextHandle dec n side st z
  let kt := nextTail (m := m) st
  (kh, kt, Function.update st.2.2 n
    (r n seed side st kh kt (FangqingPrefixAdaptedModel.mask kh handle)
      (FangqingPrefixAdaptedModel.mask kt tail) z))

def run [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m) :
    ℕ → Seed → Side → (Fin 1 → H) → (Fin m → W) → State A
  | 0, _, _, _, _ => (0, 0, 0)
  | n + 1, seed, side, handle, tail =>
      step q dec r n seed side handle tail (run q dec r n seed side handle tail)

theorem count_step_bounds [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W) :
    let st := run q dec r n seed side handle tail
    let st' := run q dec r (n + 1) seed side handle tail
    st.1 ≤ st'.1 ∧ st'.1 ≤ st.1 + 1 ∧ st.2.1 ≤ st'.2.1 ∧ st'.2.1 ≤ st.2.1 + 1 := by
  have hh := OriginalPrefixOracleReplay.advance_bounds 1
    (run q dec r n seed side handle tail).1
    (dec n side (run q dec r n seed side handle tail)
      (q n seed (run q dec r n seed side handle tail).2.2))
  have ht := OriginalPrefixOracleReplay.advance_bounds m
    (run q dec r n seed side handle tail).2.1 (tailDecision (run q dec r n seed side handle tail))
  exact ⟨hh.1, hh.2, ht.1, ht.2⟩

theorem counts_bounded [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W) :
    (run q dec r n seed side handle tail).1 ≤ 1 ∧
      (run q dec r n seed side handle tail).2.1 ≤ m := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      change OriginalPrefixOracleReplay.advance 1 _ _ ≤ 1 ∧
        OriginalPrefixOracleReplay.advance m _ _ ≤ m
      constructor <;> simp only [OriginalPrefixOracleReplay.advance] <;> split_ifs <;> omega

theorem activation_response_grants_no_tail [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hbefore : (run q dec r n seed side handle tail).1 = 0) :
    (run q dec r (n + 1) seed side handle tail).2.1 =
      (run q dec r n seed side handle tail).2.1 := by
  change OriginalPrefixOracleReplay.advance m _ (tailDecision _) = _
  simp only [tailDecision, hbefore, lt_self_iff_false, decide_false,
    OriginalPrefixOracleReplay.advance, Bool.false_eq_true, and_false, if_false]

theorem post_activation_tail_schedule [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hactive : (run q dec r n seed side handle tail).1 = 1) :
    (run q dec r (n + 1) seed side handle tail).2.1 =
      if (run q dec r n seed side handle tail).2.1 < m
      then (run q dec r n seed side handle tail).2.1 + 1
      else (run q dec r n seed side handle tail).2.1 := by
  change OriginalPrefixOracleReplay.advance m _ (tailDecision _) = _
  simp only [tailDecision, hactive, Nat.zero_lt_one, decide_true,
    OriginalPrefixOracleReplay.advance, and_true]

theorem handle_prefix_replay [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle handle' : Fin 1 → H) (tail : Fin m → W)
    (h : FangqingPrefixProtocol.agreePrefix (run q dec r n seed side handle tail).1 handle handle') :
    run q dec r n seed side handle tail = run q dec r n seed side handle' tail := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hs := count_step_bounds q dec r n seed side handle tail
      have hp := ih (FangqingPrefixProtocol.agreePrefix_mono h hs.1)
      have hm := FangqingPrefixAdaptedModel.mask_agree _ handle handle' h
      change step q dec r n seed side handle tail (run q dec r n seed side handle tail) =
        step q dec r n seed side handle' tail (run q dec r n seed side handle' tail)
      rw [← hp]
      dsimp only [step]
      congr 3
      exact congrArg (fun hh => r n seed side (run q dec r n seed side handle tail)
        (run q dec r (n + 1) seed side handle tail).1
        (run q dec r (n + 1) seed side handle tail).2.1 hh
        (FangqingPrefixAdaptedModel.mask (run q dec r (n + 1) seed side handle tail).2.1 tail)
        (q n seed (run q dec r n seed side handle tail).2.2)) hm

theorem tail_prefix_replay [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail tail' : Fin m → W)
    (h : FangqingPrefixProtocol.agreePrefix (run q dec r n seed side handle tail).2.1 tail tail') :
    run q dec r n seed side handle tail = run q dec r n seed side handle tail' := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hs := count_step_bounds q dec r n seed side handle tail
      have hp := ih (FangqingPrefixProtocol.agreePrefix_mono h hs.2.2.1)
      have hm := FangqingPrefixAdaptedModel.mask_agree _ tail tail' h
      change step q dec r n seed side handle tail (run q dec r n seed side handle tail) =
        step q dec r n seed side handle tail' (run q dec r n seed side handle tail')
      rw [← hp]
      dsimp only [step]
      congr 3
      exact congrArg (fun tt => r n seed side (run q dec r n seed side handle tail)
        (run q dec r (n + 1) seed side handle tail).1
        (run q dec r (n + 1) seed side handle tail).2.1
        (FangqingPrefixAdaptedModel.mask (run q dec r (n + 1) seed side handle tail).1 handle) tt
        (q n seed (run q dec r n seed side handle tail).2.2)) hm

theorem two_group_replay_from_actual_prefixes [Zero H] [Zero W] [Zero A]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W) :
    run q dec r n seed side handle tail = run q dec r n seed side
      (FangqingPrefixAdaptedModel.mask (run q dec r n seed side handle tail).1 handle)
      (FangqingPrefixAdaptedModel.mask (run q dec r n seed side handle tail).2.1 tail) := by
  have hh := handle_prefix_replay q dec r n seed side handle _ tail
    (OriginalPrefixOracleReplay.agreePrefix_mask _ handle)
  have ht := tail_prefix_replay q dec r n seed side
    (FangqingPrefixAdaptedModel.mask (run q dec r n seed side handle tail).1 handle) tail
    (FangqingPrefixAdaptedModel.mask (run q dec r n seed side handle tail).2.1 tail)
  rw [← hh] at ht
  exact ht (OriginalPrefixOracleReplay.agreePrefix_mask _ tail)

section Measurability

variable [Zero H] [Zero W] [Zero A]
  [MeasurableSpace Seed] [MeasurableSpace Side] [MeasurableSpace H]
  [MeasurableSpace W] [MeasurableSpace Q] [MeasurableSpace A]

abbrev Input (Seed Side H W : Type*) (m : ℕ) := (Seed × Side) × (Fin 1 → H) × (Fin m → W)

theorem mask_measurable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [Zero E]
    {k : ℕ} (K : Ω → ℕ) (V : Ω → (Fin k → E)) (hK : Measurable K) (hV : Measurable V) :
    Measurable (fun ω => FangqingPrefixAdaptedModel.mask (K ω) (V ω)) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_lt measurable_const hK)
    ((measurable_pi_apply i).comp hV) measurable_const

theorem run_measurable
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × History A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Side × State A × Q => dec n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable
      (fun x : Seed × Side × State A × ℕ × ℕ × (Fin 1 → H) × (Fin m → W) × Q =>
        r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2))
    (n : ℕ) : Measurable (fun x : Input Seed Side H W m =>
      run q dec r n x.1.1 x.1.2 x.2.1 x.2.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hseed : Measurable (fun x : Input Seed Side H W m => x.1.1) :=
        measurable_fst.comp measurable_fst
      have hside : Measurable (fun x : Input Seed Side H W m => x.1.2) :=
        measurable_snd.comp measurable_fst
      have hkh := measurable_fst.comp ih
      have hkt := measurable_fst.comp (measurable_snd.comp ih)
      have hhist := measurable_snd.comp (measurable_snd.comp ih)
      have hz := (hq n).comp (hseed.prodMk hhist)
      have hb := (hd n).comp (hside.prodMk (ih.prodMk hz))
      have hnewh : Measurable (fun x : Input Seed Side H W m =>
          nextHandle dec n x.1.2 (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2)
            (q n x.1.1 (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2).2.2)) := by
        apply Measurable.ite
          ((measurableSet_lt hkh measurable_const).inter (hb (measurableSet_singleton true)))
          (hkh.add_const 1) hkh
      have hnewt : Measurable (fun x : Input Seed Side H W m =>
          nextTail (m := m) (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2)) := by
        have hba : Measurable (fun x : Input Seed Side H W m =>
            tailDecision (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2)) := by
          apply Measurable.ite (measurableSet_lt measurable_const hkh) measurable_const measurable_const
        apply Measurable.ite
          ((measurableSet_lt hkt measurable_const).inter (hba (measurableSet_singleton true)))
          (hkt.add_const 1) hkt
      have hmH := mask_measurable _ _ hnewh (measurable_fst.comp measurable_snd)
      have hmT := mask_measurable _ _ hnewt (measurable_snd.comp measurable_snd)
      have ha := (hr n).comp (hseed.prodMk (hside.prodMk (ih.prodMk
        (hnewh.prodMk (hnewt.prodMk (hmH.prodMk (hmT.prodMk hz)))))))
      apply hnewh.prodMk
      apply hnewt.prodMk
      apply measurable_pi_lambda
      intro i
      by_cases hi : i = n
      · subst i
        convert! ha using 1
        funext x
        simp [step, run, Function.update_apply]
      · convert! (measurable_pi_apply i).comp hhist using 1
        funext x
        simp [step, run, Function.update_apply, hi]

def handleView (q : Query Seed A Q) (dec : Activation Side A Q)
    (r : Reply Seed Side H W A Q m) (n : ℕ) (x : Input Seed Side H W m) :
    (Seed × Side × (Fin m → W)) × ℕ × (Fin 1 → H) :=
  let kh := (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2).1
  ((x.1.1, x.1.2, x.2.2), kh, FangqingPrefixAdaptedModel.mask kh x.2.1)

def tailView (q : Query Seed A Q) (dec : Activation Side A Q)
    (r : Reply Seed Side H W A Q m) (n : ℕ) (x : Input Seed Side H W m) :
    (Seed × Side × (Fin 1 → H)) × ℕ × (Fin m → W) :=
  let kt := (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2).2.1
  ((x.1.1, x.1.2, x.2.1), kt, FangqingPrefixAdaptedModel.mask kt x.2.2)

def handleStateFactor (q : Query Seed A Q) (dec : Activation Side A Q)
    (r : Reply Seed Side H W A Q m) (n : ℕ)
    (x : (Seed × Side × (Fin m → W)) × ℕ × (Fin 1 → H)) : State A :=
  run q dec r n x.1.1 x.1.2.1 x.2.2 x.1.2.2

def tailStateFactor (q : Query Seed A Q) (dec : Activation Side A Q)
    (r : Reply Seed Side H W A Q m) (n : ℕ)
    (x : (Seed × Side × (Fin 1 → H)) × ℕ × (Fin m → W)) : State A :=
  run q dec r n x.1.1 x.1.2.1 x.1.2.2 x.2.2

theorem two_group_state_measurable_in_each_disclosed_prefix
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × History A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Side × State A × Q => dec n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable
      (fun x : Seed × Side × State A × ℕ × ℕ × (Fin 1 → H) × (Fin m → W) × Q =>
        r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2))
    (n : ℕ) :
    Measurable[MeasurableSpace.comap (handleView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => run q dec r n x.1.1 x.1.2 x.2.1 x.2.2) ∧
    Measurable[MeasurableSpace.comap (tailView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => run q dec r n x.1.1 x.1.2 x.2.1 x.2.2) := by
  have hrun := run_measurable q dec r hq hd hr n
  have hfH : Measurable (handleStateFactor q dec r n) := by
    exact hrun.comp (((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_snd.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have hfT : Measurable (tailStateFactor q dec r n) := by
    exact hrun.comp (((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_snd)))
  constructor
  · convert! hfH.comp (comap_measurable (handleView q dec r n)) using 1
    funext x
    exact handle_prefix_replay q dec r n x.1.1 x.1.2 x.2.1 _ x.2.2
      (OriginalPrefixOracleReplay.agreePrefix_mask _ x.2.1)
  · convert! hfT.comp (comap_measurable (tailView q dec r n)) using 1
    funext x
    exact tail_prefix_replay q dec r n x.1.1 x.1.2 x.2.1 x.2.2 _
      (OriginalPrefixOracleReplay.agreePrefix_mask _ x.2.2)

theorem chosen_candidate_measurable_in_each_disclosed_prefix
    {F : Type*} [MeasurableSpace F]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × History A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Side × State A × Q => dec n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable
      (fun x : Seed × Side × State A × ℕ × ℕ × (Fin 1 → H) × (Fin m → W) × Q =>
        r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2))
    (choose : Seed × History A → F) (hc : Measurable choose) (n : ℕ) :
    Measurable[MeasurableSpace.comap (handleView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => choose (x.1.1, (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2).2.2)) ∧
    Measurable[MeasurableSpace.comap (tailView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => choose (x.1.1, (run q dec r n x.1.1 x.1.2 x.2.1 x.2.2).2.2)) := by
  obtain ⟨hh, ht⟩ := two_group_state_measurable_in_each_disclosed_prefix q dec r hq hd hr n
  have hhseed : Measurable[MeasurableSpace.comap (handleView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => x.1.1) := by
    convert! (measurable_fst.comp measurable_fst :
      Measurable (fun x : (Seed × Side × (Fin m → W)) × ℕ × (Fin 1 → H) => x.1.1)).comp
        (comap_measurable (handleView q dec r n)) using 1
  have htseed : Measurable[MeasurableSpace.comap (tailView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => x.1.1) := by
    convert! (measurable_fst.comp measurable_fst :
      Measurable (fun x : (Seed × Side × (Fin 1 → H)) × ℕ × (Fin m → W) => x.1.1)).comp
        (comap_measurable (tailView q dec r n)) using 1
  exact ⟨hc.comp (hhseed.prodMk (measurable_snd.comp (measurable_snd.comp hh))),
    hc.comp (htseed.prodMk (measurable_snd.comp (measurable_snd.comp ht)))⟩

end Measurability

section RealReplay

variable [Zero H] [Zero W] [Zero A]

def fullStep
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (n : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (st : State A) : State A :=
  let z := q n seed st.2.2
  let kh := nextHandle dec n side st z
  let kt := nextTail (m := m) st
  (kh, kt, Function.update st.2.2 n (r n seed side st kh kt handle tail z))

def fullRun
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m) :
    ℕ → Seed → Side → (Fin 1 → H) → (Fin m → W) → State A
  | 0, _, _, _, _ => (0, 0, 0)
  | n + 1, seed, side, handle, tail =>
      fullStep q dec r n seed side handle tail (fullRun q dec r n seed side handle tail)

theorem literal_real_virtual_replay
    (q : Query Seed A Q) (dec : Activation Side A Q)
    (realReply virtualReply : Reply Seed Side H W A Q m)
    (N : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hlocal : ∀ n < N,
      let st := run q dec virtualReply n seed side handle tail
      let z := q n seed st.2.2
      let kh := nextHandle dec n side st z
      let kt := nextTail (m := m) st
      realReply n seed side st kh kt handle tail z = virtualReply n seed side st kh kt
        (FangqingPrefixAdaptedModel.mask kh handle) (FangqingPrefixAdaptedModel.mask kt tail) z) :
    (∀ n ≤ N, fullRun q dec realReply n seed side handle tail =
      run q dec virtualReply n seed side handle tail) ∧
    (∀ n < N, q n seed (fullRun q dec realReply n seed side handle tail).2.2 =
      q n seed (run q dec virtualReply n seed side handle tail).2.2) := by
  have hall : ∀ n ≤ N, fullRun q dec realReply n seed side handle tail =
      run q dec virtualReply n seed side handle tail := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
        have hp := ih (by omega)
        change fullStep q dec realReply n seed side handle tail
          (fullRun q dec realReply n seed side handle tail) =
          step q dec virtualReply n seed side handle tail (run q dec virtualReply n seed side handle tail)
        rw [hp]
        dsimp only [fullStep, step]
        rw [hlocal n (by omega)]
  exact ⟨hall, fun n hn => congrArg (fun st => q n seed st.2.2) (hall n (by omega))⟩

theorem literal_first_hit_and_terminal_replay
    (q : Query Seed A Q) (dec : Activation Side A Q)
    (realReply virtualReply : Reply Seed Side H W A Q m)
    (hit : Q → Bool) (out : Seed → History A → Q)
    (N : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hlocal : ∀ n < N,
      let st := run q dec virtualReply n seed side handle tail
      let z := q n seed st.2.2
      let kh := nextHandle dec n side st z
      let kt := nextTail (m := m) st
      realReply n seed side st kh kt handle tail z = virtualReply n seed side st kh kt
        (FangqingPrefixAdaptedModel.mask kh handle) (FangqingPrefixAdaptedModel.mask kt tail) z) :
    OriginalPrefixOracleReplay.firstHitUntil N
      (fun n => hit (q n seed (fullRun q dec realReply n seed side handle tail).2.2)) =
      OriginalPrefixOracleReplay.firstHitUntil N
        (fun n => hit (q n seed (run q dec virtualReply n seed side handle tail).2.2)) ∧
    out seed (fullRun q dec realReply N seed side handle tail).2.2 =
      out seed (run q dec virtualReply N seed side handle tail).2.2 := by
  obtain ⟨hs, hq⟩ := literal_real_virtual_replay q dec realReply virtualReply N seed side handle tail hlocal
  exact ⟨OriginalPrefixOracleReplay.firstHitUntil_eq_of_queries_equal N _ _
      (fun n hn => congrArg hit (hq n hn)),
    congrArg (fun st => out seed st.2.2) (hs N le_rfl)⟩

end RealReplay

end OriginalTwoGroupPrefixExecution
end

section
-- Source component: TwoGroupProductLaw.lean

/- Actual product-measure independence for the two different hidden
   spaces. The side variable for one group may include the other group;
   no false Haar law on their physical direct sum is used. -/

open MeasureTheory ProbabilityTheory

namespace OriginalTwoGroupProductLaw

theorem indepFun_pullback_of_measurePreserving
    {Ω Ω' X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (F : Ω → Ω') (hF : MeasurePreserving F μ ν)
    (f : Ω' → X) (g : Ω' → Y) (hf : Measurable f) (hg : Measurable g)
    (hind : IndepFun f g ν) : IndepFun (f ∘ F) (g ∘ F) μ := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp hF.measurable).aemeasurable (hg.comp hF.measurable).aemeasurable).mpr
  have hx : μ.map (f ∘ F) = ν.map f := by
    rw [← Measure.map_map hf hF.measurable, hF.map_eq]
  have hy : μ.map (g ∘ F) = ν.map g := by
    rw [← Measure.map_map hg hF.measurable, hF.map_eq]
  calc
    μ.map (fun ω => ((f ∘ F) ω, (g ∘ F) ω)) = ν.map (fun ω => (f ω, g ω)) := by
      change μ.map ((fun ω => (f ω, g ω)) ∘ F) = _
      rw [← Measure.map_map (hf.prodMk hg) hF.measurable, hF.map_eq]
    _ = (ν.map f).prod (ν.map g) := hind.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
    _ = (μ.map (f ∘ F)).prod (μ.map (g ∘ F)) := by rw [hx, hy]

theorem handle_side_independent
    {S H T : Type*} [MeasurableSpace S] [MeasurableSpace H] [MeasurableSpace T]
    (σ : Measure S) (νH : Measure H) (νT : Measure T)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure νH] [IsProbabilityMeasure νT] :
    IndepFun (fun ω : S × H × T => (ω.1, ω.2.2))
      (fun ω : S × H × T => ω.2.1) (σ.prod (νH.prod νT)) := by
  have hswap := (MeasurePreserving.id σ).prod
    (Measure.measurePreserving_swap (μ := νH) (ν := νT))
  have hassoc := (measurePreserving_prodAssoc σ νT νH).symm MeasurableEquiv.prodAssoc
  have hF : MeasurePreserving (fun ω : S × H × T => ((ω.1, ω.2.2), ω.2.1))
      (σ.prod (νH.prod νT)) ((σ.prod νT).prod νH) := by
    convert! hassoc.comp hswap using 1
  have hi : IndepFun (Prod.fst : (S × T) × H → S × T) Prod.snd ((σ.prod νT).prod νH) :=
    indepFun_prod measurable_id measurable_id
  exact indepFun_pullback_of_measurePreserving _ _ _ hF _ _ measurable_fst measurable_snd hi

theorem tail_side_independent
    {S H T : Type*} [MeasurableSpace S] [MeasurableSpace H] [MeasurableSpace T]
    (σ : Measure S) (νH : Measure H) (νT : Measure T)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure νH] [IsProbabilityMeasure νT] :
    IndepFun (fun ω : S × H × T => (ω.1, ω.2.1))
      (fun ω : S × H × T => ω.2.2) (σ.prod (νH.prod νT)) := by
  have hF : MeasurePreserving (fun ω : S × H × T => ((ω.1, ω.2.1), ω.2.2))
      (σ.prod (νH.prod νT)) ((σ.prod νH).prod νT) := by
    exact (measurePreserving_prodAssoc σ νH νT).symm MeasurableEquiv.prodAssoc
  have hi : IndepFun (Prod.fst : (S × H) × T → S × H) Prod.snd ((σ.prod νH).prod νT) :=
    indepFun_prod measurable_id measurable_id
  exact indepFun_pullback_of_measurePreserving _ _ _ hF _ _ measurable_fst measurable_snd hi

theorem actual_group_marginal_laws
    {S H T : Type*} [MeasurableSpace S] [MeasurableSpace H] [MeasurableSpace T]
    (σ : Measure S) (νH : Measure H) (νT : Measure T)
    [IsProbabilityMeasure σ] [IsProbabilityMeasure νH] [IsProbabilityMeasure νT] :
    (σ.prod (νH.prod νT)).map (fun ω : S × H × T => ω.2.1) = νH ∧
    (σ.prod (νH.prod νT)).map (fun ω : S × H × T => ω.2.2) = νT := by
  constructor
  · rw [show (fun ω : S × H × T => ω.2.1) = Prod.fst ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]
  · rw [show (fun ω : S × H × T => ω.2.2) = Prod.snd ∘ Prod.snd from rfl,
      ← Measure.map_map measurable_snd measurable_snd, Measure.map_snd_prod,
      measure_univ, one_smul, Measure.map_snd_prod, measure_univ, one_smul]

end OriginalTwoGroupProductLaw
end

section
-- Source component: TwoGroupHaarExecution.lean

/- Two actual Haar calls for the one executed handle/tail protocol.
   The physical mixed frame is never asserted Haar on a direct sum. -/

open MeasureTheory ProbabilityTheory

namespace OriginalTwoGroupHaarExecution

open OriginalTwoGroupPrefixExecution

section ExplicitView

variable {Ω S E A : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] {m d : ℕ}

theorem haar_from_explicit_execution_view
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (V : Ω → (Fin m → E)) (hX : Measurable X) (hV : Measurable V)
    (hind : IndepFun X V μ) (b : OrthonormalBasis (Fin d) ℝ E) (hmd : m ≤ d)
    (hlaw : μ.map V = FangqingAdaptiveHaarOriginal.frameLaw b hmd)
    (K : ℕ → Ω → ℕ) (D : ℕ → Ω → Bool) (U : ℕ → Ω → A)
    (hK0 : ∀ ω, K 0 ω = 0)
    (hKstep : ∀ n ω, K (n + 1) ω = if K n ω < m ∧ D n ω = true then K n ω + 1 else K n ω)
    (hU : ∀ n, Measurable[MeasurableSpace.comap
      (fun ω => (X ω, FangqingAdaptiveHaarExternal.prefixInfo K V n ω))
        (inferInstance : MeasurableSpace (S × ℕ × (Fin m → E)))] (U n))
    (hD : ∀ n, Measurable[MeasurableSpace.comap
      (fun ω => (X ω, FangqingAdaptiveHaarExternal.prefixInfo K V n ω))
        (inferInstance : MeasurableSpace (S × ℕ × (Fin m → E)))] (D n))
    (N J : ℕ) (Z : Fin (N + 1) → Fin J → Ω → E)
    (hZ : ∀ n j, Measurable[MeasurableSpace.comap
      (fun ω => (X ω, FangqingAdaptiveHaarExternal.prefixInfo K V n.val ω))
        (inferInstance : MeasurableSpace (S × ℕ × (Fin m → E)))] (Z n j))
    (R s : ℝ) (hR : 0 < R) (hs : 0 ≤ s) (hZR : ∀ n j ω, ‖Z n j ω‖ ≤ R) :
    FangqingAdaptiveHaarExternal.HaarConclusion
      (μ.real (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        {ω | K n.val ω ≤ i.val ∧ s < |inner ℝ (V ω i) (Z n j ω)|})) d m N J R s := by
  let G := MeasurableSpace.comap X inferInstance
  have heq (n : ℕ) : MeasurableSpace.comap
      (fun ω => (X ω, FangqingAdaptiveHaarExternal.prefixInfo K V n ω))
        (inferInstance : MeasurableSpace (S × ℕ × (Fin m → E))) =
      G ⊔ MeasurableSpace.comap (FangqingAdaptiveHaarExternal.prefixInfo K V n) inferInstance := by
    convert! MeasurableSpace.comap_prodMk X (FangqingAdaptiveHaarExternal.prefixInfo K V n) using 1
  have hU' : ∀ n, Measurable[G ⊔ MeasurableSpace.comap
      (FangqingAdaptiveHaarExternal.prefixInfo K V n) inferInstance] (U n) := by
    intro n
    rw [← heq]
    exact hU n
  have hD' : ∀ n, Measurable[(G ⊔ MeasurableSpace.comap
      (FangqingAdaptiveHaarExternal.prefixInfo K V n) inferInstance) ⊔
        MeasurableSpace.comap (U n) inferInstance] (D n) := by
    intro n
    exact ((heq n) ▸ hD n).mono le_sup_left le_rfl
  have hZ' : ∀ n j, Measurable[(G ⊔ MeasurableSpace.comap
      (FangqingAdaptiveHaarExternal.prefixInfo K V n.val) inferInstance) ⊔
        MeasurableSpace.comap (U n.val) inferInstance] (Z n j) := by
    intro n j
    exact ((heq n.val) ▸ hZ n j).mono le_sup_left le_rfl
  exact FangqingAdaptiveHaarExternal.arbitrary_external_sigma_complete (mΩ := mΩ) μ G hX.comap_le
    V hV hind b hmd hlaw K D U hK0 hKstep hU' hD' N J (fun n => n.val) Z hZ' R s hR hs hZR

end ExplicitView

variable {Seed Side H W Q A : Type*} [MeasurableSpace Seed] [MeasurableSpace Side]
  [MeasurableSpace Q] [MeasurableSpace A] [Zero A]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] [Nontrivial H]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W] {m dH dW : ℕ}

def queryOrOutput (q : Query Seed A Q) (out : Seed → History A → Q)
    (N : ℕ) (n : Fin (N + 1)) (x : Seed × History A) : Q :=
  if n.val < N then q n.val x.1 x.2 else out x.1 x.2

noncomputable def generatedCandidate
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (out : Seed → History A → Q) (N J : ℕ) (components : Fin J → Q → E) (R : ℝ)
    (n : Fin (N + 1)) (j : Fin J) (x : Input Seed Side H W m) : E :=
  OriginalPrefixOracleHaarBridge.zeroClip R (components j
    (queryOrOutput q out N n (x.1.1, (run q dec r n.val x.1.1 x.1.2 x.2.1 x.2.2).2.2)))

noncomputable def packetLaw (σ : Measure (Seed × Side))
    (bH : OrthonormalBasis (Fin dH) ℝ H) (hH : 1 ≤ dH)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : m ≤ dW) : Measure (Input Seed Side H W m) :=
  σ.prod ((FangqingAdaptiveHaarOriginal.frameLaw bH hH).prod
    (FangqingAdaptiveHaarOriginal.frameLaw bW hW))

theorem actual_handle_and_tail_haar_calls
    (σ : Measure (Seed × Side)) [IsProbabilityMeasure σ]
    (bH : OrthonormalBasis (Fin dH) ℝ H) (hH : 1 ≤ dH)
    (bW : OrthonormalBasis (Fin dW) ℝ W) (hW : m ≤ dW)
    (q : Query Seed A Q) (dec : Activation Side A Q) (r : Reply Seed Side H W A Q m)
    (hq : ∀ n, Measurable (fun x : Seed × History A => q n x.1 x.2))
    (hd : ∀ n, Measurable (fun x : Side × State A × Q => dec n x.1 x.2.1 x.2.2))
    (hr : ∀ n, Measurable
      (fun x : Seed × Side × State A × ℕ × ℕ × (Fin 1 → H) × (Fin m → W) × Q =>
        r n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2))
    (out : Seed → History A → Q) (hout : Measurable (fun x : Seed × History A => out x.1 x.2))
    (N J : ℕ) (componentsH : Fin J → Q → H) (componentsW : Fin J → Q → W)
    (hcH : ∀ j, Measurable (componentsH j)) (hcW : ∀ j, Measurable (componentsW j))
    (RH RW sH sW : ℝ) (hRH : 0 < RH) (hRW : 0 < RW) (hsH : 0 ≤ sH) (hsW : 0 ≤ sW) :
    let μ := packetLaw σ bH hH bW hW
    FangqingAdaptiveHaarExternal.HaarConclusion
      (μ.real (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin 1,
        {x : Input Seed Side H W m | (run q dec r n.val x.1.1 x.1.2 x.2.1 x.2.2).1 ≤ i.val ∧
          sH < |inner ℝ (x.2.1 i) (generatedCandidate q dec r out N J componentsH RH n j x)|}))
      dH 1 N J RH sH ∧
    FangqingAdaptiveHaarExternal.HaarConclusion
      (μ.real (⋃ n : Fin (N + 1), ⋃ j : Fin J, ⋃ i : Fin m,
        {x : Input Seed Side H W m | (run q dec r n.val x.1.1 x.1.2 x.2.1 x.2.2).2.1 ≤ i.val ∧
          sW < |inner ℝ (x.2.2 i) (generatedCandidate q dec r out N J componentsW RW n j x)|}))
      dW m N J RW sW := by
  let νH := FangqingAdaptiveHaarOriginal.frameLaw bH hH
  let νW := FangqingAdaptiveHaarOriginal.frameLaw bW hW
  haveI : IsProbabilityMeasure νH := Measure.isProbabilityMeasure_map
    (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  haveI : IsProbabilityMeasure νW := Measure.isProbabilityMeasure_map
    (FangqingAdaptiveHaarProduct.measurable_frame _).aemeasurable
  let μ := σ.prod (νH.prod νW)
  let U (n : ℕ) (x : Input Seed Side H W m) := run q dec r n x.1.1 x.1.2 x.2.1 x.2.2
  let KH (n : ℕ) (x : Input Seed Side H W m) := (U n x).1
  let KT (n : ℕ) (x : Input Seed Side H W m) := (U n x).2.1
  let DH (n : ℕ) (x : Input Seed Side H W m) := dec n x.1.2 (U n x) (q n x.1.1 (U n x).2.2)
  let DT (n : ℕ) (x : Input Seed Side H W m) := tailDecision (U n x)
  let XH (x : Input Seed Side H W m) := (x.1.1, x.1.2, x.2.2)
  let XT (x : Input Seed Side H W m) := (x.1.1, x.1.2, x.2.1)
  have hindH : IndepFun XH (fun x : Input Seed Side H W m => x.2.1) μ := by
    have hi := OriginalTwoGroupProductLaw.handle_side_independent σ νH νW
    convert! hi.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd)) measurable_id using 1
  have hindT : IndepFun XT (fun x : Input Seed Side H W m => x.2.2) μ := by
    have hi := OriginalTwoGroupProductLaw.tail_side_independent σ νH νW
    convert! hi.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd)) measurable_id using 1
  have hlaw := OriginalTwoGroupProductLaw.actual_group_marginal_laws σ νH νW
  have hstate (n : ℕ) := two_group_state_measurable_in_each_disclosed_prefix q dec r hq hd hr n
  have hqueryH (n : ℕ) := (chosen_candidate_measurable_in_each_disclosed_prefix
    q dec r hq hd hr (fun x => q n x.1 x.2) (hq n) n).1
  have hsideH (n : ℕ) : Measurable[MeasurableSpace.comap (handleView q dec r n) inferInstance]
      (fun x : Input Seed Side H W m => x.1.2) := by
    convert! (measurable_fst.comp (measurable_snd.comp measurable_fst) :
      Measurable (fun x : (Seed × Side × (Fin m → W)) × ℕ × (Fin 1 → H) => x.1.2.1)).comp
      (comap_measurable (handleView q dec r n)) using 1
  have hDH (n : ℕ) : Measurable[MeasurableSpace.comap (handleView q dec r n) inferInstance] (DH n) :=
    (hd n).comp ((hsideH n).prodMk ((hstate n).1.prodMk (hqueryH n)))
  have hDT (n : ℕ) : Measurable[MeasurableSpace.comap (tailView q dec r n) inferInstance] (DT n) := by
    apply Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp (hstate n).2))
      measurable_const measurable_const
  have hchoose (n : Fin (N + 1)) : Measurable (queryOrOutput q out N n) := by
    unfold queryOrOutput
    by_cases hn : n.val < N
    · simpa only [if_pos hn] using hq n.val
    · simpa only [if_neg hn] using hout
  have hcandH (n : Fin (N + 1)) (j : Fin J) :=
    (chosen_candidate_measurable_in_each_disclosed_prefix q dec r hq hd hr
      (fun x => OriginalPrefixOracleHaarBridge.zeroClip RH (componentsH j (queryOrOutput q out N n x)))
      ((OriginalPrefixOracleHaarBridge.zeroClip_measurable RH).comp ((hcH j).comp (hchoose n))) n.val).1
  have hcandT (n : Fin (N + 1)) (j : Fin J) :=
    (chosen_candidate_measurable_in_each_disclosed_prefix q dec r hq hd hr
      (fun x => OriginalPrefixOracleHaarBridge.zeroClip RW (componentsW j (queryOrOutput q out N n x)))
      ((OriginalPrefixOracleHaarBridge.zeroClip_measurable RW).comp ((hcW j).comp (hchoose n))) n.val).2
  constructor
  · exact haar_from_explicit_execution_view μ XH (fun x => x.2.1) (by fun_prop) (by fun_prop)
      hindH bH hH hlaw.1 KH DH U (fun _ => rfl) (fun _ _ => rfl)
      (fun n => (hstate n).1) hDH N J (generatedCandidate q dec r out N J componentsH RH)
      hcandH RH sH hRH hsH (fun _ _ _ => OriginalPrefixOracleHaarBridge.zeroClip_bound RH hRH.le _)
  · exact haar_from_explicit_execution_view μ XT (fun x => x.2.2) (by fun_prop) (by fun_prop)
      hindT bW hW hlaw.2 KT DT U (fun _ => rfl) (fun _ _ => rfl)
      (fun n => (hstate n).2) hDT N J (generatedCandidate q dec r out N J componentsW RW)
      hcandT RW sW hRW hsW (fun _ _ _ => OriginalPrefixOracleHaarBridge.zeroClip_bound RW hRW.le _)

end OriginalTwoGroupHaarExecution
end
