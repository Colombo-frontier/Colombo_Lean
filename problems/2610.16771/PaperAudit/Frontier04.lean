import Mathlib
import PaperAudit.Frontier03

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: CanonicalRelayRegularityComplete.lean

open scoped ContDiff Topology NNReal

namespace FangqingCanonicalRelayRegularityComplete

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingExternalPhysicalRelayValidity FangqingPhysicalRelayExactInitialPoint
  FangqingInitialGateGeometry FangqingRelayStationarity FangqingRelayRegularityComplete
  FangqingActualShellMinimizerPublicCoefficients OriginalCanonicalPacketTailSupport

noncomputable section

set_option maxHeartbeats 8500000

universe u

theorem actual_original_relay_has_public_canonical_minimizers
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
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, hBuilder⟩ :=
    actual_relay_regularity_stationarity_initialization.{u} P phi Bp left right Cm Cw b0
      hCm hCw hb0 hp hl hr hcore
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r rhop q delta omega hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn
    Li ri scale barlam homega hDistance nu D A R seed Mpath gain H0 H1 Zc
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRest⟩ :=
    hBuilder A0 B0 W outer nt C h tail L mu eps r rhop q delta omega hh ht
      hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn homega hDistance
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
  rw [hEq] at hMin1 hNorm hLocalGap hBulk hRest
  exact ⟨hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRest⟩

end
end FangqingCanonicalRelayRegularityComplete
end

section
-- Source component: ActualRelayDecoderInterfaces.lean

namespace FangqingActualRelayDecoderInterfaces

open FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingActualRelayScaling FangqingRadialGateBounds FangqingExternalPhysicalRelayValidity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_normalizing_minimum_is_literal_infimum (H : E → ℝ) (Z : E)
    (hmin : ∀ Y, H Z ≤ H Y) : sInf (Set.range H) = H Z := by
  apply le_antisymm
  · exact csInf_le ⟨H Z, by rintro _ ⟨Y, rfl⟩; exact hmin Y⟩ ⟨Z, rfl⟩
  · apply le_csInf (Set.range_nonempty H)
    rintro _ ⟨Y, rfl⟩
    exact hmin Y

theorem scaled_gate_is_literal_private_center_radial_gate
    (theta : ℝ → ℝ) (a ell : ℝ) (star : E) :
    scaledGate theta (a * ell) (a • star) = radialGate theta a ell star := by
  funext p
  simp only [scaledGate, radialGate, mul_pow]

theorem actual_full_relay_gate_coefficient_is_nonzero
    (Cdelta N L mu KD eps : ℝ) (hL : 0 < L) (hmu : 0 < mu)
    (heps : 0 < eps) (hC : 0 ≤ Cdelta) (hN : 0 ≤ N)
    (h0 h1 : Fin 2 → E → ℝ) (m0 m1 : Fin 2 → ℝ)
    (hDelta : ∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤
      rawBudget Cdelta N L mu KD eps) (point : FlatJoint 1 E) :
    coefficient 1 (reward Cdelta N L KD eps) h0 h1 m0 m1
      (fun t => point (1, t)) 0 ≠ 0 := by
  have hinterval := actual_coefficient_interval Cdelta N L mu KD eps
    (delta (h0 1) (h1 1) (m0 1) (m1 1) (point (1, 1))) hL hmu hC hN (hDelta 1 _)
  have hE : 0 < energy L eps := by unfold energy; positivity
  have heq : coefficient 1 (reward Cdelta N L KD eps) h0 h1 m0 m1
      (fun t => point (1, t)) 0 =
      delta (h0 1) (h1 1) (m0 1) (m1 1) (point (1, 1)) - reward Cdelta N L KD eps := by
    rfl
  rw [heq]
  exact ne_of_lt (hinterval.2.trans_lt (neg_neg_of_pos hE))

end FangqingActualRelayDecoderInterfaces
end

section
-- Source component: CanonicalLateHitMargins.lean

open scoped Topology

namespace FangqingCanonicalLateHitMargins

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalCanonicalPacketTailSupport FangqingCanonicalLateGateGeometry FangqingLateGateKnownSphere
  FangqingRelayStationarity

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem actual_three_missing_columns_query_is_inside_chamber_and_flat_gate
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1) (n : ℕ)
    (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (alpha tau a ell q omega Cw b1 : ℝ) (z : Fin (n + 3) → ℝ)
    (j : Fin (n + 3)) (hj : 2 ≤ j.val)
    (hzero : ∀ i, j.val < i.val → z i = 0)
    (hq : 0 < q) (hw : 0 ≤ omega) (hCw : 0 ≤ Cw) (ha : 0 < a)
    (hell : 0 < ell) (hb1 : 0 < b1)
    (hellEq : ell = tau * (q * Real.sqrt q * omega))
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 2 * Cw * q * omega)
    (hLargeB : 12 * Cw ^ 2 < q * b1 ^ 2)
    (hLargeInner : 12 * Cw ^ 2 < q * (9 / 4 : ℝ)) :
    let star := -(tau • coordinatePoint C h n tail alpha z)
    let known := -(tau • knownPrefixPoint C h n tail alpha z (j.val - 2))
    ‖a • known - a • star‖ < b1 * a * ell ∧
      radialGate FangqingPublicShellProfiles.theta a ell star (a • known) = 1 ∧
      radialGate FangqingPublicShellProfiles.theta a ell star =ᶠ[𝓝 (a • known)] (fun _ => 1) := by
  intro star known
  have hgeo := actual_scaled_last_three_residual_norm C h hh n tail ht alpha tau z j hj hzero
  change ‖star - known‖ ^ 2 = _ at hgeo
  have hb := three_last_coefficients_residual_bound q omega tau Cw
    (z (previousIndex j 2)) (z (previousIndex j 1)) (z j) hq hw hCw
    (hz _).1 (hz _).1 (hz _).1 (hz _).2 (hz _).2 (hz _).2
  rw [← hellEq] at hb
  have hbound : ‖known - star‖ ^ 2 ≤ 12 * Cw ^ 2 * ell ^ 2 / q := by
    rw [norm_sub_rev, hgeo]
    convert hb using 1 <;> ring
  have hBcoeff : 12 * Cw ^ 2 / q < b1 ^ 2 :=
    (div_lt_iff₀ hq).mpr (by nlinarith only [hLargeB])
  have hIcoeff : 12 * Cw ^ 2 / q < (9 / 4 : ℝ) :=
    (div_lt_iff₀ hq).mpr (by nlinarith only [hLargeInner])
  have hnormB : ‖known - star‖ < b1 * ell := by
    have hs := mul_lt_mul_of_pos_right hBcoeff (sq_pos_of_pos hell)
    rw [div_mul_eq_mul_div] at hs
    nlinarith only [hbound, hs, norm_nonneg (known - star), mul_pos hb1 hell]
  have hnormI : ‖known - star‖ ^ 2 < (9 / 4 : ℝ) * ell ^ 2 := by
    have hs := mul_lt_mul_of_pos_right hIcoeff (sq_pos_of_pos hell)
    rw [div_mul_eq_mul_div] at hs
    exact hbound.trans_lt hs
  have hquerynorm : ‖a • known - a • star‖ = a * ‖known - star‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hchamber : ‖a • known - a • star‖ < b1 * a * ell := by
    rw [hquerynorm]
    have hh := mul_lt_mul_of_pos_left hnormB ha
    nlinarith only [hh]
  let argument := fun p : PhysicalSpace A B W => ‖p - a • star‖ ^ 2 / (a ^ 2 * ell ^ 2)
  have harg : argument (a • known) < (9 / 4 : ℝ) := by
    dsimp only [argument]
    rw [hquerynorm]
    apply (div_lt_iff₀ (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hell))).mpr
    have hh := mul_lt_mul_of_pos_left hnormI (sq_pos_of_pos ha)
    nlinarith only [hh]
  have hcontinuous : Continuous argument := by dsimp only [argument]; fun_prop
  have hnhds : ∀ᶠ p in 𝓝 (a • known), argument p < (9 / 4 : ℝ) :=
    (isOpen_lt hcontinuous continuous_const).mem_nhds harg
  have heq : radialGate FangqingPublicShellProfiles.theta a ell star =ᶠ[𝓝 (a • known)]
      (fun _ => 1) := by
    filter_upwards [hnhds] with p hp
    exact FangqingPublicShellProfiles.theta_one _ hp.le
  exact ⟨hchamber, heq.eq_of_nhds, heq⟩

theorem public_transition_offset_exists_from_two_coefficient_bound
    (q omega tau Cw z1 z2 ell t0 : ℝ)
    (hq : 0 < q) (hw : 0 ≤ omega) (hCw : 0 ≤ Cw) (hell : 0 < ell)
    (hellEq : ell = tau * (q * Real.sqrt q * omega))
    (hz1 : 0 ≤ z1) (hz2 : 0 ≤ z2)
    (hu1 : z1 ≤ 2 * Cw * q * omega) (hu2 : z2 ≤ 2 * Cw * q * omega)
    (hLarge : 8 * Cw ^ 2 < q * t0) :
    let r := knownOffset ell t0 (-tau * z1) (-tau * z2)
    0 < r ∧ r ^ 2 + (-tau * z1) ^ 2 + (-tau * z2) ^ 2 = ell ^ 2 * t0 := by
  apply knownOffset_properties
  have hb := two_last_coefficients_residual_bound q omega tau Cw z1 z2 hq hw hCw hz1 hz2 hu1 hu2
  rw [← hellEq] at hb
  have hcoeff : 8 * Cw ^ 2 / q < t0 := (div_lt_iff₀ hq).mpr (by nlinarith only [hLarge])
  have hs := mul_lt_mul_of_pos_right hcoeff (sq_pos_of_pos hell)
  rw [div_mul_eq_mul_div] at hs
  have hh := hb.trans_lt hs
  nlinarith only [hh]

end FangqingCanonicalLateHitMargins
end

section
-- Source component: UnboundedOriginalPacketLength.lean

namespace FangqingUnboundedOriginalPacketLength

open HandleAlignment

theorem original_packet_length_can_exceed_every_fixed_threshold
    (cq : ℝ) (hcq : 0 < cq) (hcq1 : cq ≤ 1) (Q : ℕ) :
    ∃ kappa r : ℝ, 1 ≤ kappa ∧ 1 ≤ r ∧
      Q ≤ packetLength cq r kappa := by
  let S := ((Q : ℝ) + 1) / cq + 1
  have hS : 1 ≤ S := by
    have hn : 0 ≤ ((Q : ℝ) + 1) / cq := by positivity
    dsimp only [S]
    linarith only [hn]
  have hS0 : 0 < S := zero_lt_one.trans_le hS
  have hsq : S ≤ S ^ 2 := by nlinarith only [hS, sq_nonneg (S - 1)]
  have hpow : (S ^ 7) ^ (2 / 7 : ℝ) = S ^ 2 := by
    calc
      (S ^ 7) ^ (2 / 7 : ℝ) = (S ^ (7 : ℝ)) ^ (2 / 7 : ℝ) := by norm_num
      _ = S ^ ((7 : ℝ) * (2 / 7)) := (Real.rpow_mul hS0.le _ _).symm
      _ = S ^ 2 := by norm_num
  refine ⟨S ^ 2, S ^ 7, one_le_pow₀ hS, one_le_pow₀ hS, ?_⟩
  apply Nat.le_floor
  rw [hpow, Real.sqrt_sq hS0.le, min_eq_right hsq]
  have heq : cq * S = (Q : ℝ) + 1 + cq := by
    dsimp only [S]
    field_simp
  rw [heq]
  linarith only [hcq]

theorem actual_external_regime_is_the_same_public_r
    (kappa r : ℝ) (hkappa : 0 < kappa) :
    regime kappa (FangqingThirdGroupScaling.rho kappa 1 1 r) 1 kappa = r := by
  unfold regime
  rw [rpow_three_halves kappa hkappa]
  dsimp [FangqingThirdGroupScaling.rho]
  have hs : Real.sqrt kappa ≠ 0 := (Real.sqrt_pos.mpr hkappa).ne'
  field_simp

theorem original_packet_length_unbounded_in_actual_regime
    (cq : ℝ) (hcq : 0 < cq) (hcq1 : cq ≤ 1) (Q : ℕ) :
    ∃ kappa r : ℝ, 1 ≤ kappa ∧ 1 ≤ r ∧
      Q ≤ packetLength cq
        (regime kappa (FangqingThirdGroupScaling.rho kappa 1 1 r) 1 kappa) kappa := by
  obtain ⟨kappa, r, hk, hr, hQ⟩ :=
    original_packet_length_can_exceed_every_fixed_threshold cq hcq hcq1 Q
  refine ⟨kappa, r, hk, hr, ?_⟩
  rw [actual_external_regime_is_the_same_public_r kappa r (zero_lt_one.trans_le hk)]
  exact hQ

theorem arbitrary_original_dimension_reserve_is_available (m : ℕ) (bound : ℝ) :
    ∃ d : ℕ, m ≤ d ∧ bound ≤ ((d - m : ℕ) : ℝ) := by
  obtain ⟨k, hk⟩ := exists_nat_ge bound
  exact ⟨m + k, Nat.le_add_right m k, by simpa only [Nat.add_sub_cancel_left] using hk⟩

end FangqingUnboundedOriginalPacketLength
end

section
-- Source component: ActualLateGateResponseSeparation.lean

namespace FangqingActualLateGateResponseSeparation

open FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingLateGateLeakageKernel FangqingObservableGateCenterDecoder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

noncomputable def negateLast (v : Fin 3 → E) : Fin 3 → E := ![v 0, v 1, -(v 2)]

theorem negateLast_orthonormal (v : Fin 3 → E) (hv : Orthonormal ℝ v) :
    Orthonormal ℝ (negateLast v) := by
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negateLast, inner_neg_left, inner_neg_right, orthonormal_iff_ite.mp hv, hv.norm_eq_one]

theorem actual_original_full_response_separates_last_column_sign
    (bet lam a sigma reward ell : ℝ)
    (h0p h1p h0m h1m : Fin 2 → E → ℝ) (m0p m1p m0m m1m : Fin 2 → ℝ)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta)
    (point : FlatJoint 1 E) (v : Fin 3 → E) (hv : Orthonormal ℝ v) (known : E)
    (r alpha beta t0 : ℝ) (ha : 0 < a) (hr : 0 < r) (hell : 0 < ell)
    (hbeta : beta ≠ 0)
    (hquery : point (2, 0) = a • (known + r • v 0))
    (hsphere : r ^ 2 + alpha ^ 2 + beta ^ 2 = ell ^ 2 * t0)
    (hderiv : deriv theta t0 ≠ 0)
    (hBp : coefficient 1 reward h0p h1p m0p m1p (fun t => point (1, t)) 0 ≠ 0)
    (hBm : coefficient 1 reward h0m h1m m0m m1m (fun t => point (1, t)) 0 ≠ 0)
    (hJp : Differentiable ℝ (assembled 1 bet lam a sigma reward h0p h1p m0p m1p
      (fun _ => radialGate theta a ell (known + alpha • v 1 + beta • v 2))))
    (hJm : Differentiable ℝ (assembled 1 bet lam a sigma reward h0m h1m m0m m1m
      (fun _ => radialGate theta a ell (known + alpha • v 1 + beta • -(v 2))))) :
    FangqingShellPrefixLocality.bundle
      (assembled 1 bet lam a sigma reward h0m h1m m0m m1m
        (fun _ => radialGate theta a ell (known + alpha • v 1 + beta • -(v 2)))) point ≠
    FangqingShellPrefixLocality.bundle
      (assembled 1 bet lam a sigma reward h0p h1p m0p m1p
        (fun _ => radialGate theta a ell (known + alpha • v 1 + beta • v 2))) point := by
  have hp := (actual_center_decoder_needs_no_private_normalizer bet lam a sigma reward ell
    h0p h1p m0p m1p theta htheta (known + alpha • v 1 + beta • v 2) hJp
    point v hv known r alpha beta t0 ha hr hell rfl hquery hsphere hderiv hBp).2.2
  have hm := (actual_center_decoder_needs_no_private_normalizer bet lam a sigma reward ell
    h0m h1m m0m m1m theta htheta (known + alpha • v 1 + beta • -(v 2)) hJm
    point (negateLast v) (negateLast_orthonormal v hv) known r alpha beta t0 ha hr hell
    (by simp [negateLast]) (by simpa [negateLast] using hquery) hsphere hderiv hBm).2.2
  simp only [negateLast, Matrix.cons_val_zero] at hm
  intro heq
  rw [heq, hp] at hm
  have hip := congrArg (fun z : E => inner ℝ (v 2) z) hm
  have h21 : inner ℝ (v 2) (v 1) = 0 := by
    simpa using orthonormal_iff_ite.mp hv (2 : Fin 3) 1
  have h22 : inner ℝ (v 2) (v 2) = 1 := by
    simpa using orthonormal_iff_ite.mp hv (2 : Fin 3) 2
  simp only [inner_add_right, real_inner_smul_right, inner_neg_right, h21, h22,
    mul_zero, mul_one, add_zero, mul_neg] at hip
  exact hbeta (by linarith only [hip])

end FangqingActualLateGateResponseSeparation
end

section
-- Source component: RecursivePrefixSimulatorObstruction.lean

namespace FangqingRecursivePrefixSimulatorObstruction

open MeasureTheory

variable {Column Response : Type*} [Zero Column] {m : ℕ}

def disclosed (k : ℕ) (frame : Fin m → Column) : Fin m → Column :=
  fun i => if i.val < k then frame i else 0

def simulatedTranscript
    (step : ℕ → (Fin m → Column) → List Response → Response)
    (frame : Fin m → Column) : ℕ → List Response
  | 0 => []
  | r + 1 =>
      let previous := simulatedTranscript step frame r
      previous ++ [step r (disclosed (r + 2) frame) previous]

def simulatedAnswer
    (step : ℕ → (Fin m → Column) → List Response → Response)
    (frame : Fin m → Column) (r : ℕ) : Response :=
  step r (disclosed (r + 2) frame) (simulatedTranscript step frame r)

theorem disclosed_respects_prefix (cap k : ℕ) (hk : k ≤ cap)
    (V U : Fin m → Column) (hVU : ∀ i, i.val < cap → V i = U i) :
    disclosed k V = disclosed k U := by
  funext i
  by_cases hi : i.val < k
  · simp only [disclosed, if_pos hi, hVU i (lt_of_lt_of_le hi hk)]
  · simp only [disclosed, if_neg hi]

theorem simulatedTranscript_respects_prefix
    (step : ℕ → (Fin m → Column) → List Response → Response)
    (cap : ℕ) (V U : Fin m → Column) (hVU : ∀ i, i.val < cap → V i = U i)
    (r : ℕ) (hr : r + 1 ≤ cap) :
    simulatedTranscript step V r = simulatedTranscript step U r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hprevious := ih (by omega)
      have hcolumns := disclosed_respects_prefix cap (r + 2) (by omega) V U hVU
      simp only [simulatedTranscript, hprevious, hcolumns]

theorem simulatedAnswer_respects_prefix
    (step : ℕ → (Fin m → Column) → List Response → Response)
    (r : ℕ) (V U : Fin m → Column) (hVU : ∀ i, i.val < r + 2 → V i = U i) :
    simulatedAnswer step V r = simulatedAnswer step U r := by
  unfold simulatedAnswer
  rw [disclosed_respects_prefix (r + 2) (r + 2) le_rfl V U hVU,
    simulatedTranscript_respects_prefix step (r + 2) V U hVU r (by omega)]

theorem recursive_prefix_simulation_probability_at_most_half
    {Omega Seed : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (flip : Omega → Omega) (hflip : MeasurePreserving flip mu mu)
    (seed : Omega → Seed) (frame : Omega → Fin m → Column)
    (r : ℕ) (hseed : ∀ omega, seed (flip omega) = seed omega)
    (hprefix : ∀ omega i, i.val < r + 2 → frame (flip omega) i = frame omega i)
    (response : Omega → Response)
    (hresponse : ∀ omega, response (flip omega) ≠ response omega)
    (step : Seed → ℕ → (Fin m → Column) → List Response → Response)
    (good : Set Omega) (hgood : MeasurableSet good)
    (hsim : ∀ omega ∈ good, response omega =
      simulatedAnswer (step (seed omega)) (frame omega) r) :
    mu.real good ≤ 1 / 2 := by
  let prediction := fun omega => simulatedAnswer (step (seed omega)) (frame omega) r
  have hprediction : ∀ omega, prediction (flip omega) = prediction omega := by
    intro omega
    dsimp only [prediction]
    rw [hseed omega]
    exact simulatedAnswer_respects_prefix (step (seed omega)) r _ _ (hprefix omega)
  exact FangqingPrefixSimulatorSymmetryObstruction.prefix_simulation_event_has_probability_at_most_half
    mu flip hflip prediction response hprediction hresponse id good hgood hsim

end FangqingRecursivePrefixSimulatorObstruction
end

section
-- Source component: PhysicalHaarLastColumnFlip.lean

namespace FangqingPhysicalHaarLastColumnFlip

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalCanonicalPacketTailSupport FangqingAdaptiveHaarProduct FangqingHaarColumnSignFlip
  FangqingCanonicalLateGateGeometry

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]

theorem physical_column_flip
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (g : FangqingOrthogonalHaar.Group W)
    (i : Fin (n + 3)) :
    physicalFrame C h n (frame b (g * flipColumn b j)) i =
      if i = j.succ then -(physicalFrame C h n (frame b g) i)
      else physicalFrame C h n (frame b g) i := by
  refine Fin.cases ?_ (fun k => ?_) i
  · have hne : (0 : Fin (n + 3)) ≠ j.succ := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_zero, Fin.val_succ] at hv
      omega
    simp [physicalFrame, hne]
  · simp only [physicalFrame, Fin.cons_succ, actual_rotated_frame_flip b hb j g k]
    by_cases hk : k = j
    · subst k
      simp only [if_pos rfl]
      apply (WithLp.ext_iff 2).mpr
      apply Prod.ext
      · apply (WithLp.ext_iff 2).mpr
        apply Prod.ext <;> simp [mkPhysical]
      · simp [mkPhysical]
    · simp [hk, mkPhysical]

theorem physical_prefix_unchanged
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (g : FangqingOrthogonalHaar.Group W)
    (cutoff : ℕ) (hcutoff : cutoff ≤ j.val + 1) (i : Fin (n + 3)) (hi : i.val < cutoff) :
    physicalFrame C h n (frame b (g * flipColumn b j)) i =
      physicalFrame C h n (frame b g) i := by
  rw [physical_column_flip C h n b hb j g i]
  have hne : i ≠ j.succ := by
    intro he
    have he' := congrArg Fin.val he
    simp only [Fin.val_succ] at he'
    omega
  rw [if_neg hne]

theorem actual_known_center_prefix_unchanged
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (g : FangqingOrthogonalHaar.Group W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (cutoff : ℕ) (hcutoff : cutoff ≤ j.val + 1) :
    knownPrefixPoint C h n (frame b (g * flipColumn b j)) alpha z cutoff =
      knownPrefixPoint C h n (frame b g) alpha z cutoff := by
  exact knownPrefixPoint_depends_only_on_prefix C h n _ _ alpha z cutoff
    (physical_prefix_unchanged C h n b hb j g cutoff hcutoff)

theorem actual_flipped_scaled_center_last_two
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (g : FangqingOrthogonalHaar.Group W)
    (alpha tau : ℝ) (z : Fin (n + 3) → ℝ)
    (hzero : ∀ i, j.succ.val < i.val → z i = 0) :
    -(tau • coordinatePoint C h n (frame b (g * flipColumn b j)) alpha z) =
      -(tau • knownPrefixPoint C h n (frame b g) alpha z (j.succ.val - 1)) +
        (-tau * z (previousIndex j.succ 1)) •
          physicalFrame C h n (frame b g) (previousIndex j.succ 1) +
        (-tau * z j.succ) • -(physicalFrame C h n (frame b g) j.succ) := by
  rw [actual_scaled_center_last_two_decomposition C h n _ alpha tau z j.succ
    (by simp only [Fin.val_succ]; omega) hzero]
  rw [actual_known_center_prefix_unchanged C h n b hb j g alpha z (j.succ.val - 1)
    (by simp only [Fin.val_succ]; omega)]
  rw [physical_column_flip C h n b hb j g (previousIndex j.succ 1),
    physical_column_flip C h n b hb j g j.succ]
  have hne : previousIndex j.succ 1 ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  rw [if_neg hne, if_pos rfl]

theorem canonical_prefixPoint_is_granted_prefixPoint
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha : ℝ) (z : Fin (n + 3) → ℝ) (cutoff : ℕ) :
    knownPrefixPoint C h n tail alpha z cutoff =
      FangqingLateQueryFromHistory.prefixPoint n cutoff alpha (mkPhysical h 0 0) z
        (physicalFrame C h n tail) := by
  simp only [knownPrefixPoint, FangqingLateQueryFromHistory.prefixPoint]
  congr 1
  apply (WithLp.ext_iff 2).mpr
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    apply Prod.ext <;> simp [mkPhysical]
  · simp [mkPhysical]

end FangqingPhysicalHaarLastColumnFlip
end

section
-- Source component: PhysicalHaarActualGateSeparation.lean

namespace FangqingPhysicalHaarActualGateSeparation

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalCanonicalPacketTailSupport FangqingAdaptiveHaarProduct FangqingHaarColumnSignFlip
  FangqingCanonicalLateGateGeometry FangqingPhysicalHaarLastColumnFlip
  FangqingActualLateGateResponseSeparation FangqingRelayStationarity FangqingRelayAnalyticAssembly
  FangqingRelayJointReindexing FangqingLateGateRelaySlice

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]

noncomputable def transitionPoint
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha tau a r : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 2)) :
    FlatJoint 1 (PhysicalSpace A B W) :=
  coordinateIsometry ((2 : Fin 3), (0 : Fin 2))
    (a • (-(tau • knownPrefixPoint C h n tail alpha z j.val) + r • mkPhysical h 0 0))

theorem actual_transition_query_is_identical_under_last_column_flip
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (g : FangqingOrthogonalHaar.Group W)
    (alpha tau a r : ℝ) (z : Fin (n + 3) → ℝ) :
    transitionPoint C h n (frame b (g * flipColumn b j)) alpha tau a r z j =
      transitionPoint C h n (frame b g) alpha tau a r z j := by
  unfold transitionPoint
  rw [actual_known_center_prefix_unchanged C h n b hb j g alpha z j.val (by omega)]

theorem actual_full_relay_oracle_is_flip_sensitive_at_legal_prefix_query
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n : ℕ) (b : Fin (n + 2) → W) (hb : Orthonormal ℝ b) (j : Fin (n + 2))
    (alpha tau a r bet lam sigma reward ell t0 : ℝ) (z : Fin (n + 3) → ℝ)
    (htau : tau ≠ 0) (hz : z j.succ ≠ 0)
    (hzero : ∀ i, j.succ.val < i.val → z i = 0)
    (ha : 0 < a) (hr : 0 < r) (hell : 0 < ell)
    (hsphere : r ^ 2 + (-tau * z (previousIndex j.succ 1)) ^ 2 +
      (-tau * z j.succ) ^ 2 = ell ^ 2 * t0)
    (theta : ℝ → ℝ) (htheta : Differentiable ℝ theta) (hderiv : deriv theta t0 ≠ 0)
    (h0 h1 : (Fin (n + 2) → W) → Fin 2 → PhysicalSpace A B W → ℝ)
    (m0 m1 : (Fin (n + 2) → W) → Fin 2 → ℝ)
    (hJ : ∀ g : FangqingOrthogonalHaar.Group W,
      Differentiable ℝ (assembled 1 bet lam a sigma reward (h0 (frame b g)) (h1 (frame b g))
        (m0 (frame b g)) (m1 (frame b g))
        (fun _ => radialGate theta a ell (-(tau • coordinatePoint C h n (frame b g) alpha z)))))
    (hB : ∀ (g : FangqingOrthogonalHaar.Group W) (point : FlatJoint 1 (PhysicalSpace A B W)),
      coefficient 1 reward (h0 (frame b g)) (h1 (frame b g)) (m0 (frame b g)) (m1 (frame b g))
        (fun t => point (1, t)) 0 ≠ 0) :
    let response := fun g : FangqingOrthogonalHaar.Group W =>
      FangqingShellPrefixLocality.bundle
        (assembled 1 bet lam a sigma reward (h0 (frame b g)) (h1 (frame b g))
          (m0 (frame b g)) (m1 (frame b g))
          (fun _ => radialGate theta a ell (-(tau • coordinatePoint C h n (frame b g) alpha z))))
        (transitionPoint C h n (frame b g) alpha tau a r z j)
    ∀ g, response (g * flipColumn b j) ≠ response g := by
  intro response g
  let V := physicalFrame C h n (frame b g)
  let v := handleFrameTriple C h n (frame b g) (previousIndex j.succ 1) j.succ
  let known := -(tau • knownPrefixPoint C h n (frame b g) alpha z j.val)
  let point := transitionPoint C h n (frame b g) alpha tau a r z j
  have ht : Orthonormal ℝ (frame b g) := hb.comp_linearIsometryEquiv (Unitary.linearIsometryEquiv g)
  have hne : previousIndex j.succ 1 ≠ j.succ := by
    intro he
    have hv := congrArg Fin.val he
    dsimp [previousIndex] at hv
    omega
  have hv : Orthonormal ℝ v := actual_handle_two_columns_orthonormal C h hh n _ ht _ _ hne
  have hstarP := actual_scaled_center_last_two_decomposition C h n (frame b g) alpha tau z
    j.succ (by simp only [Fin.val_succ]; omega) hzero
  have hstarM := actual_flipped_scaled_center_last_two C h n b hb j g alpha tau z hzero
  simp only [Fin.val_succ, Nat.add_sub_cancel] at hstarP hstarM
  change -(tau • coordinatePoint C h n (frame b g) alpha z) =
    known + (-tau * z (previousIndex j.succ 1)) • v 1 + (-tau * z j.succ) • v 2 at hstarP
  change -(tau • coordinatePoint C h n (frame b (g * flipColumn b j)) alpha z) =
    known + (-tau * z (previousIndex j.succ 1)) • v 1 + (-tau * z j.succ) • -(v 2) at hstarM
  have hpJ := hJ g
  have hmJ := hJ (g * flipColumn b j)
  rw [hstarP] at hpJ
  rw [hstarM] at hmJ
  have hpquery : point (2, 0) = a • (known + r • v 0) := by
    simp [point, transitionPoint, coordinateIsometry, known, v, handleFrameTriple]
  have hseparation := actual_original_full_response_separates_last_column_sign bet lam a sigma reward ell
    (h0 (frame b g)) (h1 (frame b g)) (h0 (frame b (g * flipColumn b j)))
    (h1 (frame b (g * flipColumn b j))) (m0 (frame b g)) (m1 (frame b g))
    (m0 (frame b (g * flipColumn b j))) (m1 (frame b (g * flipColumn b j))) theta htheta
    point v hv known r (-tau * z (previousIndex j.succ 1)) (-tau * z j.succ) t0
    ha hr hell (mul_ne_zero (neg_ne_zero.mpr htau) hz) hpquery hsphere hderiv
    (hB g point) (hB (g * flipColumn b j) point) hpJ hmJ
  dsimp only [response]
  rw [actual_transition_query_is_identical_under_last_column_flip C h n b hb j g alpha tau a r z]
  rw [hstarP, hstarM]
  exact hseparation

end FangqingPhysicalHaarActualGateSeparation
end

section
-- Source component: ActualHaarRecursivePrefixObstruction.lean

namespace FangqingActualHaarRecursivePrefixObstruction

open MeasureTheory FangqingAmplifier OriginalPacketOrientationNormalization
  FangqingAdaptiveHaarProduct FangqingHaarColumnSignFlip FangqingPhysicalHaarLastColumnFlip
  FangqingRecursivePrefixSimulatorObstruction

variable {A B W Seed Response : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W] [MeasurableSpace Seed]

theorem actual_haar_recursive_prefix_good_event_has_probability_at_most_half
    (sigma : Measure Seed) [IsProbabilityMeasure sigma]
    (C : A ≃ₗᵢ[ℝ] B) (handle : Seed → A) (n : ℕ) (b : Fin (n + 2) → W)
    (hb : Orthonormal ℝ b) (j : Fin (n + 2)) (r : ℕ) (hr : r + 2 ≤ j.val + 1)
    (response : Seed × FangqingOrthogonalHaar.Group W → Response)
    (hresponse : ∀ seed g, response (seed, g * flipColumn b j) ≠ response (seed, g))
    (step : Seed → ℕ → (Fin (n + 3) → PhysicalSpace A B W) → List Response → Response)
    (good : Set (Seed × FangqingOrthogonalHaar.Group W)) (hgood : MeasurableSet good)
    (hsim : ∀ x ∈ good, response x = simulatedAnswer (step x.1)
      (physicalFrame C (handle x.1) n (frame b x.2)) r) :
    (sigma.prod (FangqingOrthogonalHaar.rightHaar W)).real good ≤ 1 / 2 := by
  apply recursive_prefix_simulation_probability_at_most_half
    (sigma.prod (FangqingOrthogonalHaar.rightHaar W))
    (fun x : Seed × FangqingOrthogonalHaar.Group W => (x.1, x.2 * flipColumn b j))
    (product_flipColumn_preserving sigma b j) Prod.fst
    (fun x : Seed × FangqingOrthogonalHaar.Group W => physicalFrame C (handle x.1) n (frame b x.2))
    r (fun _ => rfl) ?_ response (fun x => hresponse x.1 x.2) step good hgood hsim
  intro x i hi
  exact physical_prefix_unchanged C (handle x.1) n b hb j x.2 (r + 2) hr i hi

theorem original_conditional_good_probability_is_incompatible_with_late_flip
    {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (F : MeasurableSpace Omega) (hF : F ≤ mOmega)
    (zeta : ℝ) (hzeta : zeta < 1 / 2)
    (good : Set Omega) (hgood : MeasurableSet[mOmega] good)
    (hconditional : ∀ᵐ x ∂mu,
      mu[goodᶜ.indicator (fun _ => (1 : ℝ)) | F] x ≤ zeta)
    (hhalf : mu.real good ≤ 1 / 2) : False := by
  have hbad := FangqingAdaptiveHaar.event_bound_of_conditional_indicator (mΩ := mOmega) mu F hF goodᶜ
    hgood.compl zeta hconditional
  have hsum := measureReal_add_measureReal_compl (μ := mu) hgood
  rw [measureReal_univ_eq_one] at hsum
  linarith only [hhalf, hbad, hsum, hzeta]

end FangqingActualHaarRecursivePrefixObstruction
end

section
-- Source component: LateGateClippingMargins.lean

namespace FangqingLateGateClippingMargins

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_mapped_relay_candidate_is_bounded
    (tau D Cmin : ℝ) (htau : 0 < tau) (Z query : E)
    (hZ : ‖Z‖ ≤ Cmin * D)
    (hnear : ‖query - (-(tau • Z))‖ ≤ 2 * (tau * D)) :
    ‖-(tau⁻¹ • query)‖ ≤ (Cmin + 2) * D := by
  have hdiff : -(tau⁻¹ • query) - Z = -(tau⁻¹ • (query - (-(tau • Z)))) := by
    rw [smul_sub, smul_neg, smul_smul, inv_mul_cancel₀ htau.ne', one_smul]
    module
  have hnorm : ‖-(tau⁻¹ • query) - Z‖ = tau⁻¹ * ‖query - (-(tau • Z))‖ := by
    rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htau)]
  have hdistance : ‖-(tau⁻¹ • query) - Z‖ ≤ 2 * D := by
    rw [hnorm]
    have hh := mul_le_mul_of_nonneg_left hnear (inv_pos.mpr htau).le
    calc
      _ ≤ tau⁻¹ * (2 * (tau * D)) := hh
      _ = 2 * D := by field_simp
  have htriangle := norm_add_le (-(tau⁻¹ • query) - Z) Z
  rw [sub_add_cancel] at htriangle
  linarith only [htriangle, hdistance, hZ]

theorem one_public_clipping_radius_meets_original_reserves
    (Cmin b1 CR : ℝ) (hCmin : 0 ≤ Cmin) (hb1 : 0 ≤ b1) (hCR : 0 ≤ CR) :
    let Cclip := 4 * (Cmin + b1 + CR + 2)
    2 * CR ≤ Cclip ∧ 4 * Cmin < Cclip ∧ 4 * b1 < Cclip ∧
      Cmin + 2 < Cclip := by
  dsimp only
  constructor
  · linarith only [hCmin, hb1, hCR]
  constructor
  · linarith only [hb1, hCR]
  constructor
  · linarith only [hCmin, hCR]
  · linarith only [hCmin, hb1, hCR]

end FangqingLateGateClippingMargins
end

section
-- Source component: LateAugmentedGrantOnlyProtocol.lean

open MeasureTheory
open scoped Topology BigOperators
namespace FangqingLateAugmentedGrantProtocol
open FangqingOriginalF2PrefixAcquisition FangqingLateGateRelaySlice FangqingLateQueryFromHistory
noncomputable section
set_option maxHeartbeats 1800000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

abbrev AugResponse (n : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :=
  Response E × (Fin (n + 3) → E)
abbrev AugHistory (n : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] := ℕ → AugResponse n E

def maskFrame (n cutoff : ℕ) (V : Fin (n + 3) → E) : Fin (n + 3) → E :=
  fun i => if i.val < cutoff then V i else 0

def initialFrame (n : ℕ) (initial : E) : Fin (n + 3) → E := Function.update 0 0 initial

def learnedFrame (n : ℕ) (initial : E) (r : ℕ) (history : AugHistory n E) : Fin (n + 3) → E :=
  if r = 0 then initialFrame n initial else (history (r - 1)).2

def prefixCount (n r : ℕ) : ℕ := min (r + 1) (n + 3)

def sOnlyQuery (s : E) : Query E := coordinateIsometry ((2 : Fin 3), (0 : Fin 2)) s

def query (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E)
    (coeff : Fin (n + 3) → ℝ) (r : ℕ) (history : AugHistory n E) : Query E :=
  if r < N then 0 else if r ≤ N + 1 then
    sOnlyQuery (a • (-(tau • prefixPoint n (r + 1) alpha handle coeff (learnedFrame n initial r history)) +
      (if r = N + 1 then offset else 0) • handle)) else 0

/-- The first component is any genuine full bundled oracle. The extra field is
    exactly the explicitly allowed, unconditional next-column side grant. -/
def execution (n : ℕ) (choose : ℕ → AugHistory n E → Query E)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) : ℕ → AugHistory n E × List (Query E)
  | 0 => (0, [])
  | r + 1 =>
      let old := execution n choose oracle V r
      let z := choose r old.1
      (Function.update old.1 r (oracle z, maskFrame n (r + 2) V), old.2 ++ [z])

def executedQuery (n : ℕ) (choose : ℕ → AugHistory n E → Query E)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (r : ℕ) : Query E :=
  choose r (execution n choose oracle V r).1

theorem execution_paid_response_count (n : ℕ) (choose : ℕ → AugHistory n E → Query E)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (r : ℕ) :
    (execution n choose oracle V r).2.length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simpa only [execution, List.length_append, List.length_singleton] using congrArg (fun k : ℕ => k + 1) ih

theorem maskFrame_capped_clock (n r : ℕ) (V : Fin (n + 3) → E) :
    maskFrame n (prefixCount n r) V = maskFrame n (r + 1) V := by
  funext i
  simp only [maskFrame, prefixCount, lt_min_iff, i.isLt, and_true]

theorem prefix_clock_one_fresh_column (n r : ℕ) :
    prefixCount n r ≤ prefixCount n (r + 1) ∧ prefixCount n (r + 1) ≤ prefixCount n r + 1 := by
  unfold prefixCount
  omega

theorem initialFrame_eq_mask_first (n : ℕ) (initial : E) (V : Fin (n + 3) → E) (hinit : initial = V 0) :
    initialFrame n initial = maskFrame n 1 V := by
  funext i
  by_cases hi : i = 0
  · subst i
    simp only [initialFrame, Function.update_self, maskFrame, Fin.val_zero, Nat.zero_lt_one, if_true, hinit]
  · have hv : ¬i.val < 1 := by
      have hn : i.val ≠ 0 := by intro he; exact hi (Fin.ext he)
      omega
    simp only [initialFrame, Function.update_of_ne hi, Pi.zero_apply, maskFrame, if_neg hv]

theorem learnedFrame_of_actual_execution
    (n : ℕ) (initial : E) (choose : ℕ → AugHistory n E → Query E)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0) (r : ℕ) :
    learnedFrame n initial r (execution n choose oracle V r).1 = maskFrame n (r + 1) V := by
  cases r with
  | zero => simpa [learnedFrame] using initialFrame_eq_mask_first n initial V hinit
  | succ r => simp only [learnedFrame, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, execution, Function.update_self]

theorem prefixPoint_of_maskFrame (n cutoff : ℕ) (alpha : ℝ) (handle : E)
    (coeff : Fin (n + 3) → ℝ) (V : Fin (n + 3) → E) :
    prefixPoint n cutoff alpha handle coeff (maskFrame n cutoff V) = prefixPoint n cutoff alpha handle coeff V := by
  apply prefixPoint_respects_known_columns
  intro i hi
  simp only [maskFrame, if_pos hi]

theorem executed_query_formula
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0) (r : ℕ) :
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V r =
      if r < N then 0 else if r ≤ N + 1 then
        sOnlyQuery (a • (-(tau • prefixPoint n (r + 1) alpha handle coeff V) +
          (if r = N + 1 then offset else 0) • handle)) else 0 := by
  unfold executedQuery query
  rw [learnedFrame_of_actual_execution n initial _ oracle V hinit r, prefixPoint_of_maskFrame]

theorem zero_queries_before_hit
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0)
    (r : ℕ) (hr : r < N) :
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V r = 0 := by
  rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinit r, if_pos hr]

theorem actual_hit_and_transition_queries
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0) :
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V N =
      sOnlyQuery (a • (-(tau • prefixPoint n (N + 1) alpha handle coeff V))) ∧
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V (N + 1) =
      sOnlyQuery (a • (-(tau • prefixPoint n (N + 2) alpha handle coeff V) + offset • handle)) := by
  constructor
  · rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinit N]
    have hne : N ≠ N + 1 := by omega
    simp [hne]
  · rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinit (N + 1)]
    have hnot : ¬N + 1 < N := by omega
    simp [hnot, Nat.add_assoc]

theorem executed_queries_ignore_bundle
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle oracle' : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0) (r : ℕ) :
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V r =
      executedQuery n (query n N alpha tau a offset handle initial coeff) oracle' V r := by
  rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinit r,
    executed_query_formula n N alpha tau a offset handle initial coeff oracle' V hinit r]

theorem continuous_learnedFrame (n : ℕ) (initial : E) (r : ℕ) :
    Continuous (learnedFrame n initial r) := by
  change Continuous (fun history : AugHistory n E => if r = 0 then initialFrame n initial else (history (r - 1)).2)
  by_cases hr : r = 0
  · simp only [if_pos hr]
    exact continuous_const
  · simp only [if_neg hr]
    exact continuous_snd.comp (continuous_apply (r - 1))

theorem continuous_history_only_query
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ) (r : ℕ) :
    Continuous (query n N alpha tau a offset handle initial coeff r) := by
  unfold query
  by_cases hr : r < N
  · simp only [if_pos hr]; exact continuous_const
  · simp only [if_neg hr]
    by_cases hr2 : r ≤ N + 1
    · simp only [if_pos hr2]
      have hp := (continuous_prefixPoint n (r + 1) alpha handle coeff).comp (continuous_learnedFrame n initial r)
      have hc : Continuous (fun history : AugHistory n E =>
          a • (-(tau • prefixPoint n (r + 1) alpha handle coeff (learnedFrame n initial r history)) +
            (if r = N + 1 then offset else 0) • handle)) := by
        convert! ((hp.const_smul tau).neg.add continuous_const).const_smul a using 1
      exact (coordinateIsometry (E := E) ((2 : Fin 3), (0 : Fin 2))).continuous.comp hc
    · simp only [if_neg hr2]; exact continuous_const

theorem history_only_query_borel
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (Response E)] [BorelSpace (Response E)]
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ) (r : ℕ) :
    Measurable (query n N alpha tau a offset handle initial coeff r) := by
  exact (continuous_history_only_query n N alpha tau a offset handle initial coeff r).measurable

theorem sOnlyQuery_projection_zero (v s : E) (hs : inner ℝ v s = 0) (i : Fin 3 × Fin 2) :
    inner ℝ v (sOnlyQuery s i) = 0 := by
  by_cases hi : i = ((2 : Fin 3), (0 : Fin 2))
  · simp [sOnlyQuery, coordinateIsometry, hi, hs]
  · simp [sOnlyQuery, coordinateIsometry, PiLp.single_apply, hi]

theorem all_executed_query_unrevealed_projections_zero
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hV : Orthonormal ℝ V)
    (hinit : initial = V 0) (hhandle : ∀ j : Fin (n + 3), 1 ≤ j.val → inner ℝ (V j) handle = 0)
    (r : ℕ) (j : Fin (n + 3)) (hj : r + 1 ≤ j.val) (i : Fin 3 × Fin 2) :
    inner ℝ (V j) (executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V r i) = 0 := by
  rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinit r]
  have hh := hhandle j (by omega)
  have hp := prefixPoint_has_zero_unrevealed_projection n (r + 1) alpha handle coeff V hV j hj hh
  by_cases hr : r < N
  · rw [if_pos hr]
    change inner ℝ (V j) (0 : E) = 0
    exact inner_zero_right _
  · rw [if_neg hr]
    by_cases hr2 : r ≤ N + 1
    · rw [if_pos hr2]
      apply sOnlyQuery_projection_zero
      simp only [real_inner_smul_right, inner_add_right, inner_neg_right, hp, hh, mul_zero, neg_zero, zero_add]
    · rw [if_neg hr2]
      change inner ℝ (V j) (0 : E) = 0
      exact inner_zero_right _

theorem last_three_then_last_two_actual_history_queries
    (n : ℕ) (j : Fin (n + 3)) (hj : 3 ≤ j.val)
    (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle : Query E → Response E) (V : Fin (n + 3) → E) (hinit : initial = V 0) :
    let N := j.val - 3
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V N =
      sOnlyQuery (a • (-(tau • prefixPoint n (j.val - 2) alpha handle coeff V))) ∧
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V (N + 1) =
      sOnlyQuery (a • (-(tau • prefixPoint n (j.val - 1) alpha handle coeff V) + offset • handle)) := by
  dsimp only
  have h1 : j.val - 3 + 1 = j.val - 2 := by omega
  have h2 : j.val - 3 + 2 = j.val - 1 := by omega
  simpa only [h1, h2] using actual_hit_and_transition_queries n (j.val - 3) alpha tau a offset handle initial coeff oracle V hinit

theorem post_response_grant_is_exactly_one_column
    (n r : ℕ) (V : Fin (n + 3) → E) (hr : r + 1 < n + 3) :
    maskFrame n (r + 2) V =
      Function.update (maskFrame n (r + 1) V) ⟨r + 1, hr⟩ (V ⟨r + 1, hr⟩) := by
  funext i
  by_cases hi : i = ⟨r + 1, hr⟩
  · subst i
    simp [maskFrame]
  · rw [Function.update_of_ne hi]
    have hne : i.val ≠ r + 1 := by intro he; exact hi (Fin.ext he)
    unfold maskFrame
    split_ifs <;> first | rfl | omega

theorem post_response_grant_capped
    (n r : ℕ) (V : Fin (n + 3) → E) (hr : n + 3 ≤ r + 1) :
    maskFrame n (r + 2) V = maskFrame n (r + 1) V := by
  funext i
  have h1 : i.val < r + 1 := lt_of_lt_of_le i.isLt hr
  have h2 : i.val < r + 2 := by omega
  simp only [maskFrame, if_pos h1, if_pos h2]

theorem executed_query_respects_disclosed_prefix_across_oracles
    (n N : ℕ) (alpha tau a offset : ℝ) (handle initial : E) (coeff : Fin (n + 3) → ℝ)
    (oracle oracle' : Query E → Response E) (V U : Fin (n + 3) → E)
    (hinitV : initial = V 0) (hinitU : initial = U 0) (r : ℕ)
    (hpref : ∀ i, i.val < r + 1 → V i = U i) :
    executedQuery n (query n N alpha tau a offset handle initial coeff) oracle V r =
      executedQuery n (query n N alpha tau a offset handle initial coeff) oracle' U r := by
  rw [executed_query_formula n N alpha tau a offset handle initial coeff oracle V hinitV r,
    executed_query_formula n N alpha tau a offset handle initial coeff oracle' U hinitU r,
    prefixPoint_respects_known_columns n (r + 1) alpha handle coeff V U hpref]

def bundleOfFunction (F : Query E → ℝ) (z : Query E) : Response E :=
  (F z, gradient F z, fderiv ℝ (gradient F) z)

theorem execution_actual_augmented_response
    (n : ℕ) (choose : ℕ → AugHistory n E → Query E) (oracle : Query E → Response E)
    (V : Fin (n + 3) → E) (r : ℕ) :
    (execution n choose oracle V (r + 1)).1 r =
      (oracle (executedQuery n choose oracle V r), maskFrame n (r + 2) V) := by
  simp only [execution, Function.update_self, executedQuery]

theorem execution_actual_full_function_bundle
    (n : ℕ) (choose : ℕ → AugHistory n E → Query E) (F : Query E → ℝ)
    (V : Fin (n + 3) → E) (r : ℕ) :
    ((execution n choose (bundleOfFunction F) V (r + 1)).1 r).1 =
      (F (executedQuery n choose (bundleOfFunction F) V r),
        gradient F (executedQuery n choose (bundleOfFunction F) V r),
        fderiv ℝ (gradient F) (executedQuery n choose (bundleOfFunction F) V r)) := by
  rw [execution_actual_augmented_response]
  rfl

theorem last_three_then_two_exact_prefix_clock
    (n : ℕ) (j : Fin (n + 3)) (hj : 3 ≤ j.val) :
    let N := j.val - 3
    prefixCount n N = j.val - 2 ∧ prefixCount n (N + 1) = j.val - 1 ∧
      prefixCount n (N + 2) = j.val := by
  dsimp only [prefixCount]
  have hjlt := j.isLt
  omega

end
end FangqingLateAugmentedGrantProtocol
end

section
-- Source component: ActualAugmentedLateGateExecution.lean

namespace FangqingActualAugmentedLateGateExecution

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalCanonicalPacketTailSupport
  FangqingPhysicalHaarLastColumnFlip FangqingPhysicalHaarActualGateSeparation
  FangqingLateAugmentedGrantProtocol FangqingLateQueryFromHistory FangqingAdaptiveHaarProduct
  FangqingHaarColumnSignFlip FangqingOriginalF2PrefixAcquisition

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]

theorem actual_history_transition_query_is_canonical_transition_query
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (alpha tau a offset : ℝ) (z : Fin (n + 3) → ℝ) (j : Fin (n + 2)) (hj : 2 ≤ j.val)
    (oracle : Query (PhysicalSpace A B W) → Response (PhysicalSpace A B W)) :
    executedQuery n (query n (j.succ.val - 3) alpha tau a offset
      (mkPhysical h 0 0) (mkPhysical 0 (C h) 0) z) oracle (physicalFrame C h n tail)
        (j.succ.val - 3 + 1) = transitionPoint C h n tail alpha tau a offset z j := by
  have hinit : mkPhysical 0 (C h) (0 : W) = physicalFrame C h n tail 0 := rfl
  have hh := (last_three_then_last_two_actual_history_queries n j.succ
    (by simp only [Fin.val_succ]; omega) alpha tau a offset (mkPhysical h 0 0)
    (mkPhysical 0 (C h) 0) z oracle (physicalFrame C h n tail) hinit).2
  rw [← canonical_prefixPoint_is_granted_prefixPoint C h n tail alpha z (j.succ.val - 1)] at hh
  simpa only [Fin.val_succ, Nat.add_sub_cancel, transitionPoint, sOnlyQuery] using hh

theorem genuine_augmented_full_bundle_execution_retains_last_flip_obstruction
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (b : Fin (n + 2) → W)
    (j : Fin (n + 2)) (hj : 2 ≤ j.val) (alpha tau a offset : ℝ) (z : Fin (n + 3) → ℝ)
    (F : FangqingOrthogonalHaar.Group W → Query (PhysicalSpace A B W) → ℝ)
    (hseparation : ∀ g : FangqingOrthogonalHaar.Group W,
      FangqingShellPrefixLocality.bundle (F (g * flipColumn b j))
        (transitionPoint C h n (frame b (g * flipColumn b j)) alpha tau a offset z j) ≠
      FangqingShellPrefixLocality.bundle (F g)
        (transitionPoint C h n (frame b g) alpha tau a offset z j)) :
    let choose := query n (j.succ.val - 3) alpha tau a offset
      (mkPhysical h 0 0) (mkPhysical 0 (C h) 0) z
    let response := fun g : FangqingOrthogonalHaar.Group W =>
      FangqingShellPrefixLocality.bundle (F g)
        (executedQuery n choose (FangqingShellPrefixLocality.bundle (F g))
          (physicalFrame C h n (frame b g)) (j.succ.val - 3 + 1))
    ∀ g, response (g * flipColumn b j) ≠ response g := by
  intro choose response g
  dsimp only [response, choose]
  rw [actual_history_transition_query_is_canonical_transition_query C h n
    (frame b (g * flipColumn b j)) alpha tau a offset z j hj,
    actual_history_transition_query_is_canonical_transition_query C h n
      (frame b g) alpha tau a offset z j hj]
  exact hseparation g

end FangqingActualAugmentedLateGateExecution

namespace FangqingOwnGateRestoration

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def ownGateAtRound (gate : E → ℝ) (chamber : Set E)
    (queries : ℕ → E) (r : ℕ) : E → ℝ := by
  classical
  exact if ∃ k < r, queries k ∈ chamber then gate else fun _ => 0

theorem previous_chamber_hit_restores_actual_own_gate
    (gate : E → ℝ) (chamber : Set E) (queries : ℕ → E)
    (N : ℕ) (hhit : queries N ∈ chamber) :
    ownGateAtRound gate chamber queries (N + 1) = gate := by
  classical
  unfold ownGateAtRound
  exact if_pos ⟨N, by omega, hhit⟩

end FangqingOwnGateRestoration
end

section
-- Source component: CanonicalLateGateFamily.lean

namespace FangqingCanonicalLateGateFamily

open FangqingAmplifier FangqingPathEdgeRegularity FangqingInactiveShellClass
  FangqingLocalizedSeedJets FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalCanonicalPacketTailSupport FangqingRelayFenchelInterfaces
  FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  FangqingExternalPhysicalRelayValidity FangqingActualRelayDecoderInterfaces

structure Config (n : ℕ) where
  profile : FlatCubic.Profile
  phi : ℝ → ℝ
  q : ℝ
  delta : ℝ
  omega : ℝ
  scale : ℝ
  barlam : ℝ
  R : ℝ
  A : ℝ
  gain : ℝ
  seed : ℝ
  beta : ℝ
  lam : ℝ
  mu : ℝ
  a : ℝ
  sigma : ℝ
  reward : ℝ
  ell : ℝ

noncomputable section

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def publicPair {n : ℕ} (c : Config n) : ℝ × (Fin (n + 3) → ℝ) :=
  canonicalScalarPair c.profile c.delta c.omega n c.q c.barlam

def H0 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : A) (tail : Fin (n + 2) → W) :
    PhysicalSpace A B W → ℝ :=
  inactiveShell (QPhysical c.q (c.scale * c.barlam) C)
    (fun z => c.scale * pathEdge c.profile c.delta c.omega (n + 2) (physicalFrame C h n tail) z)
    c.R c.gain

def H1 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : A) (tail : Fin (n + 2) → W) :
    PhysicalSpace A B W → ℝ :=
  fun z => H0 c C h tail z - localizedSeed theta c.phi c.R c.A (c.seed * c.A) (mkPhysical h 0 0) z

def Z {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : A) (tail : Fin (n + 2) → W) :
    PhysicalSpace A B W := coordinatePoint C h n tail (publicPair c).1 (publicPair c).2

def h0 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : Fin 2 → PhysicalSpace A B W → ℝ :=
  fun t => reduced (H0 c C (h t) (tail t)) c.mu

def h1 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : Fin 2 → PhysicalSpace A B W → ℝ :=
  fun t => reduced (H1 c C (h t) (tail t)) c.mu

def m0 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : Fin 2 → ℝ := fun t => H0 c C (h t) (tail t) 0

def m1 {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : Fin 2 → ℝ :=
  fun t => H1 c C (h t) (tail t) (Z c C (h t) (tail t))

def gate {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : Fin 1 → PhysicalSpace A B W → ℝ :=
  fun _ => radialGate theta c.a c.ell (-((c.lam / c.beta) • Z c C (h 0) (tail 0)))

def J {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) : FlatJoint 1 (PhysicalSpace A B W) → ℝ :=
  assembled 1 c.beta c.lam c.a c.sigma c.reward (h0 c C h tail) (h1 c C h tail)
    (m0 c C h tail) (m1 c C h tail) (gate c C h tail)

def initialX {n : ℕ} (c : Config n) (h : Fin 2 → A) : Blocks 1 (PhysicalSpace A B W) :=
  WithLp.toLp 2 (Fin.cons ((-(c.seed / c.lam)) • mkPhysical (h 0) (0 : B) (0 : W)) (fun _ => 0))

def Valid {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) (L rho M Ctheta Cgap Egap : ℝ) : Prop :=
  Validity 1 c.beta c.lam c.a c.sigma c.reward L c.mu rho M Ctheta c.ell Cgap Egap
    (h0 c C h tail) (h1 c C h tail) (m0 c C h tail) (m1 c C h tail)
    (gate c C h tail) (initialX c h)

theorem actual_validity_supplies_actual_C2_and_reward_decoder
    {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B) (h : Fin 2 → A)
    (tail : Fin 2 → Fin (n + 2) → W) (L rho M Ctheta Cgap Egap Cdelta KD eps : ℝ)
    (hValid : Valid c C h tail L rho M Ctheta Cgap Egap)
    (hbeta : 0 < c.beta) (hmu : 0 < c.mu) (heps : 0 < eps) (hCD : 0 ≤ Cdelta)
    (hM : M = FangqingActualRelayScaling.rawBudget Cdelta 8 c.beta c.mu KD eps)
    (hReward : c.reward = FangqingActualRelayScaling.reward Cdelta 8 c.beta KD eps) :
    ContDiff ℝ 2 (J c C h tail) ∧
      ∀ point : FlatJoint 1 (PhysicalSpace A B W),
        coefficient 1 c.reward (h0 c C h tail) (h1 c C h tail) (m0 c C h tail) (m1 c C h tail)
          (fun t => point (1, t)) 0 ≠ 0 := by
  obtain ⟨hDelta, _, _, hJ, _⟩ := hValid
  refine ⟨hJ, ?_⟩
  intro point
  rw [hReward]
  apply actual_full_relay_gate_coefficient_is_nonzero Cdelta 8 c.beta c.mu KD eps hbeta hmu heps hCD
    (by norm_num) (h0 c C h tail) (h1 c C h tail) (m0 c C h tail) (m1 c C h tail)
  · simpa only [hM] using hDelta

end
end FangqingCanonicalLateGateFamily
end

section
-- Source component: CanonicalLateGateWorldFactory.lean

open scoped NNReal Topology

namespace FangqingCanonicalLateGateWorldFactory

open FangqingCanonicalLateGateFamily FangqingAmplifier FangqingActualRelayScaling
  FangqingThirdGroupScaling FangqingCanonicalRelayRegularityComplete
  FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  OriginalPacketDistanceGapBounds FangqingPublicShellProfiles FangqingRadialGateBounds
  FangqingExternalPhysicalRelayValidity

noncomputable section

set_option maxHeartbeats 8500000

def originalConfig
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (n : ℕ)
    (Ce : ℝ≥0) (K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q delta omega : ℝ) : Config n :=
  let Li := cL * L
  let ri := r / Real.sqrt cL
  let scale := cg * rhop
  let barlam := (8 * mu) / scale
  let D := distanceScale q omega
  let nu := scale * barlam
  let A := (1 + 2 * Ks * (2 * Cw) + 2 * Cw * (Cm + 2)) * D
  let a := relayAmplitude 1 (Li / mu) ri
  { profile := P, phi := phi, q := q, delta := delta, omega := omega,
    scale := scale, barlam := barlam, R := 2 * A, A := A,
    gain := (16 * K + 1) * ((4 * Ce : ℝ) * scale * omega),
    seed := (2 * Cw) * nu * D,
    beta := Li, lam := lam Li mu, mu := mu, a := a,
    sigma := sigma Li a csigma, reward := reward Cdelta 8 Li KD eps,
    ell := width Li mu KD eps }

universe u
variable {A B W : Type u}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

structure BuiltWorld {n : ℕ} (c : Config n) (C : A ≃ₗᵢ[ℝ] B)
    (h : Fin 2 → A) (tail : Fin 2 → Fin (n + 2) → W)
    (Cmin L rho M Ctheta Cgap Egap : ℝ) : Prop where
  inactive_minimum : ∀ t Y, H0 c C (h t) (tail t) 0 ≤ H0 c C (h t) (tail t) Y
  active_minimum : ∀ t Y, H1 c C (h t) (tail t) (Z c C (h t) (tail t)) ≤ H1 c C (h t) (tail t) Y
  minimum_norm : ∀ t, ‖Z c C (h t) (tail t)‖ ≤ Cmin * distanceScale c.q c.omega
  bulk : ∀ t (j : Fin (n + 3)), (j.val : ℝ) ≤ c.q →
    3 * c.q * c.omega ≤ inner ℝ
      (OriginalPacketOrientationNormalization.physicalFrame C (h t) n (tail t) j) (Z c C (h t) (tail t))
  valid : Valid c C h tail L rho M Ctheta Cgap Egap
  initial_gate_flat : ∀ j, gate c C h tail j =ᶠ[𝓝 (c.a • initialX c h j.castSucc)] (fun _ => 0)
  exact_dual_initial : ∀ yy ss : Fin 2 → PhysicalSpace A B W,
    family 1 c.beta c.lam c.a c.sigma c.reward (h0 c C h tail) (h1 c C h tail)
      (m0 c C h tail) (m1 c C h tail) (gate c C h tail) (initialX c h).ofLp yy ss ≤
    family 1 c.beta c.lam c.a c.sigma c.reward (h0 c C h tail) (h1 c C h tail)
      (m0 c C h tail) (m1 c C h tail) (gate c C h tail) (initialX c h).ofLp 0
      (fun t => c.a • initialX c h t)


theorem actual_original_world_factory
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
      ∀ (nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin 2 → A0)
        (tail : Fin 2 → Fin (nt + 2) → W)
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
        let c := originalConfig P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg
          L mu eps r rhop q delta omega
        BuiltWorld c C h tail (2 * Cw * (Cm + 2)) L (rho L mu eps r)
          (rawBudget Cdelta 8 Li mu KD eps) Ctheta Cgap (energy L eps) := by
  obtain ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, hBuilder⟩ :=
    actual_original_relay_has_public_canonical_minimizers.{u} P phi Bp left right Cm Cw b0
      hCm hCw hb0 hp hl hr hcore
  refine ⟨Ce, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hGap, hDeriv,
    cL, cq, cg, hcL, hcL1, hcq, hcq1, hcg, hcg1, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' nt C h tail
    L mu eps r rhop q delta omega hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn
    Li ri scale barlam homega hDistance c
  obtain ⟨hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hV, hFlat, hInit, hStat⟩ :=
    hBuilder A0 B0 W 1 nt C h tail L mu eps r rhop q delta omega hh ht
      hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn homega hDistance
  let oldgate : Fin 1 → PhysicalSpace A0 B0 W → ℝ := fun j =>
    scaledGate theta (c.a * c.ell) (c.a • ((-c.lam / c.beta) • Z c C (h j.castSucc) (tail j.castSucc)))
  have hGateEq : oldgate = gate c C h tail := by
    funext j y
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [oldgate, gate, scaledGate, radialGate, mul_pow, neg_div, neg_smul, Fin.castSucc_zero]
  change Validity 1 c.beta c.lam c.a c.sigma c.reward L c.mu (rho L mu eps r)
    (rawBudget Cdelta 8 Li mu KD eps) Ctheta c.ell Cgap (energy L eps)
      (h0 c C h tail) (h1 c C h tail) (m0 c C h tail) (m1 c C h tail) oldgate (initialX c h) at hV
  rw [hGateEq] at hV
  change (∀ j, oldgate j =ᶠ[𝓝 (c.a • initialX c h j.castSucc)] (fun _ => 0)) at hFlat
  rw [hGateEq] at hFlat
  change (∀ yy ss : Fin 2 → PhysicalSpace A0 B0 W,
    family 1 c.beta c.lam c.a c.sigma c.reward (h0 c C h tail) (h1 c C h tail)
      (m0 c C h tail) (m1 c C h tail) oldgate (initialX c h).ofLp yy ss ≤
    family 1 c.beta c.lam c.a c.sigma c.reward (h0 c C h tail) (h1 c C h tail)
      (m0 c C h tail) (m1 c C h tail) oldgate (initialX c h).ofLp 0
      (fun t => c.a • initialX c h t)) at hInit
  rw [hGateEq] at hInit
  exact ⟨hMin0, hMin1, hNorm, hBulk, hV, hFlat, hInit⟩

end
end FangqingCanonicalLateGateWorldFactory
end

section
-- Source component: HierarchyShellClass.lean

open scoped ContDiff NNReal Topology

namespace FangqingHierarchyShellClass

open FangqingInactiveShellClass FangqingRadialGateBounds FangqingGateBudgetBridge FangqingCutoffProductRegularity
  FangqingRadialCollar FangqingRadialCollarBounds FangqingPublicShellProfiles
  FangqingHessianStrongConvexity FangqingC2HessianAlgebra FangqingJetToRegularity
  FangqingHessianTensorIsometry FangqingC2ProductHessianBounds

set_option maxHeartbeats 2000000

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]


universe u

theorem universal_factor_four_shell_class :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (Q g : F → ℝ) (R nu LQ : ℝ) (M rho : ℝ≥0),
      0 < R → 0 ≤ LQ → ContDiff ℝ 2 Q → ContDiff ℝ 2 g →
      StrongConvexOn (Set.univ : Set F) nu Q → ConvexOn ℝ (Set.univ : Set F) g →
      (∀ z, ‖iteratedFDeriv ℝ 2 Q z‖ ≤ LQ) →
      (∀ x y, fderiv ℝ (fderiv ℝ Q) x = fderiv ℝ (fderiv ℝ Q) y) →
      (∀ z, ‖iteratedFDeriv ℝ 2 g z‖ ≤ M) → g 0 = 0 → fderiv ℝ g 0 = 0 →
      (∀ x y, ‖fderiv ℝ (fderiv ℝ g) x - fderiv ℝ (fderiv ℝ g) y‖ ≤ (rho : ℝ) * ‖x - y‖) →
      let gain := (64 * K + 1) * (M : ℝ)
      let H := inactiveShell Q g R gain
      4 * (16 * K * (M : ℝ)) ≤ gain ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * g z)) z‖ ≤ 16 * K * M) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * g z)) x -
        fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * g z)) y‖ ≤
        (K * rho + 21 * K * M / R) * ‖x - y‖) ∧
      (∀ z v, (3 / 2 : ℝ) * R ≤ ‖z‖ →
        4 * |fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * g z)) z v v| ≤
          gain * fderiv ℝ (fderiv ℝ (collar psi R)) z v v) ∧
      ContDiff ℝ 2 H ∧ StrongConvexOn (Set.univ : Set F) nu H ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ LQ + 16 * K * M + gain * Kc) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y‖ ≤
        (K * rho + 21 * K * M / R + gain * (Kc / R)) * ‖x - y‖) := by
  obtain ⟨K, hK, hcut⟩ := universal_actual_cutoff_jets.{u}
  have hpsi : ContDiff ℝ 2 psi := psi_smooth.of_le (by decide)
  obtain ⟨Kc, hKc, hcol⟩ := universal_scaled_collar_jets.{u} psi hpsi (3 / 2) (by norm_num)
    (fun t ht => psi_one t (by nlinarith only [ht]))
  refine ⟨K, hK, Kc, hKc, ?_⟩
  intro F inst inst' inst'' Q g R nu LQ M rho hR hLQ hQ hg hQs hgc hQ2 hQconst hg2 hg0 hgd0 hglip gain H
  let f : F → ℝ := scaledGate theta R 0
  have hf : ContDiff ℝ 3 f := scaledGate_contDiff theta R 0 hR (theta_smooth.of_le (by decide))
  obtain ⟨hprod, hprod2, hprodLip⟩ := cutoff_product_regularity f g hf hg R K M rho hR hK
    (fun j hj z => hcut F R hR z j hj) (actual_cutoff_zero_outside R hR) hg2 hg0 hgd0 hglip
  have hc3 : ContDiff ℝ 3 (collar (E := F) psi R) := collar_contDiff_three psi hpsi R
  have hc2 : ContDiff ℝ 2 (collar (E := F) psi R) := hc3.of_le (by norm_num)
  have hgain : 0 ≤ gain := by dsimp [gain]; positivity
  have hH : ContDiff ℝ 2 H := (hQ.add hprod).add (contDiff_const.mul hc2)
  have hform : ∀ z v : F, fderiv ℝ (fderiv ℝ H) z v v =
      fderiv ℝ (fderiv ℝ Q) z v v + fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z v v +
      gain * fderiv ℝ (fderiv ℝ (collar psi R)) z v v := by
    intro z v
    change fderiv ℝ (fderiv ℝ (fun z => Q z + f z * g z + gain * collar psi R z)) z v v = _
    rw [hessian_add _ _ (hQ.add hprod) (contDiff_const.mul hc2),
      hessian_add _ _ hQ hprod, hessian_const_mul _ hc2]
  have hSC : StrongConvexOn (Set.univ : Set F) nu H := by
    apply strongConvex_of_hessian_lower H nu hH
    intro z v
    rw [hform]
    have hq := hessian_lower_of_strongConvex Q nu hQ hQs z v
    have hcolpos := collar_hessian_nonneg psi hpsi psi_monotone (fun t => (psi_range t).1) R hR z v
    by_cases hz : ‖z‖ < (3 / 2 : ℝ) * R
    · have heq : (fun z => f z * g z) =ᶠ[𝓝 z] g := by
        have hopen := (isOpen_lt continuous_norm continuous_const).mem_nhds hz
        filter_upwards [hopen] with y hy
        rw [show f y = 1 from actual_cutoff_one_inside R hR y hy.le, one_mul]
      have hfirst : fderiv ℝ (fun z => f z * g z) =ᶠ[𝓝 z] fderiv ℝ g := heq.fderiv
      have heq2 : fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z = fderiv ℝ (fderiv ℝ g) z := hfirst.fderiv_eq
      rw [heq2]
      have hgpos := hessian_lower_of_strongConvex g 0 hg (strongConvexOn_zero.mpr hgc) z v
      simp only [zero_mul] at hgpos
      nlinarith only [hq, hgpos, mul_nonneg hgain hcolpos]
    · have hc := collar_hessian_outer_lower psi hpsi psi_monotone (3 / 2) R (by norm_num) hR
        (fun t ht => psi_one t (by nlinarith only [ht])) z v (le_of_not_gt hz)
      have hb := second_eval_bound _ (16 * K * M) (hprod2 z) v v
      have hb' := (abs_le.mp hb).1
      have hm := mul_le_mul_of_nonneg_left hc hgain
      dsimp [gain] at hm
      nlinarith only [hq, hb', hm, mul_nonneg M.coe_nonneg (sq_nonneg ‖v‖),
        mul_nonneg (mul_nonneg hK M.coe_nonneg) (sq_nonneg ‖v‖)]
  have hjet : ∀ z, iteratedFDeriv ℝ 2 H z =
      iteratedFDeriv ℝ 2 Q z + iteratedFDeriv ℝ 2 (fun z => f z * g z) z +
      gain • iteratedFDeriv ℝ 2 (collar psi R) z := by
    intro z
    change iteratedFDeriv ℝ 2 (fun z => Q z + f z * g z + gain * collar psi R z) z = _
    rw [fun_iteratedFDeriv_add_apply (hQ.add hprod).contDiffAt (contDiff_const.mul hc2).contDiffAt,
      fun_iteratedFDeriv_add_apply hQ.contDiffAt hprod.contDiffAt]
    have hh := iteratedFDeriv_const_smul_apply' (a := gain) hc2.contDiffAt (x := z)
    change iteratedFDeriv ℝ 2 (fun z => gain * collar psi R z) z = _ at hh
    rw [hh]
  have hH2 : ∀ z, ‖iteratedFDeriv ℝ 2 H z‖ ≤ LQ + 16 * K * M + gain * Kc := by
    intro z
    rw [hjet]
    have hp2 : ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) z‖ ≤ 16 * K * M := by
      rw [← hessian_norm_eq_second_jet]
      exact hprod2 z
    have hh := norm_add_le
      (iteratedFDeriv ℝ 2 Q z + iteratedFDeriv ℝ 2 (fun z => f z * g z) z)
      (gain • iteratedFDeriv ℝ 2 (collar psi R) z)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgain] at hh
    have hh1 := norm_add_le (iteratedFDeriv ℝ 2 Q z) (iteratedFDeriv ℝ 2 (fun z => f z * g z) z)
    exact hh.trans (add_le_add (hh1.trans (add_le_add (hQ2 z) hp2))
      (mul_le_mul_of_nonneg_left (hcol F R hR z).2.1 hgain))
  have hDom : 4 * (16 * K * (M : ℝ)) ≤ gain := by
    dsimp [gain]
    nlinarith only [M.coe_nonneg]
  have hAnnular : ∀ z v : F, (3 / 2 : ℝ) * R ≤ ‖z‖ →
      4 * |fderiv ℝ (fderiv ℝ (fun z => f z * g z)) z v v| ≤
        gain * fderiv ℝ (fderiv ℝ (collar psi R)) z v v := by
    intro z v hz
    have hc := collar_hessian_outer_lower psi hpsi psi_monotone (3 / 2) R (by norm_num) hR
      (fun t ht => psi_one t (by nlinarith only [ht])) z v hz
    have hb := second_eval_bound _ (16 * K * M) (hprod2 z) v v
    have hm := mul_le_mul_of_nonneg_right hDom (sq_nonneg ‖v‖)
    have hcm := mul_le_mul_of_nonneg_left hc hgain
    nlinarith only [hb, hm, hcm]
  refine ⟨hDom, hprod2, hprodLip, hAnnular, hH, hSC, hH2, ?_⟩
  intro x y
  have hQjet : iteratedFDeriv ℝ 2 Q x = iteratedFDeriv ℝ 2 Q y := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [second_jet_difference_eq_hessian, hQconst x y, sub_self]
    exact ContinuousLinearMap.opNorm_zero
  have hprodjet : ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) x -
      iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖ ≤ (K * rho + 21 * K * M / R) * ‖x - y‖ := by
    rw [second_jet_difference_eq_hessian]
    exact hprodLip x y
  let Rc : ℝ≥0 := ⟨Kc / R, by positivity⟩
  have hcolLip := second_jet_lipschitz_from_third_jet (collar (E := F) psi R) hc3 Rc
    (fun z => (hcol F R hR z).2.2)
  have heq : iteratedFDeriv ℝ 2 H x - iteratedFDeriv ℝ 2 H y =
      (iteratedFDeriv ℝ 2 (fun z => f z * g z) x - iteratedFDeriv ℝ 2 (fun z => f z * g z) y) +
      gain • (iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y) := by
    rw [hjet x, hjet y, hQjet, smul_sub]
    abel
  rw [heq]
  have hh := norm_add_le
    (iteratedFDeriv ℝ 2 (fun z => f z * g z) x - iteratedFDeriv ℝ 2 (fun z => f z * g z) y)
    (gain • (iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hgain] at hh
  have hcpoint : ‖iteratedFDeriv ℝ 2 (collar psi R) x - iteratedFDeriv ℝ 2 (collar psi R) y‖ ≤
      (Kc / R) * ‖x - y‖ := hcolLip.norm_sub_le x y
  have hc := mul_le_mul_of_nonneg_left hcpoint hgain
  have hb := hh.trans (add_le_add hprodjet hc)
  convert! hb using 1 <;> try ring

end
end FangqingHierarchyShellClass
end

section
-- Source component: HierarchySeedWidth.lean

open scoped ContDiff

namespace FangqingHierarchySeedWidth

open FangqingActualInactivePacket FangqingActiveShellClass FangqingLocalizedSeedJets
  FangqingC2SmallPerturbation FangqingHessianTensorIsometry FangqingPublicShellProfiles

noncomputable section

theorem actual_one_eighth_curvature (Ks Cs nu D A : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hnu : 0 ≤ nu) (hA : 0 < A)
    (hwidth : 8 * Ks * Cs * D ≤ A) :
    Ks * ((Cs * nu * D) * A) / A ^ 2 ≤ nu / 8 := by
  have heq : Ks * ((Cs * nu * D) * A) / A ^ 2 = Ks * Cs * nu * D / A := by
    field_simp [ne_of_gt hA]
    <;> try ring
  rw [heq]
  apply (div_le_iff₀ hA).mpr
  have hm := mul_le_mul_of_nonneg_left hwidth (by positivity : 0 ≤ nu / 8)
  convert! hm using 1 <;> try ring

theorem one_eighth_width_choice (Ks Cs Cmin D : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hCmin : 0 ≤ Cmin) (hD : 0 < D) :
    let A := (1 + 8 * Ks * Cs + Cmin) * D
    D ≤ A ∧ 8 * Ks * Cs * D ≤ A ∧ Cmin * D < A := by
  intro A
  have hk : 0 ≤ 8 * Ks * Cs := by positivity
  have hkD : 0 ≤ 8 * Ks * Cs * D := by positivity
  have hmD : 0 ≤ Cmin * D := by positivity
  dsimp [A]
  constructor
  · nlinarith only [hkD, hmD]
  constructor
  · nlinarith only [hmD, hD]
  · nlinarith only [hkD, hD]

universe u

theorem actual_seeded_shell_one_eighth
    (phi : ℝ → ℝ) (B left right Cs : ℝ) (hCs : 0 ≤ Cs)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (F : Type u)
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ (H0 : F → ℝ) (nu L0 rho0 D A R : ℝ) (handle : F),
      AnalyticClass H0 nu L0 rho0 → 0 ≤ nu → 0 ≤ L0 →
      0 < D → D ≤ A → 8 * Ks * Cs * D ≤ A → A ≤ R → ‖handle‖ ≤ 1 →
      let s := Cs * nu * D
      let H1 := fun z => H0 z - localizedSeed theta phi R A (s * A) handle z
      Ks * (s * A) / A ^ 2 ≤ nu / 8 ∧
      (∀ z, ‖fderiv ℝ (fderiv ℝ (localizedSeed theta phi R A (s * A) handle)) z‖ ≤ nu / 8) ∧
      AnalyticClass H1 (7 * nu / 8) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) := by
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
  have hsmall : S ≤ nu / 8 := actual_one_eighth_curvature Ks Cs nu D A hKs hCs hnu hA hwidth
  have hmod : 7 * nu / 8 ≤ nu - S := by linarith only [hsmall]
  refine ⟨hsmall, ?_, class_of_actual_jets H1 (7 * nu / 8) (L0 + S) (rho0 + T)
    (add_nonneg hL0 hS) hc (hsc.mono hmod) h2 hLip⟩
  intro z
  rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
  exact (hSJ 2 (by norm_num) z).trans hsmall

end
end FangqingHierarchySeedWidth
end

section
-- Source component: HierarchyPathData.lean

open scoped ContDiff

namespace FangqingHierarchyPathData

open FangqingPathEdgeRegularity

noncomputable section

universe u

theorem positive_actual_path_edge_regularity (P : FlatCubic.Profile) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧
      ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F],
      ∀ delta omega : ℝ, 0 < delta → delta ≤ omega →
      ∀ (n : ℕ) (v : Fin (n + 1) → F), Orthonormal ℝ v →
      ContDiff ℝ 2 (pathEdge P delta omega n v) ∧
      ConvexOn ℝ (Set.univ : Set F) (pathEdge P delta omega n v) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) z‖ ≤ (4 * Ce : ℝ) * omega) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) x -
        iteratedFDeriv ℝ 2 (pathEdge P delta omega n v) y‖ ≤ (8 * Ce : ℝ) * ‖x - y‖) ∧
      (∀ x y, ‖fderiv ℝ (fderiv ℝ (pathEdge P delta omega n v)) x -
        fderiv ℝ (fderiv ℝ (pathEdge P delta omega n v)) y‖ ≤ (8 * Ce : ℝ) * ‖x - y‖) := by
  obtain ⟨Ce0, hb⟩ := actual_pathEdge_regularity.{u} P
  let Ce := Ce0 + 1
  have hOne : 1 ≤ Ce := by
    change (1 : ℝ) ≤ (Ce0 : ℝ) + 1
    linarith only [Ce0.coe_nonneg]
  have hCe : (Ce0 : ℝ) ≤ (Ce : ℝ) := by
    change (Ce0 : ℝ) ≤ (Ce0 : ℝ) + 1
    linarith
  have h4 : (4 * Ce0 : ℝ) ≤ (4 * Ce : ℝ) := by exact_mod_cast mul_le_mul_of_nonneg_left hCe (by norm_num : (0 : ℝ) ≤ 4)
  have h8 : (8 * Ce0 : ℝ) ≤ (8 * Ce : ℝ) := by exact_mod_cast mul_le_mul_of_nonneg_left hCe (by norm_num : (0 : ℝ) ≤ 8)
  refine ⟨Ce, hOne, ?_⟩
  intro F inst inst' inst'' delta omega hd hdw n v hv
  obtain ⟨hc, hconv, h2, hJ, hH⟩ := hb F delta omega hd hdw n v hv
  have hw : 0 ≤ omega := (hd.trans_le hdw).le
  exact ⟨hc, hconv, fun z => (h2 z).trans (mul_le_mul_of_nonneg_right h4 hw),
    fun x y => (hJ x y).trans (mul_le_mul_of_nonneg_right h8 (norm_nonneg _)),
    fun x y => (hH x y).trans (mul_le_mul_of_nonneg_right h8 (norm_nonneg _))⟩

theorem edge_budget_dominates_curvature (Ce Cw q nu scale omega : ℝ)
    (hCe : 1 ≤ Ce) (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu)
    (hscale : scale * omega = Cw * nu * q ^ 2) :
    nu ≤ 4 * Ce * scale * omega := by
  have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
  have h1 := mul_le_mul_of_nonneg_left hq2 hnu
  have h2 := mul_le_mul_of_nonneg_right hCw (mul_nonneg hnu (sq_nonneg q))
  have hraw : nu ≤ scale * omega := by rw [hscale]; nlinarith only [h1, h2]
  have h4 : 1 ≤ 4 * Ce := by linarith only [hCe]
  have h3 := mul_le_mul_of_nonneg_right h4 (hnu.trans hraw)
  nlinarith only [hraw, h3]

theorem factor_four_full_hidden_reserve (K M nu S : ℝ)
    (hM : 0 ≤ M) (hnuM : nu ≤ M) (hS : S ≤ nu / 8) :
    4 * (16 * K * M + S) ≤ (64 * K + 1) * M := by
  nlinarith only [hM, hnuM, hS]

end
end FangqingHierarchyPathData
end

section
-- Source component: HierarchyInactivePacket.lean

open scoped ContDiff NNReal

namespace FangqingHierarchyInactivePacket

open FangqingActualInactivePacket FangqingAmplifier FangqingAmplifierRegularity FangqingPacketLeakage
  FangqingPathIncidenceBounds FangqingPathEdgeRegularity FangqingInactiveShellClass
  FangqingHessianTensorIsometry FangqingJetToRegularity FangqingHierarchyPathData FangqingHierarchyShellClass
  FangqingRadialGateBounds FangqingPublicShellProfiles FangqingUnlocalizedPacketRegularity

noncomputable section

set_option maxHeartbeats 3500000

universe u

def HessianNormBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℝ) (L : ℝ) : Prop :=
  ∀ z, ‖fderiv ℝ (fderiv ℝ f) z‖ ≤ L

theorem actual_factor_four_inactive_packet (P : FlatCubic.Profile) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧
    ∀ (A B W : Type u)
      [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
      [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W],
      ∀ (q nu scale delta omega R : ℝ) (C : A ≃ₗᵢ[ℝ] B)
      (n : ℕ) (v : Fin (n + 1) → PhysicalSpace A B W),
      0 ≤ q → 0 ≤ nu → 0 ≤ scale → 0 < delta → delta ≤ omega → 0 < R → Orthonormal ℝ v →
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (64 * K + 1) * M
      let H0 := inactiveShell (QPhysical q nu C) (fun z => scale * pathEdge P delta omega n v z) R gain
      4 * (16 * K * M) ≤ gain ∧
      HessianNormBound (fun z => scaledGate theta R 0 z * (scale * pathEdge P delta omega n v z)) (16 * K * M) ∧
      (∀ z w, (3 / 2 : ℝ) * R ≤ ‖z‖ →
        4 * |fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * (scale * pathEdge P delta omega n v z))) z w w| ≤
          gain * fderiv ℝ (fderiv ℝ (FangqingRadialCollar.collar psi R)) z w w) ∧
      AnalyticClass H0 nu (nu * (q + 2) + 16 * K * M + gain * Kc)
        (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 H0 z‖ ≤ nu * (q + 2) + 16 * K * M + gain * Kc) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 H0 x - iteratedFDeriv ℝ 2 H0 y‖ ≤
        (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)) * ‖x - y‖) ∧
      (∀ seedLin : PhysicalSpace A B W →L[ℝ] ℝ,
        AnalyticClass (FangqingUnlocalizedPacketRegularity.packet (QPhysical q nu C)
          (pathEdge P delta omega n v) scale seedLin) nu (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale)) := by
  obtain ⟨Ce, hOne, hCe⟩ := positive_actual_path_edge_regularity.{u} P
  obtain ⟨K, hK, Kc, hKc, hShell⟩ := universal_factor_four_shell_class.{u}
  refine ⟨Ce, hOne, K, hK, Kc, hKc, ?_⟩
  intro A B W inst inst' inst'' instB instB' instB'' instW instW' instW''
    q nu scale delta omega R C n v hq hnu hscale hd hdD hR hv M gain H0
  have homega : 0 < omega := hd.trans_le hdD
  obtain ⟨hgc, hgv, hg2, hg0, hgd0, hgLip⟩ := actual_scaled_path_data P Ce hCe
    delta omega scale hd hdD hscale n v hv
  let Mn : ℝ≥0 := ⟨M, by dsimp [M]; positivity⟩
  let rn : ℝ≥0 := ⟨(8 * Ce : ℝ) * scale, by positivity⟩
  have hQc := physical_quadratic_contDiff (W := W) q nu C
  have hQs := physical_quadratic_strongConvex (W := W) q nu hq hnu C
  have hQconst : ∀ x y : PhysicalSpace A B W,
      fderiv ℝ (fderiv ℝ (QPhysical q nu C)) x = fderiv ℝ (fderiv ℝ (QPhysical q nu C)) y := by
    intro x y
    rw [physical_quadratic_hessian_constant, physical_quadratic_hessian_constant]
  obtain ⟨hDom, hprod2, hprodLip, hAnnular, hHc, hHs, hH2, hHLip⟩ := hShell (PhysicalSpace A B W)
    (QPhysical q nu C) (fun z => scale * pathEdge P delta omega n v z) R nu (nu * (q + 2)) Mn rn
    hR (by positivity) hQc hgc hQs hgv (physical_quadratic_second_jet_bound q nu hq hnu C)
    hQconst hg2 hg0 hgd0 hgLip
  have hRawAll : ∀ seedLin : PhysicalSpace A B W →L[ℝ] ℝ,
      AnalyticClass (FangqingUnlocalizedPacketRegularity.packet (QPhysical q nu C)
        (pathEdge P delta omega n v) scale seedLin) nu (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale) := by
    intro seedLin
    obtain ⟨hec, heconv, he2, heJ, heH⟩ := hCe (PhysicalSpace A B W) delta omega hd hdD n v hv
    let Raw := FangqingUnlocalizedPacketRegularity.packet (QPhysical q nu C) (pathEdge P delta omega n v) scale seedLin
    have hRc : ContDiff ℝ 2 Raw := packet_contDiff _ _ scale seedLin hQc hec
    have hRs : StrongConvexOn (Set.univ : Set (PhysicalSpace A B W)) nu Raw :=
      packet_strongConvex _ _ scale nu seedLin hscale hQc hec hQs heconv
    have hR2 : ∀ z, ‖iteratedFDeriv ℝ 2 Raw z‖ ≤ nu * (q + 2) + M := by
      intro z
      have hh := packet_second_jet_bound (QPhysical q nu C) (pathEdge P delta omega n v) scale
        (nu * (q + 2)) ((4 * Ce : ℝ) * omega) seedLin hscale hQc hec
        (physical_quadratic_second_jet_bound q nu hq hnu C) he2 z
      convert! hh using 1 <;> dsimp [M] <;> try ring
    have hRLip : ∀ x y, ‖iteratedFDeriv ℝ 2 Raw x - iteratedFDeriv ℝ 2 Raw y‖ ≤
        ((8 * Ce : ℝ) * scale) * ‖x - y‖ := by
      intro x y
      rw [second_jet_difference_eq_hessian]
      have hh := packet_hessian_lipschitz (QPhysical q nu C) (pathEdge P delta omega n v) scale
        (8 * Ce : ℝ) seedLin hscale hQc hec hQconst heJ x y
      convert! hh using 1 <;> try ring
    exact class_of_actual_jets Raw nu _ _ (by dsimp [M]; positivity) hRc hRs hR2 hRLip
  exact ⟨hDom, hprod2, hAnnular, class_of_actual_jets H0 nu _ _ (by dsimp [M, gain]; positivity)
    hHc hHs hH2 hHLip, hH2, hHLip, hRawAll⟩



end
end FangqingHierarchyInactivePacket
end

section
-- Source component: HierarchyPairedShell.lean

open scoped BigOperators ContDiff Topology

namespace FangqingHierarchyPairedShell

open FangqingAmplifier FangqingPacketLeakage FangqingPathEdgeRegularity
  FangqingActualInactivePacket FangqingInactiveShellClass FangqingLocalizedSeedJets
  FangqingHierarchySeedWidth FangqingShellMinimizerTransfer FangqingHierarchyInactivePacket FangqingHierarchyPathData FangqingInactiveShellMinimum
  FangqingPublicShellProfiles FangqingRadialGateBounds OriginalPacketOrientationNormalization
  OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds

set_option maxHeartbeats 3000000

noncomputable section

universe u

theorem chamber_safe_width_choice (Ks Cs Cmin D : ℝ)
    (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs) (hCmin : 0 ≤ Cmin) (hD : 0 < D) :
    let A := (3 + 8 * Ks * Cs + Cmin) * D
    D ≤ A ∧ 8 * Ks * Cs * D ≤ A ∧ Cmin * D < A ∧ (Cmin + 2) * D < A := by
  intro A
  have hK : 0 ≤ 8 * Ks * Cs * D := by positivity
  have hm : 0 ≤ Cmin * D := by positivity
  dsimp [A]
  constructor
  · nlinarith only [hK, hm, hD]
  constructor
  · nlinarith only [hm, hD]
  constructor <;> nlinarith only [hK, hD]

theorem sub_hessian_norm_bound {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (f g : F → ℝ) (A B : ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hF : HessianNormBound f A) (hG : HessianNormBound g B) :
    HessianNormBound (fun z => f z - g z) (A + B) := by
  intro z
  rw [FangqingJetToRegularity.hessian_norm_eq_second_jet,
    fun_iteratedFDeriv_sub_apply hf.contDiffAt hg.contDiffAt]
  apply (norm_sub_le _ _).trans
  rw [← FangqingJetToRegularity.hessian_norm_eq_second_jet,
    ← FangqingJetToRegularity.hessian_norm_eq_second_jet]
  exact add_le_add (hF z) (hG z)

theorem actual_hierarchy_physical_paired_shell
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧
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
      let A := (3 + 8 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let g := fun z => scale * pathEdge P delta omega (n + 2) (physicalFrame C h n tail) z
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (64 * K + 1) * M
      let F0 := inactiveShell Q g R gain
      let F1 := fun z => F0 z - localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) z
      let L0 := nu * (q + 2) + 16 * K * M + gain * Kc
      let rho0 := K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)
      Ks * (s * A) / A ^ 2 ≤ nu / 8 ∧
      HessianNormBound (localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W))) (nu / 8) ∧
      4 * (16 * K * M + nu / 8) ≤ gain ∧
      HessianNormBound (fun z => scaledGate theta R 0 z * g z -
        localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) z) (16 * K * M + nu / 8) ∧
      (∀ z w, (3 / 2 : ℝ) * R ≤ ‖z‖ →
        4 * |fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * g z -
          localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) z)) z w w| ≤
          gain * fderiv ℝ (fderiv ℝ (FangqingRadialCollar.collar psi R)) z w w) ∧
      (∀ seedLin : PhysicalSpace A0 B0 W →L[ℝ] ℝ,
        AnalyticClass (FangqingUnlocalizedPacketRegularity.packet Q
          (pathEdge P delta omega (n + 2) (physicalFrame C h n tail)) scale seedLin)
          nu (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale)) ∧
      AnalyticClass F0 nu L0 rho0 ∧
      AnalyticClass F1 (7 * nu / 8) (L0 + Ks * (s * A) / A ^ 2) (rho0 + Ks * (s * A) / A ^ 3) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
          rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧
        F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) ∧
        (∀ Y, ‖Y - Z‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R) ∧
        (∀ Y, ‖Y - Z‖ ≤ 2 * D → F1 =ᶠ[𝓝 Y]
          (fun y => Q y + g y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) y)) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ 2 * Cw := by positivity
  have hCmin : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
  obtain ⟨Ce, hCeOne, K, hK, Kc, hKc, hInactive⟩ := actual_factor_four_inactive_packet.{u} P
  obtain ⟨Ks, hKs, hWide⟩ := actual_seeded_shell_one_eighth.{u} phi Bp left right (2 * Cw) hCs hp hl hr
  refine ⟨Ce, hCeOne, K, hK, Kc, hKc, Ks, hKs, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn nu D Cs Cmin A R s Q g M gain F0 F1 L0 rho0
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hwidth, hCminA, hChamberA⟩ := chamber_safe_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hR : 0 < R := hA.trans_le hAR
  have hv := physicalFrame_orthonormal C h hh n tail ht
  obtain ⟨hEdgeDom, hCutH, hEdgeAnnular, hF0, _, _, hRawAll⟩ := hInactive A0 B0 W q nu scale delta omega R C (n + 2) (physicalFrame C h n tail)
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
  obtain ⟨hSeedSmall, hSeedH, hF1⟩ := hWide (PhysicalSpace A0 B0 W) F0 nu L0 rho0 D A R (mkPhysical h (0 : B0) (0 : W))
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
  have hCwOne : 1 ≤ Cw := by linarith only [hCm, hCw]
  have hScaleOmega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; dsimp [nu]; ring
  have hMnu : nu ≤ M := edge_budget_dominates_curvature (Ce : ℝ) Cw q nu scale omega
    (by exact_mod_cast hCeOne) hCwOne hq hnu.le hScaleOmega
  have hFullDom : 4 * (16 * K * M + nu / 8) ≤ gain :=
    factor_four_full_hidden_reserve K M nu (nu / 8) (by dsimp [M]; positivity) hMnu le_rfl
  let cut := fun z : PhysicalSpace A0 B0 W => scaledGate theta R 0 z * g z
  let seedF := localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W))
  let hidden := fun z => cut z - seedF z
  have hcutC : ContDiff ℝ 2 cut :=
    ((FangqingGateBudgetBridge.scaledGate_contDiff theta R 0 hR
      (theta_smooth.of_le (by decide))).of_le (by norm_num)).mul
      (contDiff_const.mul (pathEdge_contDiff P delta omega hd hdw (n + 2) (physicalFrame C h n tail)))
  have hseedC : ContDiff ℝ 2 seedF :=
    (localizedSeed_contDiff theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) hR
      (theta_smooth.of_le (by decide)) hp).of_le (by norm_num)
  have hHidden : HessianNormBound hidden (16 * K * M + nu / 8) :=
    sub_hessian_norm_bound cut seedF (16 * K * M) (nu / 8) hcutC hseedC hCutH hSeedH
  have hFullAnn : ∀ z w : PhysicalSpace A0 B0 W, (3 / 2 : ℝ) * R ≤ ‖z‖ →
      4 * |fderiv ℝ (fderiv ℝ hidden) z w w| ≤
        gain * fderiv ℝ (fderiv ℝ (FangqingRadialCollar.collar psi R)) z w w := by
    intro z w hz
    have hc := FangqingRadialCollar.collar_hessian_outer_lower psi
      (psi_smooth.of_le (by decide)) psi_monotone (3 / 2) R (by norm_num) hR
      (fun t ht => psi_one t (by nlinarith only [ht])) z w hz
    have hb : |fderiv ℝ (fderiv ℝ hidden) z w w| ≤ (16 * K * M + nu / 8) * ‖w‖ * ‖w‖ :=
      FangqingC2ProductHessianBounds.second_eval_bound (fderiv ℝ (fderiv ℝ hidden) z)
        (16 * K * M + nu / 8) (hHidden z) w w
    have hm := mul_le_mul_of_nonneg_right hFullDom (sq_nonneg ‖w‖)
    have hcm := mul_le_mul_of_nonneg_left hc hGain
    nlinarith only [hb, hm, hcm]
  refine ⟨hSeedSmall, hSeedH, hFullDom, hHidden, hFullAnn, hRawAll, hF0, hF1, hMin0, ?_⟩
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
  obtain ⟨hm1, hu1⟩ := actual_active_minimizer_preserved Q g phi R A s gain (7 * nu / 8) hR hA (by positivity)
    (mkPhysical h (0 : B0) (0 : W)) Z hhandle hcore hzR hzA hrawmin hF1.1 hF1.2.1
  have hzval := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h (0 : B0) (0 : W)) Z hhandle hcore hzR hzA
  have h0val := actual_active_shell_inner_eq Q g phi R A s gain hR hA (mkPhysical h (0 : B0) (0 : W)) (0 : PhysicalSpace A0 B0 W)
    hhandle hcore (by simpa using hR) (by simpa using hA)
  have hChamber : ∀ Y : PhysicalSpace A0 B0 W, ‖Y - Z‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R := by
    intro Y hY
    have htri : ‖Y‖ ≤ ‖Y - Z‖ + ‖Z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (Y - Z) Z
    have hZ : ‖Z‖ ≤ Cmin * D := hnorm
    have hYA : ‖Y‖ < A := by nlinarith only [htri, hY, hZ, hChamberA]
    exact ⟨hYA, hYA.trans_le hAR⟩
  have hChamberEq : ∀ Y : PhysicalSpace A0 B0 W, ‖Y - Z‖ ≤ 2 * D →
      F1 =ᶠ[𝓝 Y] (fun y => Q y + g y - s * inner ℝ (mkPhysical h (0 : B0) (0 : W)) y) := by
    intro Y hY
    exact actual_active_shell_eventually_eq_raw Q g phi R A s gain hR hA (mkPhysical h (0 : B0) (0 : W))
      Y hhandle hcore (hChamber Y hY).2 (hChamber Y hY).1
  refine ⟨Z, hm, hm1, hu1, hnorm, ?_, hbulk, hChamber, hChamberEq⟩
  change (inactiveShell Q g R gain 0 - localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) 0) -
    (inactiveShell Q g R gain Z - localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W)) Z) ≤ _
  rw [hzval, h0val, ← hRaw Z, ← hRaw 0]
  exact hgap

end
end FangqingHierarchyPairedShell
end

section
-- Source component: HierarchyRelayComponents.lean

open scoped ContDiff

namespace FangqingHierarchyRelayComponents

open FangqingRelayAnalyticAssembly FangqingRelayGlobalJointClass FangqingRelayFenchelInterfaces
  FangqingFenchelEndpointClass FangqingActualInactivePacket FangqingRelayStationarity
  FangqingLocalizedSeedJets FangqingActualRelayLink FangqingPublicShellProfiles
  FangqingRadialGateBounds FangqingGateBudgetBridge FangqingHierarchyInactivePacket
  FangqingDisjointBlockBounds FangqingRelayBlockGeometry FangqingC2BlockRegularity

noncomputable section

set_option maxHeartbeats 4000000

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_packet_endpoint_component_data (H : E → ℝ) (beta c lam m nu LH rhoH : ℝ)
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

theorem actual_relay_components_and_class (phi : ℝ → ℝ) (B left right : ℝ)
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
      (∀ t, ContDiff ℝ 2 (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h0 t) (m0 t) p.fst p.snd)) ∧
      (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h0 t) (m0 t) p.fst p.snd)
        (beta + c + 2 * |lam| + LH)) ∧
      (∀ t, ContDiff ℝ 2 (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h1 t) (m1 t) p.fst p.snd)) ∧
      (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h1 t) (m1 t) p.fst p.snd)
        (beta + c + 2 * |lam| + LH)) ∧
      HessianNormBound (localRelay (E := F) a sigma) (sigma * (1 + a ^ 2)) ∧
      FangqingFenchelEndpointClass.HessianRate (localRelay (E := F) a sigma) 0 ∧
      (∀ j, ContDiff ℝ 3 (localLink n reward h0 h1 m0 m1 gate j)) ∧
      (∀ j z, ‖iteratedFDeriv ℝ 2 (localLink n reward h0 h1 m0 m1 gate j) z‖ ≤ Ll) ∧
      (∀ j z, ‖iteratedFDeriv ℝ 3 (localLink n reward h0 h1 m0 m1 gate j) z‖ ≤ Rl) ∧
      HessianNormBound (blockSum (packet n) (localPacket n beta lam h0 h1 m0 m1))
        (beta + c + 2 * |lam| + LH) ∧
      HessianNormBound (blockSum (relay n) (fun _ : Fin (n + 1) => localRelay (E := F) a sigma))
        (sigma * (1 + a ^ 2)) ∧
      HessianNormBound (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) Ll ∧
      (∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) z‖ ≤ Rl) ∧
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
  have hEnd0 := fun t => actual_packet_endpoint_component_data (H0 t) beta c lam (m0 t) nu LH rhoH hb hc hLH hrho (hH0 t)
  have hEnd1 := fun t => actual_packet_endpoint_component_data (H1 t) beta c lam (m1 t) nu LH rhoH hb hc hLH hrho (hH1 t)
  have hEnd0H : ∀ t, HessianNormBound
      (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h0 t) (m0 t) p.fst p.snd)
      (beta + c + 2 * |lam| + LH) := by
    intro t p
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact (hEnd0 t).2.1 p
  have hEnd1H : ∀ t, HessianNormBound
      (fun p : FangqingRelayBlockGeometry.Pair F => endpoint beta lam (h1 t) (m1 t) p.fst p.snd)
      (beta + c + 2 * |lam| + LH) := by
    intro t p
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact (hEnd1 t).2.1 p
  have hLocal : ∀ t,
      ContDiff ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) z‖ ≤ beta + c + 2 * |lam| + LH) ∧
      (∀ x y, ‖iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) x -
        iteratedFDeriv ℝ 2 (localPacket n beta lam h0 h1 m0 m1 t) y‖ ≤ rhoH * ‖x - y‖) := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · exact actual_packet_endpoint_component_data (H1 0) beta c lam (m1 0) nu LH rhoH hb hc hLH hrho (hH1 0)
    · exact actual_packet_endpoint_component_data (H0 j.succ) beta c lam (m0 j.succ) nu LH rhoH hb hc hLH hrho (hH0 j.succ)
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
  have hRelayH : HessianNormBound (localRelay (E := F) a sigma) (sigma * (1 + a ^ 2)) := by
    intro p
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact relay_actual_second_jet a sigma hsigma.le p
  have hRelayR : FangqingFenchelEndpointClass.HessianRate (localRelay (E := F) a sigma) 0 := by
    intro x y
    rw [← FangqingHessianTensorIsometry.second_jet_difference_eq_hessian, relay_actual_second_jet_lip]
    simp only [zero_mul]
    exact le_rfl
  have hPacketGlobal : HessianNormBound (blockSum (packet n) (localPacket n beta lam h0 h1 m0 m1))
      (beta + c + 2 * |lam| + LH) := by
    intro z
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact second_blockSum_bound_c2 _ _ (fun t => (hLocal t).1) (packet_energy n) _
      (by positivity) z (fun t => (hLocal t).2.1 _)
  have hRelayGlobal : HessianNormBound (blockSum (relay n)
      (fun _ : Fin (n + 1) => localRelay (E := F) a sigma)) (sigma * (1 + a ^ 2)) := by
    intro z
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact second_blockSum_bound_c2 _ _ (fun _ => relay_contDiff a sigma) (relay_energy n) _
      (by positivity) z (fun _ => relay_actual_second_jet a sigma hsigma.le _)
  have hLinkGlobal : HessianNormBound (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) Ll := by
    intro z
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact second_blockSum_bound _ _ (fun j => (hLinks j).2.2.2.2.2.1) (link_energy n) Ll hLl z
      (fun j => (hLinks j).2.2.2.2.2.2.1 _)
  have hLinkThird : ∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) z‖ ≤ Rl := by
    intro z
    exact third_blockSum_bound _ _ (fun j => (hLinks j).2.2.2.2.2.1) (link_energy n) Rl hRl z
      (fun j => (hLinks j).2.2.2.2.2.2.2 _)
  refine ⟨(fun t => (hEnd0 t).1), hEnd0H, (fun t => (hEnd1 t).1), hEnd1H, hRelayH, hRelayR,
    (fun j => (hLinks j).2.2.2.2.2.1), (fun j => (hLinks j).2.2.2.2.2.2.1),
    (fun j => (hLinks j).2.2.2.2.2.2.2), hPacketGlobal, hRelayGlobal, hLinkGlobal, hLinkThird, hDeltaAll, (fun j z => (hLinks j).2.1 z), hJ, hJgrad, hJhess, ?_⟩
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
end FangqingHierarchyRelayComponents
end

section
-- Source component: HierarchyScalarReserves.lean

namespace FangqingHierarchyScalarReserves

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
  let csigma := 5 + 4 * (Kg + Kh) * (3 * C * 8 + 1) + 4 * Kh ^ 2 * C ^ 2 * 8 ^ 2 + csigmaExtra
  let Clink := C * 8 * (1 + 2 * Kg) + csigma / 2
  have hthird : 0 ≤ 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) := by positivity
  have hKD : 1 ≤ KD := by dsimp [KD]; linarith only [hKDlower, hthird]
  have hKDl : KDlower ≤ KD := by dsimp [KD]; linarith only [hthird]
  have hres3 : 16 * (1 + 3 * Kg) * (3 * C * 8 + 1) ≤ KD := by dsimp [KD]; linarith only [hKDlower]
  have hpureNon : 0 ≤ 4 * (Kg + Kh) * (3 * C * 8 + 1) := by positivity
  have hschurNon : 0 ≤ 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 := by positivity
  have hcs : 0 < csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon, hExtra]
  have hresSigma : 4 * (1 : ℝ) ^ 2 ≤ csigma := by dsimp [csigma]; linarith only [hpureNon, hschurNon, hExtra]
  have hresSchur : 4 * Kh ^ 2 * C ^ 2 * (8 : ℝ) ^ 2 ≤ csigma := by
    dsimp [csigma]; linarith only [hpureNon, hExtra]
  have hresKg : 2 * Kg * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKh (by positivity : 0 ≤ 4 * (3 * C * 8 + 1))
    have hhK : 0 ≤ 2 * Kg * (3 * C * 8 + 1) := by positivity
    dsimp [csigma]
    nlinarith only [hh, hhK, hschurNon, hExtra]
  have hresFourKh : 2 * (2 * Kh) * (3 * C * 8 + 1) ≤ csigma := by
    have hh := mul_nonneg hKg (by positivity : 0 ≤ 4 * (3 * C * 8 + 1))
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
  have hpureFour := actual_pure_gate_margin C 8 (2 * Kh) L mu KD eps a csigma hL hmu hKD heps ha0
    hC (by norm_num) (by positivity) hresFourKh
  have hpureStrong : totalBudget C 8 L mu KD eps * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 4 := by
    dsimp [ell]
    rw [mul_pow]
    have heq : totalBudget C 8 L mu KD eps * (2 * Kh / (a ^ 2 * width L mu KD eps ^ 2)) =
        2 * (totalBudget C 8 L mu KD eps * (Kh / (a ^ 2 * width L mu KD eps ^ 2))) := by ring
    rw [heq] at hpureFour
    linarith only [hpureFour]
  have hpure : totalBudget C 8 L mu KD eps * (Kh / (a * ell) ^ 2) ≤ sigma L a csigma / 2 :=
    hpureStrong.trans (by linarith only [hsig0])
  have hschur := actual_schur_margin Kh C 8 L mu KD eps a csigma hL hmu hKD0 heps ha0 hcs hresSchur
  refine ⟨hsigma, ?_, ?_, ?_, ?_⟩
  · convert! hpure using 1 <;> ring
  · exact hschur.trans (by linarith only [hmu])
  · exact actual_link_second_budget C 8 Kg L mu KD eps a csigma hC (by norm_num) hKg
      hmu hLmu hKD heps ha hresKg
  · exact actual_third_link_reserved_budget C 8 Kg 1 L mu KD eps r hC (by norm_num) hKg
      (by norm_num) hmu hLmu hKD heps hr hres3

end
end FangqingHierarchyScalarReserves
end

section
-- Source component: HierarchyUniformRelay.lean

open scoped ContDiff

namespace FangqingHierarchyUniformRelay

open FangqingHierarchyRelayComponents FangqingHierarchyInactivePacket
  FangqingDisjointBlockBounds FangqingRelayBlockGeometry FangqingRelayStationarity FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingActualRelayLinkBudgets FangqingHierarchyScalarReserves FangqingRelayAnalyticAssembly
  FangqingRelayFenchelInterfaces FangqingActualInactivePacket FangqingLocalizedSeedJets
  FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 4500000

universe u

theorem actual_uniform_relay_master (phi : ℝ → ℝ) (B left right Camp KDlower : ℝ)
    (hCamp : 0 ≤ Camp) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -B → phi t = left) (hr : ∀ t, B < t → phi t = right) :
    ∃ KD csigma Cglobal Cdelta Ctheta Clink : ℝ,
      1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧ 0 ≤ Cdelta ∧
      0 ≤ Ctheta ∧ 0 ≤ Clink ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
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
      (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair E =>
        endpoint L (lam L mu) (h0 t) (m0 t) p.fst p.snd) (4 * L + LH)) ∧
      (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair E =>
        endpoint L (lam L mu) (h1 t) (m1 t) p.fst p.snd) (4 * L + LH)) ∧
      HessianNormBound (blockSum (packet n) (localPacket n L (lam L mu) h0 h1 m0 m1)) (4 * L + LH) ∧
      HessianNormBound (blockSum (relay n) (fun _ : Fin (n + 1) => localRelay (E := E) a (sigma L a csigma))) (2 * csigma * L) ∧
      HessianNormBound (blockSum (link n) (localLink n rw h0 h1 m0 m1 gate)) (Clink * L) ∧
      (∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link n) (localLink n rw h0 h1 m0 m1 gate)) z‖ ≤ rho L mu eps r / 4) ∧
      ContDiff ℝ 2 J ∧
      (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + LH) * ‖x - y‖) ∧
      FangqingRelayGlobalJointClass.HessianRate J (rhoH + rho L mu eps r / 4) ∧
      (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) mu
        (FangqingRelayDualAssembly.negativeFamily n L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) := by
  obtain ⟨Kd, hKd, Kg, hKg, Kh, hKh, hFamily⟩ := actual_relay_components_and_class.{u} phi B left right hp hl hr
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
  refine ⟨KD, csigma, Cglobal, Cdelta, Ctheta, Clink, hKD, hKDl, hcs, (by dsimp [Cglobal]; positivity), hCdelta,
    hCt, hClink, htDeriv, hExtra, ?_⟩
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
  obtain ⟨hE0c, hE0h, hE1c, hE1h, hRh, hRr, hLc, hL2, hL3, hPG, hRG, hLG, hL3G, hDelta, hRange, hJ, hG, hH, hSC⟩ := hFamily E n L mu (lam L mu) a (sigma L a csigma) rw (4 * mu) mu LH rhoH
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
  refine ⟨?_, hRange, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hJ, ?_, ?_, hSC⟩
  · intro t z
    rw [← hRaw]
    exact hDelta t z
  · convert! hStationarityPure using 1 <;> unfold totalBudget <;> dsimp [rw] <;> ring
  · intro t z
    exact (hE0h t z).trans (by linarith only [hBase])
  · intro t z
    exact (hE1h t z).trans (by linarith only [hBase])
  · intro z
    exact (hPG z).trans (by linarith only [hBase])
  · intro z
    exact (hRG z).trans hQuadratic
  · intro z
    exact (hLG z).trans (by rw [hEq2]; exact hSecond)
  · intro z
    exact (hL3G z).trans (by rw [hEq3]; exact hThird)
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
end FangqingHierarchyUniformRelay
end

section
-- Source component: HierarchyScaleBudgets.lean

namespace FangqingHierarchyScaleBudgets

noncomputable section

theorem actual_hierarchy_rate_budgets (Ce K Kc Ks Cs Cw Cmin q nu scale omega D R : ℝ)
    (hCe : 0 ≤ Ce) (hK : 0 ≤ K) (hKc : 0 ≤ Kc) (hKs : 0 ≤ Ks) (hCs : 0 ≤ Cs)
    (hCmin : 0 ≤ Cmin) (hCw : 1 ≤ Cw) (hq : 1 ≤ q) (hnu : 0 ≤ nu) (hscale : 0 ≤ scale)
    (homega : 0 < omega) (hDomega : omega ≤ D)
    (hscaleomega : scale * omega = Cw * nu * q ^ 2)
    (hRA : (3 + 8 * Ks * Cs + Cmin) * D ≤ R) :
    let A := (3 + 8 * Ks * Cs + Cmin) * D
    let s := Cs * nu * D
    let M := 4 * Ce * scale * omega
    let gain := (64 * K + 1) * M
    let S := Ks * (s * A) / A ^ 2
    let T := Ks * (s * A) / A ^ 3
    nu * (q + 2) + 16 * K * M + gain * Kc + S ≤
      (7 / 2 + 4 * Ce * Cw * (16 * K + (64 * K + 1) * Kc)) * nu * q ^ 2 ∧
    K * (8 * Ce * scale) + 21 * K * M / R + gain * (Kc / R) + T ≤
      (8 * K * Ce + 4 * Ce * (21 * K + (64 * K + 1) * Kc) + Ks * Cs) * scale := by
  intro A s M gain S T
  have hD : 0 < D := homega.trans_le hDomega
  have hCA : 1 ≤ 3 + 8 * Ks * Cs + Cmin := by
    have hm : 0 ≤ 8 * Ks * Cs := by positivity
    linarith only [hm, hCmin]
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
  have hwidth : 8 * Ks * Cs * D ≤ A := by
    dsimp [A]
    nlinarith only [mul_nonneg hCmin hD.le, hD]
  have hS8 : S ≤ nu / 8 := FangqingHierarchySeedWidth.actual_one_eighth_curvature Ks Cs nu D A hKs hCs hnu hA hwidth
  have hS : S ≤ nu / 2 := by linarith only [hS8, hnu]
  have hqlinear : q + 2 ≤ 3 * q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hnulinear := mul_le_mul_of_nonneg_left hqlinear hnu
  have hfirst : nu * (q + 2) + S ≤ (7 / 2 : ℝ) * nu * q ^ 2 := by nlinarith only [hnulinear, hS, hnuq]
  have hMpart : 16 * K * M + gain * Kc =
      4 * Ce * Cw * (16 * K + (64 * K + 1) * Kc) * nu * q ^ 2 := by
    dsimp [gain, M]
    calc
      _ = 4 * Ce * (16 * K + (64 * K + 1) * Kc) * (scale * omega) := by ring
      _ = _ := by rw [hscaleomega]; ring
  have hRomega : omega ≤ R := hDomega.trans (hDA.trans hRA)
  have hMR : M / R ≤ 4 * Ce * scale := by
    apply (div_le_iff₀ hR).mpr
    exact mul_le_mul_of_nonneg_left hRomega (by positivity : 0 ≤ 4 * Ce * scale)
  have hmiddle := mul_le_mul_of_nonneg_left hMR
    (by positivity : 0 ≤ 21 * K + (64 * K + 1) * Kc)
  have hmiddle' : 21 * K * M / R + gain * (Kc / R) ≤
      (21 * K + (64 * K + 1) * Kc) * (4 * Ce * scale) := by
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

end
end FangqingHierarchyScaleBudgets
end

section
-- Source component: HierarchyExternalReserves.lean

namespace FangqingHierarchyExternalReserves

open FangqingThirdGroupScaling FangqingActualRelayScaling

noncomputable section

set_option maxHeartbeats 3000000

theorem simultaneous_external_component_reserves (Cglobal Cp Crho Craw csigma Clink : ℝ)
    (hG : 0 ≤ Cglobal) (hP : 0 ≤ Cp) (hR : 0 ≤ Crho) (hRaw : 0 ≤ Craw)
    (hs : 0 ≤ csigma) (hl : 0 ≤ Clink) :
    ∃ cL cq cg : ℝ, 0 < cL ∧ cL ≤ 1 / 256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧
      (∀ L mu q : ℝ, 0 < mu → 0 < L → 1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) →
        let Li := 2 * cL * L
        let mui := 2 * mu
        mui ≤ Li ∧ Cp * (8 * mui) * q ^ 2 ≤ L / 64 ∧
        4 * Li + Cp * (8 * mui) * q ^ 2 ≤ L / 16 ∧
        2 * csigma * Li ≤ L / 8 ∧ Clink * Li ≤ L / 8 ∧
        Cglobal * Li + Cp * (8 * mui) * q ^ 2 ≤ L / 2) ∧
      (∀ rhop rho : ℝ, 0 ≤ rhop → rhop ≤ rho →
        Crho * (cg * rhop) ≤ rho / 8 ∧ Craw * (cg * rhop) ≤ rho / 8) := by
  let cL := 1 / (256 * (Cglobal + csigma + Clink + 1))
  let cq := Real.sqrt (cL / (32 * (Cp + 1)))
  let cg := 1 / (16 * (Crho + Craw + 1))
  have hcL : 0 < cL := by dsimp [cL]; positivity
  have hcL256 : cL ≤ 1 / 256 := by
    dsimp [cL]
    apply (div_le_iff₀ (by positivity : 0 < 256 * (Cglobal + csigma + Clink + 1))).mpr
    linarith only [hG, hs, hl]
  have hcq : 0 < cq := Real.sqrt_pos.mpr (by positivity)
  have hcq2 : cq ^ 2 = cL / (32 * (Cp + 1)) := Real.sq_sqrt (by positivity)
  have hcqL : cq ^ 2 ≤ cL := by
    rw [hcq2]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (Cp + 1))).mpr
    nlinarith only [mul_nonneg hcL.le hP, hcL.le]
  have hcq1 : cq ≤ 1 := by nlinarith only [hcq.le, hcqL, hcL256]
  have hCpq : 16 * Cp * cq ^ 2 ≤ cL / 2 := by
    rw [hcq2, ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < 32 * (Cp + 1))).mpr
    nlinarith only [hcL.le]
  have hscale : (Cglobal + csigma + Clink + 1) * cL = 1 / 256 := by
    dsimp [cL]
    field_simp
    <;> ring
  have hCG : Cglobal * cL ≤ 1 / 256 := by
    nlinarith only [hscale, mul_nonneg hs hcL.le, mul_nonneg hl hcL.le, hcL.le]
  have hCS : csigma * cL ≤ 1 / 256 := by
    nlinarith only [hscale, mul_nonneg hG hcL.le, mul_nonneg hl hcL.le, hcL.le]
  have hCL : Clink * cL ≤ 1 / 256 := by
    nlinarith only [hscale, mul_nonneg hG hcL.le, mul_nonneg hs hcL.le, hcL.le]
  have hcg : 0 < cg := by dsimp [cg]; positivity
  have hcg1 : cg ≤ 1 := by
    dsimp [cg]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (Crho + Craw + 1))).mpr
    linarith only [hR, hRaw]
  have hCrho : Crho * cg ≤ 1 / 16 := by
    dsimp [cg]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (Crho + Craw + 1))).mpr
    linarith only [hRaw]
  have hCraw : Craw * cg ≤ 1 / 16 := by
    dsimp [cg]
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 16 * (Crho + Craw + 1))).mpr
    linarith only [hR]
  refine ⟨cL, cq, cg, hcL, hcL256, hcq, hcq1, hcg, hcg1, ?_, ?_⟩
  · intro L mu q hmu hL hq hqb Li mui
    have hq2 : 1 ≤ q ^ 2 := one_le_pow₀ hq
    have hmul := mul_le_mul_of_nonneg_left hqb hmu.le
    have hmq : mu * q ^ 2 ≤ cq ^ 2 * L := by
      convert! hmul using 1 <;> field_simp <;> ring
    have hbase := mul_le_mul_of_nonneg_left hq2 hmu.le
    have hCLL := mul_le_mul_of_nonneg_right hcqL hL.le
    have hCp1 := mul_le_mul_of_nonneg_left hmq (by positivity : 0 ≤ 16 * Cp)
    have hCp2 := mul_le_mul_of_nonneg_right hCpq hL.le
    have hPacket : Cp * (8 * mui) * q ^ 2 ≤ cL / 2 * L := by
      dsimp [mui]
      nlinarith only [hCp1, hCp2]
    have hL256 := mul_le_mul_of_nonneg_right hcL256 hL.le
    have hG256 := mul_le_mul_of_nonneg_right hCG hL.le
    have hS256 := mul_le_mul_of_nonneg_right hCS hL.le
    have hlink256 := mul_le_mul_of_nonneg_right hCL hL.le
    dsimp [Li, mui]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      nlinarith only [hmq, hbase, hCLL, hPacket, hL256, hG256, hS256, hlink256, hL]
  · intro rhop rho hrhop hr
    have hrho : 0 ≤ rho := hrhop.trans hr
    have hR1 := mul_le_mul_of_nonneg_left hr (mul_nonneg hR hcg.le)
    have hR2 := mul_le_mul_of_nonneg_right hCrho hrho
    have hW1 := mul_le_mul_of_nonneg_left hr (mul_nonneg hRaw hcg.le)
    have hW2 := mul_le_mul_of_nonneg_right hCraw hrho
    constructor <;> nlinarith only [hR1, hR2, hW1, hW2, hrho]

theorem doubled_internal_rho_matches_external (cL L mu eps r : ℝ)
    (hcL : 0 < cL) (hcL256 : cL ≤ 1 / 256) (hL : 0 < L) (hmu : 0 < mu)
    (heps : 0 < eps) (hr : 1 ≤ r) :
    1 ≤ r / (4 * Real.sqrt cL) ∧
      rho (2 * cL * L) (2 * mu) eps (r / (4 * Real.sqrt cL)) = rho L mu eps r := by
  have hs : 0 < Real.sqrt cL := Real.sqrt_pos.mpr hcL
  have hsq : Real.sqrt cL ^ 2 = cL := Real.sq_sqrt hcL.le
  have hs1 : 4 * Real.sqrt cL ≤ 1 := by nlinarith only [hcL256, hsq, hs.le]
  have hkap : 0 < L / mu := div_pos hL hmu
  have hks : 0 < Real.sqrt (L / mu) := Real.sqrt_pos.mpr hkap
  refine ⟨(one_le_div (by positivity)).mpr (hs1.trans hr), ?_⟩
  have hkEq : 2 * cL * L / (2 * mu) = cL * (L / mu) := by ring
  unfold rho
  rw [hkEq, Real.sqrt_mul hcL.le]
  field_simp [ne_of_gt hcL, ne_of_gt hs, ne_of_gt hL, ne_of_gt hmu, ne_of_gt heps, ne_of_gt hks]
  nlinarith only [hsq]

theorem universal_gap_reserve (Cgap cL : ℝ) (hC : 0 ≤ Cgap) (hcL : 0 < cL) :
    ∃ cT : ℝ, 0 < cT ∧ ∀ L eps Delta N : ℝ,
      0 < L → 0 < eps → 0 ≤ Delta → 0 ≤ N → N ≤ cT * Delta / energy L eps →
      Cgap * N * energy (2 * cL * L) eps ≤ Delta / 2 := by
  let cT := cL / (Cgap + 1)
  have hcT : 0 < cT := by dsimp [cT]; positivity
  have hconst : Cgap * cT ≤ cL := by
    dsimp [cT]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0 < Cgap + 1)).mpr
    nlinarith only [hcL.le]
  refine ⟨cT, hcT, ?_⟩
  intro L eps Delta N hL heps hDelta hN hNb
  have hE : 0 < energy L eps := by unfold energy; positivity
  have hscaled := (le_div_iff₀ hE).mp hNb
  have h1 := mul_le_mul_of_nonneg_left hscaled hC
  have h2 := mul_le_mul_of_nonneg_right hconst hDelta
  have hEi : energy (2 * cL * L) eps = energy L eps / (2 * cL) := by
    unfold energy
    field_simp
    <;> ring
  rw [hEi, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity : 0 < 2 * cL)).mpr
  nlinarith only [h1, h2]

end
end FangqingHierarchyExternalReserves
end

section
-- Source component: HierarchyPairedRates.lean

open scoped ContDiff Topology

namespace FangqingHierarchyPairedRates

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingHierarchyPairedShell FangqingHierarchyInactivePacket FangqingHierarchyScaleBudgets
  FangqingWidePairedShellRateBudgets FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 5000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def ShellReserves (Q edge seed : E → ℝ) (scale R nu K M gain S Lraw Rraw : ℝ) : Prop :=
  S ≤ nu / 8 ∧ HessianNormBound seed (nu / 8) ∧
  4 * (16 * K * M + nu / 8) ≤ gain ∧
  HessianNormBound (fun z => scaledGate theta R 0 z * (scale * edge z) - seed z) (16 * K * M + nu / 8) ∧
  (∀ z w, (3 / 2 : ℝ) * R ≤ ‖z‖ →
    4 * |fderiv ℝ (fderiv ℝ (fun z => scaledGate theta R 0 z * (scale * edge z) - seed z)) z w w| ≤
      gain * fderiv ℝ (fderiv ℝ (FangqingRadialCollar.collar psi R)) z w w) ∧
  (∀ seedLin : E →L[ℝ] ℝ,
    AnalyticClass (FangqingUnlocalizedPacketRegularity.packet Q edge scale seedLin) nu Lraw Rraw)

universe u

theorem actual_hierarchy_paired_rates
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K : ℝ, 0 ≤ K ∧ ∃ Kc : ℝ, 0 ≤ Kc ∧ ∃ Ks : ℝ, 0 ≤ Ks ∧
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
      let A := (3 + 8 * Ks * Cs + Cmin) * D
      let R := 2 * A
      let s := Cs * nu * D
      let Q := QPhysical q nu C
      let edge := pathEdge P delta omega (n + 2) (physicalFrame C h n tail)
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (64 * K + 1) * M
      let seed := localizedSeed theta phi R A (s * A) (mkPhysical h (0 : B0) (0 : W))
      let F0 := inactiveShell Q (fun z => scale * edge z) R gain
      let F1 := fun z => F0 z - seed z
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
      (AnalyticClass F0 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      AnalyticClass F1 (nu / 2) (CL * nu * q ^ 2) (Crho * scale) ∧
      (∀ Y, F0 0 ≤ F0 Y) ∧
      ∃ Z : PhysicalSpace A0 B0 W,
        (∀ Y, rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Z ≤
          rawPacket C h n tail (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        (∀ Y, F1 Z ≤ F1 Y) ∧ (∀ Y, (∀ X, F1 Y ≤ F1 X) → Y = Z) ∧
        ‖Z‖ ≤ Cmin * D ∧ F1 0 - F1 Z ≤ 4 * Cw ^ 2 * nu * D ^ 2 ∧
        (∀ j : Fin (n + 3), (j.val : ℝ) ≤ q → 3 * q * omega ≤ inner ℝ (physicalFrame C h n tail j) Z) ∧
        (∀ Y, ‖Y - Z‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R)) ∧
      ShellReserves Q edge seed scale R nu K M gain (Ks * (s * A) / A ^ 2)
        (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale) := by
  obtain ⟨Ce, hCe, K, hK, Kc, hKc, Ks, hKs, hPhysical⟩ :=
    actual_hierarchy_physical_paired_shell.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  refine ⟨Ce, hCe, K, hK, Kc, hKc, Ks, hKs, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' C h n tail
    delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
    nu D Cs Cmin A R s Q edge M gain seed F0 F1 CL Crho
  obtain ⟨hSmall, hSeed, hDom, hHidden, hAnn, hRaw, hF0, hF1, hMin0, Z, hRawMin, hMin1, hUnique, hNorm, hGap, hBulk, hChamber, hIdentity⟩ :=
    hPhysical A0 B0 W C h n tail delta omega q scale lam hh ht hd hdw hq hscale hlam homega hn
  have hCw1 : 1 ≤ Cw := by linarith only [hCm, hCw]
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCmin : 0 ≤ Cmin := by dsimp [Cmin]; positivity
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hscale hlam
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  obtain ⟨hDA, hWidth, hMinA, hChamberA⟩ := chamber_safe_width_choice Ks Cs Cmin D hKs hCs hCmin hD
  have hA : 0 < A := hD.trans_le hDA
  have hAR : A ≤ R := by dsimp [R]; linarith only [hA]
  have hsqrt : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
  have hqp : 1 ≤ q * Real.sqrt q := by
    nlinarith only [hq, hsqrt, mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hsqrt)]
  have hDomega : omega ≤ D := by
    have hh := mul_le_mul_of_nonneg_right hqp hw.le
    simpa only [one_mul, D, distanceScale] using hh
  have hscaleomega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; dsimp [nu]; ring
  obtain ⟨hL, hrho⟩ := actual_hierarchy_rate_budgets (Ce : ℝ) K Kc Ks Cs Cw Cmin q nu scale omega D R
    Ce.coe_nonneg hK hKc hKs hCs hCmin hCw1 hq hnu.le hscale.le hw hDomega hscaleomega hAR
  have hS : 0 ≤ Ks * (s * A) / A ^ 2 := by positivity
  have hT : 0 ≤ Ks * (s * A) / A ^ 3 := by positivity
  have hClass0 := actual_class_reserve F0 nu (nu / 2)
    (nu * (q + 2) + 16 * K * M + gain * Kc) (CL * nu * q ^ 2)
    (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R)) (Crho * scale)
    hF0 (by linarith only [hnu]) ((le_add_of_nonneg_right hS).trans hL) ((le_add_of_nonneg_right hT).trans hrho)
  have hClass1 := actual_class_reserve F1 (7 * nu / 8) (nu / 2)
    (nu * (q + 2) + 16 * K * M + gain * Kc + Ks * (s * A) / A ^ 2) (CL * nu * q ^ 2)
    (K * ((8 * Ce : ℝ) * scale) + 21 * K * M / R + gain * (Kc / R) + Ks * (s * A) / A ^ 3) (Crho * scale)
    hF1 (by linarith only [hnu]) hL hrho
  exact ⟨⟨hClass0, hClass1, hMin0, Z, hRawMin, hMin1, hUnique, hNorm, hGap, hBulk, hChamber⟩,
    hSmall, hSeed, hDom, hHidden, hAnn, hRaw⟩

end
end FangqingHierarchyPairedRates
end

section
-- Source component: HierarchyPhysicalRelayData.lean

open scoped ContDiff

namespace FangqingHierarchyPhysicalRelayData

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingHierarchyPairedRates FangqingHierarchyUniformRelay
  FangqingHierarchyInactivePacket FangqingDisjointBlockBounds FangqingRelayBlockGeometry FangqingRelayStationarity FangqingActualRelayScaling
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
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Clink : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Clink ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
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
      let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
      let A := CA * D
      let R := 2 * A
      let s := Cs * nu * D
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (64 * K + 1) * M
      let H0 := fun t => inactiveShell (QPhysical q nu C)
        (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
      let H1 := fun t z => H0 t z - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) z
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
      ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
        (∀ t, AnalyticClass (H0 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
        (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
        (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
        (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
          3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
        (∀ t Y, rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) (Z t) ≤
          rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        (∀ t Y, ‖Y - Z t‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R) ∧
        (∀ t, ShellReserves (QPhysical q nu C)
          (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
          (localizedSeed theta phi R A (s * A) (mkPhysical (h t) (0 : B0) (0 : W)))
          scale R nu K M gain (Ks * (s * A) / A ^ 2) (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale)) ∧
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
        (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair (PhysicalSpace A0 B0 W) =>
          endpoint L (lam L mu) (h0 t) (m0 t) p.fst p.snd) (4 * L + CL * nu * q ^ 2)) ∧
        (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair (PhysicalSpace A0 B0 W) =>
          endpoint L (lam L mu) (h1 t) (m1 t) p.fst p.snd) (4 * L + CL * nu * q ^ 2)) ∧
        HessianNormBound (blockSum (packet outer) (localPacket outer L (lam L mu) h0 h1 m0 m1)) (4 * L + CL * nu * q ^ 2) ∧
        HessianNormBound (blockSum (relay outer) (fun _ : Fin (outer + 1) => localRelay (E := PhysicalSpace A0 B0 W) a (sigma L a csigma))) (2 * csigma * L) ∧
        HessianNormBound (blockSum (link outer) (localLink outer rw h0 h1 m0 m1 gate)) (Clink * L) ∧
        (∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link outer) (localLink outer rw h0 h1 m0 m1 gate)) z‖ ≤ rho L mu eps r / 4) ∧
        ContDiff ℝ 2 J ∧
        (∀ x y, ‖gradient J x - gradient J y‖ ≤ (Cglobal * L + CL * nu * q ^ 2) * ‖x - y‖) ∧
        FangqingRelayGlobalJointClass.HessianRate J (Crho * scale + rho L mu eps r / 4) ∧
        (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual outer (PhysicalSpace A0 B0 W))) mu
          (FangqingRelayDualAssembly.negativeFamily outer L (lam L mu) a (sigma L a csigma) rw h0 h1 m0 m1 gate x)) := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  obtain ⟨Ce, hCe, K, hK, Kc, hKc, Ks, hKs, hPacket⟩ :=
    actual_hierarchy_paired_rates.{u} P phi Bp left right Cm Cw hCm hCw hp hl hr hcore
  let Cs := 2 * Cw
  let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
  let Camp := Cs * CA
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCA : 1 ≤ CA := by
    have h1 : 0 ≤ 8 * Ks * Cs := by positivity
    have h2 : 0 ≤ 2 * Cw * (Cm + 2) := by positivity
    dsimp [CA]
    linarith only [h1, h2]
  have hCamp : 0 ≤ Camp := mul_nonneg hCs (zero_le_one.trans hCA)
  obtain ⟨KD, csigma, Cglobal, Cdelta, Ctheta, Clink, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hDeriv, hExtra, hUniform⟩ :=
    actual_uniform_relay_master.{u} phi Bp left right Camp KDlower hCamp hKDlower hp hl hr
  refine ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
    hCD, hCt, hClink, hDeriv, hExtra, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r delta omega q scale lam0 hh ht hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
    nu D Cs' CA' A R s M gain H0 H1 CL Crho
  have hData := fun t : Fin (outer + 1) => hPacket A0 B0 W C (h t) nt (tail t) delta omega q scale lam0
    (hh t) (ht t) hd hdw hq hscale hlam0 homega hn
  choose Z hRawMin hZmin hZunique hZnorm hZgap hZbulk hChamber using fun t => (hData t).1.2.2.2
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
    have hh := (hData t).1.1
    have hmod : nu / 2 = 4 * mu := by dsimp [nu]; rw [hnu]; ring
    change AnalyticClass _ (nu / 2) (CL * nu * q ^ 2) (Crho * scale) at hh
    rw [hmod] at hh
    exact hh
  have hH1 : ∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale) := by
    intro t
    have hh := (hData t).1.2.1
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
  refine ⟨Z, hH0, hH1, (fun t => (hData t).1.2.2.1), hZmin, hZnorm, hZgap, hZbulk, hRawMin, hChamber, (fun t => (hData t).2), ?_⟩
  intro center
  exact hUniform (PhysicalSpace A0 B0 W) outer L mu eps r (CL * nu * q ^ 2) (Crho * scale) R A
    H0 H1 (fun _ => 0) Z (fun t => mkPhysical (h t) 0 0) center
    hmu hLmu heps hr hLH hrho hdpR hdpA hH0 hH1 hHandle
    (fun t y => by change H0 t y - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) y = _; rw [hAmp])
    (fun t => (hData t).1.2.2.1) hZmin

end
end FangqingHierarchyPhysicalRelayData
end

section
-- Source component: HierarchyValueGap.lean

open scoped ContDiff

namespace FangqingHierarchyValueGap

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingHierarchyPhysicalRelayData
  FangqingHierarchyPairedRates FangqingHierarchyInactivePacket FangqingDisjointBlockBounds FangqingRelayBlockGeometry FangqingActualShellOriginJets
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
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Clink Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Clink ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
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
      let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
      let A := CA * D
      let R := 2 * A
      let s := Cs * nu * D
      let M : ℝ := (4 * Ce : ℝ) * scale * omega
      let gain := (64 * K + 1) * M
      let H0 := fun t => inactiveShell (QPhysical q nu C)
        (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
      let H1 := fun t z => H0 t z - localizedSeed theta phi R A (s * A) (mkPhysical (h t) 0 0) z
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
      ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
        (∀ t, AnalyticClass (H0 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t, AnalyticClass (H1 t) (4 * mu) (CL * nu * q ^ 2) (Crho * scale)) ∧
        (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
        (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
        (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
        (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
          3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
        (∀ t Y, rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) (Z t) ≤
          rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
          (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
        (∀ t Y, ‖Y - Z t‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R) ∧
        (∀ t, ShellReserves (QPhysical q nu C)
          (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
          (localizedSeed theta phi R A (s * A) (mkPhysical (h t) (0 : B0) (0 : W)))
          scale R nu K M gain (Ks * (s * A) / A ^ 2) (nu * (q + 2) + M) ((8 * Ce : ℝ) * scale)) ∧
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
        (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair (PhysicalSpace A0 B0 W) =>
          endpoint L (lam L mu) (h0 t) (m0 t) p.fst p.snd) (4 * L + CL * nu * q ^ 2)) ∧
        (∀ t, HessianNormBound (fun p : FangqingRelayBlockGeometry.Pair (PhysicalSpace A0 B0 W) =>
          endpoint L (lam L mu) (h1 t) (m1 t) p.fst p.snd) (4 * L + CL * nu * q ^ 2)) ∧
        HessianNormBound (blockSum (packet outer) (localPacket outer L (lam L mu) h0 h1 m0 m1)) (4 * L + CL * nu * q ^ 2) ∧
        HessianNormBound (blockSum (relay outer) (fun _ : Fin (outer + 1) => localRelay (E := PhysicalSpace A0 B0 W) a (sigma L a csigma))) (2 * csigma * L) ∧
        HessianNormBound (blockSum (link outer) (localLink outer rw h0 h1 m0 m1 gate)) (Clink * L) ∧
        (∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link outer) (localLink outer rw h0 h1 m0 m1 gate)) z‖ ≤ rho L mu eps r / 4) ∧
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
  obtain ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, hK, hKc, hKs, hKD, hKDl, hcs, hCG,
      hCD, hCt, hClink, hThetaDeriv, hExtra, hBuilder⟩ :=
    actual_physical_relay_master_data.{u} P phi Bp left right Cm Cw KDlower hCm hCw hKDlower hp hl hr hcore
  let Cgap := 32 * (2 * Cw) ^ 2 * KD ^ 2 + 24 * Cdelta * KD ^ 2 + 1
  have hGap : 0 ≤ Cgap := by dsimp [Cgap]; positivity
  refine ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hThetaDeriv, hExtra, hGap, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r delta omega q scale lam0 hh ht hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
    nu D Cs CA A R s M gain H0 H1 CL Crho
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRawMin, hChamber, hReserve, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail L mu eps r delta omega q scale lam0 hh ht
      hmu hLmu heps hr hd hdw hq hscale hlam0 homega hn hnu hDistance
  refine ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRawMin, hChamber, hReserve, ?_⟩
  intro center a ell rw h0 h1 m0 m1 gate J
  obtain ⟨hDelta, hRange, hSmall, hE0, hE1, hPG, hRG, hLG, hL3G, hJ, hGrad, hHess, hSC⟩ := hCenters center
  refine ⟨hDelta, hRange, hSmall, hE0, hE1, hPG, hRG, hLG, hL3G, hJ, hGrad, hHess, hSC, ?_⟩
  have hL : 0 < L := hmu.trans_le hLmu
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hNu : 0 < nu := mul_pos hscale hlam0
  have hD : 0 < D := by dsimp [D, distanceScale]; positivity
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCA : 1 ≤ CA := by
    have h1 : 0 ≤ 8 * Ks * Cs := by positivity
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
end FangqingHierarchyValueGap
end

section
-- Source component: HierarchyBudgetTable.lean

open scoped ContDiff

namespace FangqingHierarchyBudgetTable

open FangqingHierarchyInactivePacket FangqingRelayStationarity FangqingRelayAnalyticAssembly
  FangqingRelayFenchelInterfaces FangqingDisjointBlockBounds FangqingRelayBlockGeometry
  FangqingActualInactivePacket

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def PacketTable (Q edge H0 H1 : E → ℝ) (scale L rho : ℝ) : Prop :=
  (∀ seedLin : E →L[ℝ] ℝ,
    HessianNormBound (FangqingUnlocalizedPacketRegularity.packet Q edge scale seedLin) (L / 16) ∧
    FangqingFenchelEndpointClass.HessianRate (FangqingUnlocalizedPacketRegularity.packet Q edge scale seedLin) (rho / 8)) ∧
  HessianNormBound H0 (L / 16) ∧ HessianNormBound H1 (L / 16) ∧
  FangqingFenchelEndpointClass.HessianRate H0 (rho / 8) ∧
  FangqingFenchelEndpointClass.HessianRate H1 (rho / 8)

def RelayTable (n : ℕ) (beta lam a sigma reward L rho : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ) : Prop :=
  (∀ t, HessianNormBound (fun p : Pair E => endpoint beta lam (h0 t) (m0 t) p.fst p.snd) (L / 16)) ∧
  (∀ t, HessianNormBound (fun p : Pair E => endpoint beta lam (h1 t) (m1 t) p.fst p.snd) (L / 16)) ∧
  HessianNormBound (blockSum (packet n) (localPacket n beta lam h0 h1 m0 m1)) (L / 16) ∧
  HessianNormBound (blockSum (relay n) (fun _ : Fin (n + 1) => localRelay (E := E) a sigma)) (L / 8) ∧
  HessianNormBound (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) (L / 8) ∧
  (∀ z, ‖iteratedFDeriv ℝ 3 (blockSum (link n) (localLink n reward h0 h1 m0 m1 gate)) z‖ ≤ rho / 4)

def FinalFamily (n : ℕ) (beta lam a sigma reward L mu rho M Ctheta ell Gap : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ) (gate : Fin n → E → ℝ)
    (X0 : Blocks n E) : Prop :=
  let J := assembled n beta lam a sigma reward h0 h1 m0 m1 gate
  (∀ t z, |delta (h0 t) (h1 t) (m0 t) (m1 t) z| ≤ M) ∧
  (∀ j z, 0 ≤ gate j z ∧ gate j z ≤ 1) ∧
  ((reward + M) * (2 * Ctheta / (a ^ 2 * ell ^ 2)) ≤ sigma / 2) ∧
  ContDiff ℝ 2 J ∧
  (∀ x y, ‖gradient J x - gradient J y‖ ≤ L * ‖x - y‖) ∧
  FangqingRelayGlobalJointClass.HessianRate J rho ∧
  (∀ x, StrongConvexOn (Set.univ : Set (FangqingRelayDualAssembly.Dual n E)) (2 * mu)
    (FangqingRelayDualAssembly.negativeFamily n beta lam a sigma reward h0 h1 m0 m1 gate x)) ∧
  ∃ Y S : Blocks n E → (Fin (n + 1) → E),
    (∀ (X : Blocks n E) yy ss,
      family n beta lam a sigma reward h0 h1 m0 m1 gate X.ofLp yy ss ≤
        exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X) ∧
    Differentiable ℝ (exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S) ∧
    (∀ X, exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S X =
      sSup (Set.range (FangqingRelayValueBridge.curryF n beta lam a sigma reward h0 h1 m0 m1 gate X))) ∧
    let Phi := exactValue n beta lam a sigma reward h0 h1 m0 m1 gate Y S
    Phi X0 - sInf (Set.range Phi) ≤ Gap / 2

theorem hessian_bound_mono (f : E → ℝ) (A B : ℝ)
    (h : HessianNormBound f A) (hAB : A ≤ B) : HessianNormBound f B := fun z => (h z).trans hAB

theorem class_implies_packet_budget (f : E → ℝ) (nu LF Rf L rho : ℝ)
    (hLF : 0 ≤ LF) (h : AnalyticClass f nu LF Rf) (hL : LF ≤ L / 16) (hR : Rf ≤ rho / 8) :
    HessianNormBound f (L / 16) ∧ FangqingFenchelEndpointClass.HessianRate f (rho / 8) := by
  constructor
  · intro z
    rw [FangqingJetToRegularity.hessian_norm_eq_second_jet]
    exact (FangqingFenchelEndpointClass.second_jet_bound_from_gradient_rate f LF hLF h.2.2.1 z).trans hL
  · intro x y
    exact (h.2.2.2 x y).trans (mul_le_mul_of_nonneg_right hR (norm_nonneg _))

end
end FangqingHierarchyBudgetTable
end

section
-- Source component: HierarchyAlignment.lean

namespace FangqingHierarchyAlignment

open HandleAlignment FangqingReservedAlignment FangqingActualRelayScaling OriginalPacketDistanceGapBounds

noncomputable section

set_option maxHeartbeats 2500000

def AlignmentAvailable (cq cL Cw cg KD : ℝ) : Prop :=
  ∀ (L rho eps mu : ℝ) (q0 : ℕ), 0 < L → 0 < rho → 0 < eps → 0 < mu → 1 ≤ q0 →
    (q0 : ℝ) ≤ cq * min ((regime L rho eps (L / mu)) ^ (2 / 7 : ℝ)) (Real.sqrt (L / mu)) →
    let q := packetLength cq (regime L rho eps (L / mu)) (L / mu)
    let nu := curvature 16 L (L / mu)
    let D := distance (KD / (2 * Real.sqrt cL)) L eps (L / mu)
    let rhoq := packetBudget Cw cg nu D q
    let omega := edgeWidth Cw cg nu rhoq q
    let scale := cg * rhoq
    let barlam := nu / scale
    q0 ≤ q ∧
    cq * min ((regime L rho eps (L / mu)) ^ (2 / 7 : ℝ)) (Real.sqrt (L / mu)) / 2 ≤ (q : ℝ) ∧
    (q : ℝ) ≤ cq * min ((regime L rho eps (L / mu)) ^ (2 / 7 : ℝ)) (Real.sqrt (L / mu)) ∧
    0 < scale ∧ 0 < barlam ∧ 0 < omega ∧ 0 < rhoq ∧ rhoq ≤ rho / 8 ∧
    scale * barlam = 8 * (2 * mu) ∧ omega = Cw * barlam * (q : ℝ) ^ 2 ∧
    distanceScale (q : ℝ) omega = packetD (2 * cL * L) (2 * mu) KD eps

theorem universal_aligned_physical_witnesses (cL Cw cg KD cqcap : ℝ)
    (hcL : 0 < cL) (hCw : 0 < Cw) (hcg : 0 < cg) (hKD : 0 < KD) (hcap : 0 < cqcap) :
    ∃ cq : ℝ, 0 < cq ∧ cq ≤ 1 ∧ cq ≤ cqcap ∧ AlignmentAvailable cq cL Cw cg KD := by
  have hs : 0 < Real.sqrt cL := Real.sqrt_pos.mpr hcL
  have hKDe : 0 < KD / (2 * Real.sqrt cL) := by positivity
  obtain ⟨cq, hcq, hcq1, hcqcap, hAlign⟩ := reserved_parameter_alignment 16 Cw cg (KD / (2 * Real.sqrt cL)) cqcap
    (by norm_num) hCw hcg hKDe hcap
  refine ⟨cq, hcq, hcq1, hcqcap, ?_⟩
  intro L rho eps mu q0 hL hrho heps hmu hq0 hnd q nu D rhoq omega scale barlam
  obtain ⟨hqn, hqhalf, hqbound, hq2, hnu, hD, hR, hw, hDistance, hRB, hGap⟩ :=
    hAlign L rho eps (L / mu) q0 hL hrho heps (div_pos hL hmu) hq0 hnd
  have hs0 : 0 < scale := by dsimp [scale]; positivity
  have hb : 0 < barlam := div_pos hnu hs0
  have hnuEq : nu = 8 * (2 * mu) := by dsimp [nu, curvature]; field_simp; try ring
  have hqpos : 0 < q := lt_of_lt_of_le Nat.zero_lt_one (hq0.trans hqn)
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  have hsq : Real.sqrt cL ^ 2 = cL := Real.sq_sqrt hcL.le
  have hkap : 2 * cL * L / (2 * mu) = cL * (L / mu) := by ring
  have hActualD : D = packetD (2 * cL * L) (2 * mu) KD eps := by
    dsimp [D, distance, packetD]
    rw [hkap, Real.sqrt_mul hcL.le]
    field_simp [hcL.ne', hs.ne', hL.ne']
    nlinarith only [hsq]
  refine ⟨hqn, hqhalf, hqbound, hs0, hb, hw, hR, hRB, ?_, ?_, ?_⟩
  · dsimp [barlam]
    rw [mul_div_cancel₀ _ hs0.ne', hnuEq]
  · dsimp [omega, edgeWidth, barlam, scale]
    field_simp
    <;> ring
  · have h := hDistance
    change D = (q : ℝ) ^ (3 / 2 : ℝ) * omega at h
    rw [HandleAlignment.rpow_three_halves (q : ℝ) hqr] at h
    change (q : ℝ) * Real.sqrt (q : ℝ) * omega = _
    rw [← h, ← hActualD]

end
end FangqingHierarchyAlignment
end

section
-- Source component: PrivateConstantHierarchy.lean

open scoped ContDiff

namespace FangqingPrivateConstantHierarchy

open FangqingAmplifier FangqingPathEdgeRegularity FangqingActualInactivePacket
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer OriginalPacketDistanceGapBounds
  FangqingActualRelayScaling FangqingThirdGroupScaling FangqingRelayAnalyticAssembly FangqingRelayFenchelInterfaces
  FangqingRadialGateBounds FangqingRelayStationarity FangqingHierarchyExternalReserves FangqingHierarchyBudgetTable
  FangqingHierarchyPairedRates FangqingHierarchyInactivePacket FangqingHierarchyAlignment

noncomputable section

set_option maxHeartbeats 8000000

universe u

theorem actual_private_constant_hierarchy
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw KDlower : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hKDlower : 0 ≤ KDlower)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Clink Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ KDlower ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Clink ∧ 0 ≤ Cgap ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      let Cs := 2 * Cw
      let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
      let Cp := CL + 3 + 4 * (Ce : ℝ) * Cw
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
      ∃ cL cq cg cT : ℝ, 0 < cL ∧ cL ≤ 1 / 256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A0 B0 W : Type u)
        [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
        [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (outer nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin (outer + 1) → A0)
        (tail : Fin (outer + 1) → Fin (nt + 2) → W)
        (L mu eps r rhop q delta omega Delta : ℝ),
        (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
        0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
        1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) → 0 < delta → delta ≤ omega →
        ((nt + 2 : ℕ) : ℝ) ≤ Cm * q → 0 ≤ Delta →
        ((outer + 1 : ℕ) : ℝ) ≤ cT * Delta / energy L eps →
        let Li := 2 * cL * L
        let mui := 2 * mu
        let ri := r / (4 * Real.sqrt cL)
        let scale := cg * rhop
        let barlam := (8 * mui) / scale
        omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mui KD eps →
        let nu := scale * barlam
        let D := distanceScale q omega
        let A := CA * D
        let R := 2 * A
        let seed := Cs * nu * D
        let Mpath : ℝ := (4 * Ce : ℝ) * scale * omega
        let gain := (64 * K + 1) * Mpath
        let H0 := fun t => inactiveShell (QPhysical q nu C)
          (fun z => scale * pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)) z) R gain
        let H1 := fun t z => H0 t z - localizedSeed theta phi R A (seed * A) (mkPhysical (h t) 0 0) z
        ∃ Z : Fin (outer + 1) → PhysicalSpace A0 B0 W,
          (∀ t, AnalyticClass (H0 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t, AnalyticClass (H1 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale)) ∧
          (∀ t y, H0 t 0 ≤ H0 t y) ∧ (∀ t y, H1 t (Z t) ≤ H1 t y) ∧
          (∀ t, ‖Z t‖ ≤ (2 * Cw * (Cm + 2)) * D) ∧
          (∀ t, H1 t 0 - H1 t (Z t) ≤ 4 * Cw ^ 2 * nu * D ^ 2) ∧
          (∀ t (j : Fin (nt + 3)), (j.val : ℝ) ≤ q →
            3 * q * omega ≤ inner ℝ (physicalFrame C (h t) nt (tail t) j) (Z t)) ∧
          (∀ t Y, rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
            (scale * (2 * omega ^ 2 / Real.sqrt q)) (Z t) ≤
            rawPacket C (h t) nt (tail t) (FlatCubic.edge P delta omega) q nu scale
            (scale * (2 * omega ^ 2 / Real.sqrt q)) Y) ∧
          (∀ t Y, ‖Y - Z t‖ ≤ 2 * D → ‖Y‖ < A ∧ ‖Y‖ < R) ∧
          (∀ t, ShellReserves (QPhysical q nu C)
            (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
            (localizedSeed theta phi R A (seed * A) (mkPhysical (h t) (0 : B0) (0 : W)))
            scale R nu K Mpath gain (Ks * (seed * A) / A ^ 2) (nu * (q + 2) + Mpath) ((8 * Ce : ℝ) * scale)) ∧
          (∀ t, PacketTable (QPhysical q nu C)
            (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
            (H0 t) (H1 t) scale L (rho L mu eps r)) ∧
          ∀ center : Fin outer → PhysicalSpace A0 B0 W,
          let a := relayAmplitude 1 (Li / mui) ri
          let ell := width Li mui KD eps
          let rw := reward Cdelta 8 Li KD eps
          let h0 := fun t => reduced (H0 t) mui
          let h1 := fun t => reduced (H1 t) mui
          let m0 := fun t => H0 t 0
          let m1 := fun t => H1 t (Z t)
          let gate := fun j => scaledGate theta (a * ell) (center j)
          let X0 : Blocks outer (PhysicalSpace A0 B0 W) :=
            WithLp.toLp 2 (Fin.cons ((-(seed / lam Li mui)) • mkPhysical (h 0) (0 : B0) (0 : W)) (fun _ => 0))
          RelayTable outer Li (lam Li mui) a (sigma Li a csigma) rw L (rho L mu eps r) h0 h1 m0 m1 gate ∧
          FinalFamily outer Li (lam Li mui) a (sigma Li a csigma) rw L mu (rho L mu eps r)
            (rawBudget Cdelta 8 Li mui KD eps) Ctheta ell Delta h0 h1 m0 m1 gate X0 := by
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  obtain ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, Cgap,
      hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hThetaDeriv, hExtra, hGap, hBuilder⟩ :=
    FangqingHierarchyValueGap.actual_physical_relay_value_gap.{u} P phi Bp left right Cm Cw KDlower
      hCm hCw hKDlower hp hl hr hcore
  let Cs := 2 * Cw
  let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
  let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
  let Cp := CL + 3 + 4 * (Ce : ℝ) * Cw
  let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
  have hCs : 0 ≤ Cs := by dsimp [Cs]; positivity
  have hCL : 0 ≤ CL := by dsimp [CL]; positivity
  have hCp : 0 ≤ Cp := by dsimp [Cp]; positivity
  have hCrho : 0 ≤ Crho := by dsimp [Crho]; positivity
  obtain ⟨cL, cqcap, cg, hcL, hcL256, hcap, hcap1, hcg, hcg1, hBudget, hHessianBudget⟩ :=
    simultaneous_external_component_reserves Cglobal Cp Crho (8 * Ce) csigma Clink hCG hCp hCrho (by positivity) hcs.le hClink
  have hCwPos : 0 < Cw := by linarith only [hCm, hCw]
  obtain ⟨cq, hcq, hcq1, hcqcap, hAlignment⟩ := universal_aligned_physical_witnesses cL Cw cg KD cqcap
    hcL hCwPos hcg (lt_of_lt_of_le zero_lt_one hKD) hcap
  obtain ⟨cT, hcT, hGapReserve⟩ := universal_gap_reserve Cgap cL hGap hcL
  refine ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hGap, hThetaDeriv,
    cL, cq, cg, cT, hcL, hcL256, hcq, hcq1, hcg, hcg1, hcT, hAlignment, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' outer nt C h tail
    L mu eps r rhop q delta omega Delta hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn hDeltaGap hN
    Li mui ri scale barlam homega hDistance nu D A R seed Mpath gain H0 H1
  have hqbcap : q ^ 2 ≤ cqcap ^ 2 * (L / mu) := hqBound.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hcq.le hcqcap 2) (by positivity))
  obtain ⟨hMuLi, hPacket, hFenchel, hRelay, hLinks, hTotalGrad⟩ := hBudget L mu q hmu hL hq hqbcap
  have hLi : 0 < Li := by dsimp [Li]; positivity
  have hMui : 0 < mui := by dsimp [mui]; positivity
  have hs : 0 < scale := mul_pos hcg hrhop
  have hb : 0 < barlam := div_pos (by positivity) hs
  have hnuEq : scale * barlam = 8 * mui := by dsimp [barlam]; exact mul_div_cancel₀ _ hs.ne'
  obtain ⟨hri, hRhoEq⟩ := doubled_internal_rho_matches_external cL L mu eps r hcL hcL256 hL hmu heps hr
  obtain ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRawMin, hChamber, hReserve, hCenters⟩ :=
    hBuilder A0 B0 W outer nt C h tail Li mui eps ri delta omega q scale barlam hh ht
      hMui hMuLi heps hri hd hdw hq hs hb homega hn hnuEq hDistance
  have hw : 0 < omega := hd.trans_le hdw
  have hnu : 0 < nu := mul_pos hs hb
  have hCLCp : CL ≤ Cp := by
    have hh : 0 ≤ 4 * (Ce : ℝ) * Cw := by positivity
    dsimp [Cp]
    linarith only [hh]
  have hLH : CL * nu * q ^ 2 ≤ Cp * nu * q ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCLCp hnu.le) (sq_nonneg q)
  have hPacketExternal : Cp * nu * q ^ 2 ≤ L / 64 := by simpa only [nu, hnuEq] using hPacket
  have hShellLF : CL * nu * q ^ 2 ≤ L / 16 := by linarith only [hLH, hPacketExternal, hL]
  have hCrhoBudget : Crho * scale ≤ rho L mu eps r / 8 :=
    (hHessianBudget rhop (rho L mu eps r) hrhop.le hrhopBound).1
  have hRawR : (8 * Ce : ℝ) * scale ≤ rho L mu eps r / 8 :=
    (hHessianBudget rhop (rho L mu eps r) hrhop.le hrhopBound).2
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hqlinear : q + 2 ≤ 3 * q ^ 2 := by nlinarith only [hq, sq_nonneg (q - 1)]
  have hScaleOmega : scale * omega = Cw * nu * q ^ 2 := by rw [homega]; dsimp [nu]; ring
  have hMpath : Mpath = 4 * (Ce : ℝ) * Cw * nu * q ^ 2 := by
    dsimp [Mpath]
    calc
      _ = 4 * (Ce : ℝ) * (scale * omega) := by ring
      _ = _ := by rw [hScaleOmega]; ring
  have hRawLF : nu * (q + 2) + Mpath ≤ L / 16 := by
    have hh := mul_le_mul_of_nonneg_left hqlinear hnu.le
    have hpos : 0 ≤ CL * nu * q ^ 2 := by positivity
    have hb : nu * (q + 2) + Mpath ≤ Cp * nu * q ^ 2 := by
      rw [hMpath]
      dsimp [Cp]
      nlinarith only [hh, hpos]
    linarith only [hb, hPacketExternal, hL]
  have hPacketTable : ∀ t, PacketTable (QPhysical q nu C)
      (pathEdge P delta omega (nt + 2) (physicalFrame C (h t) nt (tail t)))
      (H0 t) (H1 t) scale L (rho L mu eps r) := by
    intro t
    have h0 := class_implies_packet_budget (H0 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale) L (rho L mu eps r)
      (by positivity) (hH0 t) hShellLF hCrhoBudget
    have h1 := class_implies_packet_budget (H1 t) (4 * mui) (CL * nu * q ^ 2) (Crho * scale) L (rho L mu eps r)
      (by positivity) (hH1 t) hShellLF hCrhoBudget
    refine ⟨?_, h0.1, h1.1, h0.2, h1.2⟩
    intro seedLin
    exact class_implies_packet_budget _ nu (nu * (q + 2) + Mpath) ((8 * Ce : ℝ) * scale) L (rho L mu eps r)
      (by dsimp [Mpath]; positivity)
      ((hReserve t).2.2.2.2.2 seedLin) hRawLF hRawR
  refine ⟨Z, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRawMin, hChamber, hReserve, hPacketTable, ?_⟩
  intro center a ell rw h0 h1 m0 m1 gate X0
  obtain ⟨hM, hRange, hSmall, hE0, hE1, hPG, hRG, hLG, hL3G, hJ, hGrad, hHess, hSC,
    Y, S, hMax, hDiff, hSup, hValueGap⟩ := hCenters center
  have hExternalFenchel : 4 * Li + CL * nu * q ^ 2 ≤ L / 16 := by
    have hb : 4 * Li + Cp * nu * q ^ 2 ≤ L / 16 := by simpa only [nu, hnuEq] using hFenchel
    linarith only [hb, hLH]
  have hGradBudget : Cglobal * Li + CL * nu * q ^ 2 ≤ L := by
    have hb : Cglobal * Li + Cp * nu * q ^ 2 ≤ L / 2 := by simpa only [nu, hnuEq] using hTotalGrad
    linarith only [hb, hLH, hL]
  have hHessBudget : Crho * scale + rho Li mui eps ri / 4 ≤ rho L mu eps r := by
    rw [hRhoEq]
    have hrho : 0 ≤ rho L mu eps r := hrhop.le.trans hrhopBound
    linarith only [hCrhoBudget, hrho]
  have hGapReserved := hGapReserve L eps Delta ((outer + 1 : ℕ) : ℝ) hL heps hDeltaGap (by positivity) hN
  refine ⟨?_, hM, hRange, hSmall, hJ, ?_, ?_, hSC, Y, S, hMax, hDiff, hSup, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t
      exact hessian_bound_mono _ _ _ (hE0 t) hExternalFenchel
    · intro t
      exact hessian_bound_mono _ _ _ (hE1 t) hExternalFenchel
    · exact hessian_bound_mono _ _ _ hPG hExternalFenchel
    · exact hessian_bound_mono _ _ _ hRG hRelay
    · exact hessian_bound_mono _ _ _ hLG hLinks
    · intro z
      have heq : rho Li mui eps ri = rho L mu eps r := hRhoEq
      rw [← heq]
      exact hL3G z
  · intro x y
    exact (hGrad x y).trans (mul_le_mul_of_nonneg_right hGradBudget (norm_nonneg _))
  · intro x y
    exact (hHess x y).trans (mul_le_mul_of_nonneg_right hHessBudget (norm_nonneg _))
  · exact hValueGap.trans hGapReserved

end
end FangqingPrivateConstantHierarchy
end

section
-- Source component: HierarchyLateGateWorldFactory.lean

open scoped NNReal Topology

namespace FangqingHierarchyLateGateWorldFactory

open FangqingCanonicalLateGateFamily FangqingCanonicalLateGateWorldFactory
  FangqingAmplifier FangqingActualRelayScaling FangqingThirdGroupScaling
  FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayJointReindexing
  OriginalPacketDistanceGapBounds FangqingPublicShellProfiles FangqingRadialGateBounds
  FangqingExternalPhysicalRelayValidity FangqingPrivateConstantHierarchy FangqingHierarchyBudgetTable
  FangqingHierarchyAlignment OriginalCanonicalPacketTailSupport FangqingPhysicalRelayExactInitialPoint
  FangqingPathEdgeRegularity FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingRelayFenchelInterfaces

noncomputable section

set_option maxHeartbeats 9500000

def originalConfig2
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (n : ℕ)
    (Ce : ℝ≥0) (K Ks Cm Cw KD csigma Cdelta cL cg L mu eps r rhop q delta omega : ℝ) : Config n :=
  let Li := 2 * cL * L
  let mui := 2 * mu
  let ri := r / (4 * Real.sqrt cL)
  let scale := cg * rhop
  let barlam := (8 * mui) / scale
  let D := distanceScale q omega
  let nu := scale * barlam
  let A := (3 + 8 * Ks * (2 * Cw) + 2 * Cw * (Cm + 2)) * D
  let a := relayAmplitude 1 (Li / mui) ri
  { profile := P, phi := phi, q := q, delta := delta, omega := omega,
    scale := scale, barlam := barlam, R := 2 * A, A := A,
    gain := (64 * K + 1) * ((4 * Ce : ℝ) * scale * omega),
    seed := (2 * Cw) * nu * D,
    beta := Li, lam := lam Li mui, mu := mui, a := a,
    sigma := sigma Li a csigma, reward := reward Cdelta 8 Li KD eps,
    ell := width Li mui KD eps }

universe u

theorem actual_hierarchy_original_world_factory
    (P : FlatCubic.Profile) (phi : ℝ → ℝ) (Bp left right Cm Cw b0 : ℝ)
    (hCm : 0 ≤ Cm) (hCw : 4 * (Cm + 2) ≤ Cw) (hb0 : 0 < b0)
    (hp : ContDiff ℝ 3 phi) (hl : ∀ t, t < -Bp → phi t = left) (hr : ∀ t, Bp < t → phi t = right)
    (hcore : ∀ t, |t| < 1 → phi t = t) :
    ∃ Ce : ℝ≥0, 1 ≤ Ce ∧ ∃ K Kc Ks KD csigma Cglobal Cdelta Ctheta Clink Cgap : ℝ,
      0 ≤ K ∧ 0 ≤ Kc ∧ 0 ≤ Ks ∧ 1 ≤ KD ∧ 2 + 1 / b0 ≤ KD ∧ 0 < csigma ∧ 0 ≤ Cglobal ∧
      0 ≤ Cdelta ∧ 0 ≤ Ctheta ∧ 0 ≤ Clink ∧ 0 ≤ Cgap ∧ (∀ u : ℝ, |deriv theta u| ≤ Ctheta) ∧
      let Cs := 2 * Cw
      let CA := 3 + 8 * Ks * Cs + 2 * Cw * (Cm + 2)
      let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
      let Cp := CL + 3 + 4 * (Ce : ℝ) * Cw
      let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * Cs
      ∃ cL cq cg cT : ℝ, 0 < cL ∧ cL ≤ 1 / 256 ∧ 0 < cq ∧ cq ≤ 1 ∧ 0 < cg ∧ cg ≤ 1 ∧ 0 < cT ∧ AlignmentAvailable cq cL Cw cg KD ∧
      ∀ (A0 B0 W : Type u)
        [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [FiniteDimensional ℝ A0]
        [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [FiniteDimensional ℝ B0]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W],
      ∀ (nt : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : Fin 2 → A0)
        (tail : Fin 2 → Fin (nt + 2) → W)
        (L mu eps r rhop q delta omega Delta : ℝ),
        (∀ t, ‖h t‖ = 1) → (∀ t, Orthonormal ℝ (tail t)) →
        0 < L → 0 < mu → 0 < eps → 1 ≤ r → 0 < rhop → rhop ≤ rho L mu eps r →
        1 ≤ q → q ^ 2 ≤ cq ^ 2 * (L / mu) →
        (∃ qn : ℕ, q = (qn : ℝ) ∧ 1 ≤ qn ∧ qn ≤ nt + 2) → 0 < delta → delta ≤ omega →
        ((nt + 2 : ℕ) : ℝ) ≤ Cm * q → 0 ≤ Delta → 2 ≤ cT * Delta / energy L eps →
        let Li := 2 * cL * L
        let mui := 2 * mu
        let ri := r / (4 * Real.sqrt cL)
        let scale := cg * rhop
        let barlam := (8 * mui) / scale
        omega = Cw * barlam * q ^ 2 → distanceScale q omega = packetD Li mui KD eps →
        let c := originalConfig2 P phi nt Ce K Ks Cm Cw KD csigma Cdelta cL cg
          L mu eps r rhop q delta omega
        BuiltWorld c C h tail (2 * Cw * (Cm + 2)) L (rho L mu eps r)
          (rawBudget Cdelta 8 Li mui KD eps) Ctheta (Delta / (4 * energy L eps)) (energy L eps) := by
  obtain ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hGap, hDeriv,
    cL, cq, cg, cT, hcL, hcL256, hcq, hcq1, hcg, hcg1, hcT, hAlignment, hBuilder⟩ :=
    actual_private_constant_hierarchy.{u} P phi Bp left right Cm Cw (2 + 1 / b0)
      hCm hCw (by positivity) hp hl hr hcore
  refine ⟨Ce, hCe, K, Kc, Ks, KD, csigma, Cglobal, Cdelta, Ctheta, Clink, Cgap,
    hK, hKc, hKs, hKD, hKDl, hcs, hCG, hCD, hCt, hClink, hGap, hDeriv,
    cL, cq, cg, cT, hcL, hcL256, hcq, hcq1, hcg, hcg1, hcT, hAlignment, ?_⟩
  intro A0 B0 W inst inst' inst'' instB instB' instB'' instW instW' instW'' nt C h tail
    L mu eps r rhop q delta omega Delta hh ht hL hmu heps hr hrhop hrhopBound hq hqBound hInteger hd hdw hn hDelta hTwo
    Li mui ri scale barlam homega hDistance c
  have hKD0 : 0 < KD := lt_of_lt_of_le zero_lt_one hKD
  have hLi : 0 < Li := by dsimp [Li]; positivity
  have hmui : 0 < mui := by dsimp [mui]; positivity
  have hs : 0 < scale := by dsimp [scale]; positivity
  have hb : 0 < barlam := by dsimp [barlam]; positivity
  have hq0 : 0 < q := by linarith only [hq]
  have hw : 0 < omega := hd.trans_le hdw
  have hnuEq : scale * barlam = 8 * mui := by dsimp [barlam]; exact mul_div_cancel₀ _ hs.ne'
  obtain ⟨Zraw, hH0, hH1, hMin0, hMin1, hNorm, hLocalGap, hBulk, hRawMin, hChamber, hReserve, hPacketTable, hCenters⟩ :=
    hBuilder A0 B0 W 1 nt C h tail L mu eps r rhop q delta omega Delta hh ht
      hL hmu heps hr hrhop hrhopBound hq hqBound hd hdw hn hDelta (by simpa using hTwo) homega hDistance
  have hZcanon : ∀ t, Zraw t = FangqingCanonicalLateGateFamily.Z c C (h t) (tail t) := by
    intro t
    exact actual_raw_minimizer_uses_public_coefficients P C (h t) (hh t) nt (tail t) (ht t)
      delta omega q scale barlam hd hdw hq0.le hs hb (Zraw t) (hRawMin t)
  have hZfun : Zraw = (fun t => FangqingCanonicalLateGateFamily.Z c C (h t) (tail t)) := funext hZcanon
  rw [hZfun] at hMin1 hNorm hBulk hCenters
  let oldgate : Fin 1 → PhysicalSpace A0 B0 W → ℝ := fun j =>
    scaledGate theta (c.a * c.ell) (c.a • ((-c.lam / c.beta) • FangqingCanonicalLateGateFamily.Z c C (h j.castSucc) (tail j.castSucc)))
  have hGateEq : oldgate = FangqingCanonicalLateGateFamily.gate c C h tail := by
    funext j y
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simp only [oldgate, FangqingCanonicalLateGateFamily.gate, scaledGate, radialGate, mul_pow,
      neg_div, neg_smul, Fin.castSucc_zero]
  let center : Fin 1 → PhysicalSpace A0 B0 W := fun j =>
    c.a • ((-c.lam / c.beta) • FangqingCanonicalLateGateFamily.Z c C (h j.castSucc) (tail j.castSucc))
  obtain ⟨hTable, hFinal⟩ := hCenters center
  change FinalFamily 1 c.beta c.lam c.a c.sigma c.reward L mu (rho L mu eps r)
    (rawBudget Cdelta 8 Li mui KD eps) Ctheta c.ell Delta
    (FangqingCanonicalLateGateFamily.h0 c C h tail) (FangqingCanonicalLateGateFamily.h1 c C h tail)
    (FangqingCanonicalLateGateFamily.m0 c C h tail) (FangqingCanonicalLateGateFamily.m1 c C h tail)
    oldgate (initialX c h) at hFinal
  rw [hGateEq] at hFinal
  obtain ⟨hM, hRange, hSmall, hJ, hGrad, hHess, hSC, Y, S, hMax, hDiff, hSup, hValueGap⟩ := hFinal
  have hValid : Valid c C h tail L (rho L mu eps r) (rawBudget Cdelta 8 Li mui KD eps)
      Ctheta (Delta / (4 * energy L eps)) (energy L eps) := by
    refine ⟨hM, hRange, hSmall, hJ, hGrad, hHess, hSC, Y, S, hMax, hDiff, hSup, ?_⟩
    intro Phi
    have hE : 0 < energy L eps := by unfold energy; positivity
    have hBudget : Delta / (4 * energy L eps) * ((1 + 1 : ℕ) : ℝ) * energy L eps = Delta / 2 := by
      norm_num
      field_simp [hE.ne']
      <;> ring
    rw [hBudget]
    exact hValueGap
  have hD : 0 < distanceScale q omega := by unfold distanceScale; positivity
  have hCw0 : 0 ≤ Cw := by linarith only [hCm, hCw]
  have hCA : 0 < 3 + 8 * Ks * (2 * Cw) + 2 * Cw * (Cm + 2) := by positivity
  have hA : 0 < c.A := by change 0 < (3 + 8 * Ks * (2 * Cw) + 2 * Cw * (Cm + 2)) * distanceScale q omega; positivity
  have hR : 0 < c.R := by change 0 < 2 * c.A; positivity
  have hbeta : 0 < c.beta := hLi
  have hlam : 0 < c.lam := by change 0 < lam Li mui; unfold lam; positivity
  have ha : 0 < c.a := by
    change 0 < relayAmplitude 1 (Li / mui) ri
    unfold relayAmplitude
    have hh : (0 : ℝ) < max 1 (((Li / mui) ^ (3 / 2 : ℝ) / ri) ^ (1 / 3 : ℝ)) := by
      exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    simpa only [one_mul] using hh
  have hell : 0 < c.ell := by
    change 0 < width Li mui KD eps
    rw [width_eq_actual Li mui KD eps hLi hmui]
    positivity
  have hsigma : 0 ≤ c.sigma := by change 0 ≤ sigma Li c.a csigma; unfold sigma; positivity
  have hMnon : 0 ≤ rawBudget Cdelta 8 Li mui KD eps := by unfold rawBudget packetD; positivity
  have hReward : rawBudget Cdelta 8 Li mui KD eps ≤ c.reward := by
    change rawBudget Cdelta 8 Li mui KD eps ≤ reward Cdelta 8 Li KD eps
    rw [reward_eq_two_raw_plus_energy Cdelta 8 Li mui KD eps hLi hmui]
    have hE : 0 ≤ energy Li eps := by unfold energy; positivity
    linarith only [hMnon, hE]
  obtain ⟨qn, hqReal, hqn, hfit⟩ := hInteger
  have hEllScale : c.ell = c.lam / c.beta * distanceScale q omega := by
    change width Li mui KD eps = lam Li mui / Li * distanceScale q omega
    rw [hDistance]
    unfold width
    ring
  let CL := 7 / 2 + 4 * (Ce : ℝ) * Cw * (16 * K + (64 * K + 1) * Kc)
  let Crho := 8 * K * (Ce : ℝ) + 4 * (Ce : ℝ) * (21 * K + (64 * K + 1) * Kc) + Ks * (2 * Cw)
  have hInit := displayed_physical_initial_point_exact P phi hcore 1 nt qn C h tail
    (fun t => FangqingCanonicalLateGateFamily.Z c C (h t) (tail t)) hh ht hqn hfit
    delta omega (scale * barlam) scale c.R c.A c.seed c.gain mui (4 * mui)
    (CL * (scale * barlam) * q ^ 2) (Crho * scale) c.beta c.lam c.a c.ell c.sigma c.reward
    (rawBudget Cdelta 8 Li mui KD eps) hR hA hw.le hbeta hlam ha hell
    (by simpa only [hqReal] using hEllScale) (by linarith only [hmui]) hsigma hMnon hReward
  have hInit' := hInit (by simpa only [c, originalConfig2, Li, mui, scale, barlam, CL, Crho, ← hqReal] using! hH0) (by simpa only [c, originalConfig2, Li, mui, scale, barlam, CL, Crho, ← hqReal] using! hH1)
    (by simpa only [c, originalConfig2, Li, mui, scale, barlam, ← hqReal] using! hMin0) (by simpa only [c, originalConfig2, Li, mui, scale, barlam, ← hqReal] using! hBulk)
    (by simpa only [c, originalConfig2, Li, mui, scale, barlam, ← hqReal, FangqingCanonicalLateGateFamily.H0, FangqingCanonicalLateGateFamily.H1, FangqingCanonicalLateGateFamily.h0, FangqingCanonicalLateGateFamily.h1,
      FangqingCanonicalLateGateFamily.m0, FangqingCanonicalLateGateFamily.m1] using! hM)
  obtain ⟨hFlat, hExact⟩ := hInit'
  change (∀ j, oldgate j =ᶠ[𝓝 (c.a • initialX c h j.castSucc)] (fun _ => 0)) at hFlat
  rw [hGateEq] at hFlat
  simp only [← hqReal] at hExact
  change (∀ yy ss : Fin 2 → PhysicalSpace A0 B0 W,
    family 1 c.beta c.lam c.a c.sigma c.reward (FangqingCanonicalLateGateFamily.h0 c C h tail)
      (FangqingCanonicalLateGateFamily.h1 c C h tail) (FangqingCanonicalLateGateFamily.m0 c C h tail)
      (FangqingCanonicalLateGateFamily.m1 c C h tail) oldgate (initialX c h).ofLp yy ss ≤
    family 1 c.beta c.lam c.a c.sigma c.reward (FangqingCanonicalLateGateFamily.h0 c C h tail)
      (FangqingCanonicalLateGateFamily.h1 c C h tail) (FangqingCanonicalLateGateFamily.m0 c C h tail)
      (FangqingCanonicalLateGateFamily.m1 c C h tail) oldgate (initialX c h).ofLp 0
      (fun t => c.a • initialX c h t)) at hExact
  rw [hGateEq] at hExact
  exact ⟨hMin0, hMin1, hNorm, hBulk, hValid, hFlat, hExact⟩

end
end FangqingHierarchyLateGateWorldFactory
end

section
-- Source component: ActualPairedPacketExecution.lean

/- Actual paired endpoint replies in the executed disclosure protocol.
   All flat cores below are derived from small undisclosed COLUMN projections;
   no target reply equality is assumed. -/

open scoped Topology BigOperators

namespace OriginalActualPairedPacketExecution
open FangqingAmplifier FangqingPacketLeakage FangqingInactiveShellClass
  FangqingLocalizedSeedJets FangqingPublicShellProfiles OriginalPacketOrientationNormalization
  FangqingShellPrefixLocality OriginalPhysicalPairedShellPrefix

noncomputable section
set_option maxHeartbeats 2000000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem physical_first_inner (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ)
    (tail : Fin (n + 2) → W) (y : PhysicalSpace A B W) :
    inner ℝ (physicalFrame C h n tail 0) y = inner ℝ h (C.symm y.fst.snd) := by
  change (inner ℝ (0 : A) y.fst.fst + inner ℝ (C h) y.fst.snd) + inner ℝ (0 : W) y.snd = _
  rw [inner_zero_left, inner_zero_left, zero_add, add_zero]
  rw [← C.apply_symm_apply y.fst.snd, C.inner_map_map]
  simp only [C.symm_apply_apply]

theorem physical_tail_inner (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ)
    (tail : Fin (n + 2) → W) (y : PhysicalSpace A B W) (j : Fin (n + 2)) :
    inner ℝ (physicalFrame C h n tail j.succ) y = inner ℝ (tail j) y.snd := by
  change (inner ℝ (0 : A) y.fst.fst + inner ℝ (0 : B) y.fst.snd) + inner ℝ (tail j) y.snd = _
  simp only [inner_zero_left, zero_add]

theorem column_bounds_give_flat_edges
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n k : ℕ) (v : Fin (n + 3) → E) (y : E) (delta : ℝ) (hd : 0 < delta)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (v j) y| ≤ delta / 8) :
    ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| ≤ delta / 2 := by
  intro i hi
  have hleft := hsmall i.castSucc (by simpa only [Fin.val_castSucc] using hi)
  have hright := hsmall i.succ (by simp only [Fin.val_succ]; omega)
  rw [pathDirection, inner_sub_left]
  have hab := abs_sub (inner ℝ (v i.castSucc) y) (inner ℝ (v i.succ) y)
  linarith only [hab, hleft, hright, hd]

theorem inactive_columns_small
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n : ℕ) (tail : Fin (n + 2) → W)
    (y : PhysicalSpace A B W) (delta : ℝ)
    (hhandle : |inner ℝ h (C.symm y.fst.snd)| ≤ delta / 8)
    (htail : ∀ j, |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    ∀ j : Fin (n + 3), |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [physical_first_inner]; exact hhandle
  · rw [physical_tail_inner]; exact htail i

theorem active_later_columns_small
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W)
    (y : PhysicalSpace A B W) (delta : ℝ)
    (htail : ∀ j, k ≤ j.val → |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    ∀ j : Fin (n + 3), k + 1 ≤ j.val → |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8 := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro hj; simp only [Fin.val_zero] at hj; omega
  · intro hj
    rw [physical_tail_inner]
    exact htail i (by simp only [Fin.val_succ] at hj; omega)

theorem masked_tail_columns_small
    (n k disclosed : ℕ) (tail : Fin (n + 2) → W) (y : W) (delta : ℝ) (hd : 0 < delta)
    (htail : ∀ j, k ≤ j.val → |inner ℝ (tail j) y| ≤ delta / 8) :
    ∀ j, k ≤ j.val → |inner ℝ (FangqingPrefixAdaptedModel.mask disclosed tail j) y| ≤ delta / 8 := by
  intro j hj
  by_cases hdj : j.val < disclosed
  · simpa only [FangqingPrefixAdaptedModel.mask, if_pos hdj] using htail j hj
  · simp only [FangqingPrefixAdaptedModel.mask, if_neg hdj, inner_zero_left, abs_zero]
    positivity

theorem physical_masked_tail_preserves_one_boundary
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (n k : ℕ) (tail : Fin (n + 2) → W) :
    ∀ j : Fin (n + 3), j.val < (k + 1) + 1 →
      physicalFrame C h n tail j =
        physicalFrame C h n (FangqingPrefixAdaptedModel.mask (min (k + 1) (n + 2)) tail) j := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · intro _; rfl
  · intro hj
    have hik : i.val < min (k + 1) (n + 2) := lt_min (by simp only [Fin.val_succ] at hj; omega) i.isLt
    simp only [physicalFrame, Fin.cons_succ, FangqingPrefixAdaptedModel.mask, if_pos hik]

theorem physical_bundles_equal_of_common_prefix_and_column_bounds
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n k : ℕ) (C : A ≃ₗᵢ[ℝ] B) (h : A) (tail tail' : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi) (q nu scale R gain width amplitude : ℝ) (hR : 0 < R)
    (y : PhysicalSpace A B W)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → physicalFrame C h n tail j = physicalFrame C h n tail' j)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (physicalFrame C h n tail j) y| ≤ delta / 8)
    (hsmall' : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (physicalFrame C h n tail' j) y| ≤ delta / 8) :
    (bundle (actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain) y,
      bundle (actualActive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)) y) =
    (bundle (actualInactive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) scale R gain) y,
      bundle (actualActive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)) y) := by
  have hV := actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail
    phi hphi q nu scale R gain width amplitude hR y (column_bounds_give_flat_edges n k _ y delta hd hsmall)
  have hW := actual_physical_paired_closed_prefix_full_bundle P delta omega hd hdw n k C h tail'
    phi hphi q nu scale R gain width amplitude hR y (column_bounds_give_flat_edges n k _ y delta hd hsmall')
  have hInv := virtual_paired_prefix_invariant P delta omega n k (physicalFrame C h n tail)
    (physicalFrame C h n tail') hprefix (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0)
  dsimp only at hV hW
  rw [hInv.1, hInv.2] at hV
  exact hV.trans hW.symm

end
end OriginalActualPairedPacketExecution
end

section
-- Source component: ActualOracleFamilyContinuityCore.lean

namespace FangqingContinuousOracleFamily

variable {Parameter E : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradient_family_contDiff_one (f : Parameter → E → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    ContDiff ℝ 1 (fun p : Parameter × E => gradient (f p.1) p.2) := by
  have hext : ContDiff ℝ 2 (fun p : (Parameter × E) × E => f p.1.1 p.2) :=
    hf.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hder : ContDiff ℝ 1 (fun p : Parameter × E => fderiv ℝ (f p.1) p.2) :=
    hext.fderiv contDiff_snd (by norm_num)
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp hder

theorem continuous_actual_oracle_family (f : Parameter → E → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) :
    Continuous (fun p : Parameter × E =>
      FangqingShellPrefixLocality.bundle (f p.1) p.2) := by
  have hg := gradient_family_contDiff_one f hf
  have hext : ContDiff ℝ 1 (fun p : (Parameter × E) × E => gradient (f p.1.1) p.2) :=
    hg.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hh : ContDiff ℝ 0 (fun p : Parameter × E => fderiv ℝ (gradient (f p.1)) p.2) :=
    hext.fderiv contDiff_snd (by norm_num)
  exact hf.continuous.prodMk (hg.continuous.prodMk hh.continuous)

end FangqingContinuousOracleFamily
end

section
-- Source component: ActualPhysicalEndpointOracleFamily.lean

open scoped Topology BigOperators

namespace OriginalActualPhysicalEndpointOracleFamily
open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
  OriginalPhysicalPairedShellPrefix OriginalActualPairedPacketExecution

noncomputable section
set_option maxHeartbeats 2000000
variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

abbrev Parameter (A W : Type*) (n : ℕ) := A × (Fin (n + 2) → W)

def endpointZero (P : FlatCubic.Profile) (delta omega : ℝ) (n : ℕ) (C : A ≃ₗᵢ[ℝ] B)
    (q nu scale R gain : ℝ) (p : Parameter A W n) : PhysicalSpace A B W → ℝ :=
  actualInactive P delta omega n (physicalFrame C p.1 n p.2) (QPhysical q nu C) scale R gain

def endpointOne (P : FlatCubic.Profile) (delta omega : ℝ) (n : ℕ) (C : A ≃ₗᵢ[ℝ] B)
    (phi : ℝ → ℝ) (q nu scale R gain width amplitude : ℝ) (p : Parameter A W n) : PhysicalSpace A B W → ℝ :=
  actualActive P delta omega n (physicalFrame C p.1 n p.2) (QPhysical q nu C)
    phi scale R gain width amplitude (mkPhysical p.1 0 0)

theorem physical_column_inner_joint_contDiff (C : A ≃ₗᵢ[ℝ] B) (n : ℕ) (i : Fin (n + 3)) :
    ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
      inner ℝ (physicalFrame C p.1.1 n p.1.2 i) p.2) := by
  have hp := (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (A × B)) W).contDiff.comp
    (contDiff_snd : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W => p.2))
  have hab := (WithLp.prodContinuousLinearEquiv 2 ℝ A B).contDiff.comp hp.fst
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [physical_first_inner]
    convert! contDiff_fst.fst.inner ℝ (C.symm.contDiff.comp hab.snd) using 1
  · simp only [physical_tail_inner]
    convert! (((contDiff_apply ℝ W j).comp contDiff_fst.snd).inner ℝ hp.snd) using 1

theorem endpoint_zero_joint_contDiff
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (C : A ≃ₗᵢ[ℝ] B) (q nu scale R gain : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (endpointZero (W := W) P delta omega n C q nu scale R gain)) := by
  have hedge : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
      FangqingPathEdgeRegularity.pathEdge P delta omega (n + 2) (physicalFrame C p.1.1 n p.1.2) p.2) := by
    unfold FangqingPathEdgeRegularity.pathEdge
    apply ContDiff.sum
    intro i _
    apply (FlatCubic.edge_contDiff_two P delta omega hd hdw).comp
    simpa only [FangqingPathIncidenceBounds.pathDirection, inner_sub_left] using
      (physical_column_inner_joint_contDiff (W := W) C n i.castSucc).sub (physical_column_inner_joint_contDiff (W := W) C n i.succ)
  have hgate : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
      FangqingRadialGateBounds.scaledGate theta R 0 p.2) := by
    simp only [FangqingRadialGateBounds.scaledGate, sub_zero]
    exact (theta_smooth.of_le (by decide)).comp ((contDiff_snd.norm_sq ℝ).div_const _)
  have hcol := (FangqingRadialCollar.collar_contDiff_three (E := PhysicalSpace A B W) psi
    (psi_smooth.of_le (by decide)) R).of_le (show (2 : WithTop ℕ∞) ≤ 3 by norm_num)
  exact ((FangqingAmplifierRegularity.physical_quadratic_contDiff q nu C).comp contDiff_snd).add
    (hgate.mul (contDiff_const.mul hedge)) |>.add (contDiff_const.mul (hcol.comp contDiff_snd))

theorem endpoint_one_joint_contDiff
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (C : A ≃ₗᵢ[ℝ] B) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi)
    (q nu scale R gain width amplitude : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (endpointOne (W := W) P delta omega n C phi q nu scale R gain width amplitude)) := by
  have hp := (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (A × B)) W).contDiff.comp
    (contDiff_snd : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W => p.2))
  have hab := (WithLp.prodContinuousLinearEquiv 2 ℝ A B).contDiff.comp hp.fst
  have hseed : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
      localizedSeed theta phi R width amplitude (mkPhysical p.1.1 (0 : B) (0 : W)) p.2) := by
    have hi : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
        inner ℝ (mkPhysical p.1.1 (0 : B) (0 : W)) p.2) := by
      have he : (fun p : Parameter A W n × PhysicalSpace A B W => inner ℝ (mkPhysical p.1.1 (0 : B) (0 : W)) p.2) =
          fun p => inner ℝ p.1.1 p.2.fst.fst := by
        funext p
        change (inner ℝ p.1.1 p.2.fst.fst + inner ℝ (0 : B) p.2.fst.snd) + inner ℝ (0 : W) p.2.snd = _
        simp only [inner_zero_left, add_zero]
      rw [he]
      exact contDiff_fst.fst.inner ℝ hab.fst
    have hgate : ContDiff ℝ 2 (fun p : Parameter A W n × PhysicalSpace A B W =>
        FangqingRadialGateBounds.scaledGate theta R 0 p.2) := by
      simp only [FangqingRadialGateBounds.scaledGate, sub_zero]
      exact (theta_smooth.of_le (by decide)).comp ((contDiff_snd.norm_sq ℝ).div_const _)
    exact contDiff_const.mul (hgate.mul ((hphi.of_le (by norm_num)).comp (hi.div_const width)))
  exact (endpoint_zero_joint_contDiff P delta omega hd hdw n C q nu scale R gain).sub hseed

theorem actual_physical_oracle_families_continuous
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (C : A ≃ₗᵢ[ℝ] B) (phi : ℝ → ℝ) (hphi : ContDiff ℝ 3 phi)
    (q nu scale R gain width amplitude : ℝ) :
    Continuous (fun p : Parameter A W n × PhysicalSpace A B W =>
      FangqingShellPrefixLocality.bundle (endpointZero P delta omega n C q nu scale R gain p.1) p.2) ∧
    Continuous (fun p : Parameter A W n × PhysicalSpace A B W =>
      FangqingShellPrefixLocality.bundle (endpointOne P delta omega n C phi q nu scale R gain width amplitude p.1) p.2) := by
  exact ⟨FangqingContinuousOracleFamily.continuous_actual_oracle_family _
      (endpoint_zero_joint_contDiff P delta omega hd hdw n C q nu scale R gain),
    FangqingContinuousOracleFamily.continuous_actual_oracle_family _
      (endpoint_one_joint_contDiff P delta omega hd hdw n C phi hphi q nu scale R gain width amplitude)⟩

end
end OriginalActualPhysicalEndpointOracleFamily
end

section
-- Source component: PreHitGateGeometry.lean

open scoped BigOperators Topology

namespace FangqingPreHitGateGeometry

open FangqingAmplifier OriginalPacketOrientationNormalization OriginalPhysicalPacketMinimizer
  OriginalPacketDistanceGapBounds OriginalPacketBulkIndexing FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 3500000

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype I]

theorem early_distance_from_unrevealed_coefficients
    (v : I → E) (hv : Orthonormal ℝ v) (J : Finset I) (Z w : E)
    (q omega : ℝ) (hq : 1 ≤ q) (hw : 0 ≤ omega)
    (hcard : 3 * q / 4 ≤ (J.card : ℝ))
    (hbulk : ∀ i ∈ J, 3 * q * omega ≤ inner ℝ (v i) Z)
    (hsmall : ∀ i ∈ J, |inner ℝ (v i) w| ≤ omega / 4) :
    (9 / 4 : ℝ) * distanceScale q omega ≤ ‖Z - w‖ := by
  have hq0 : 0 ≤ q := by linarith only [hq]
  have hqomega : omega ≤ q * omega := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hq hw
  have hcoef : ∀ i ∈ J, ((11 / 4 : ℝ) * q * omega) ^ 2 ≤ (inner ℝ (v i) (Z - w)) ^ 2 := by
    intro i hi
    have hs : inner ℝ (v i) w ≤ omega / 4 := (le_abs_self _).trans (hsmall i hi)
    have hd : (11 / 4 : ℝ) * q * omega ≤ inner ℝ (v i) (Z - w) := by
      rw [inner_sub_right]
      linarith only [hbulk i hi, hs, hqomega]
    have hp : 0 ≤ (11 / 4 : ℝ) * q * omega := by positivity
    exact (sq_le_sq₀ hp (hp.trans hd)).mpr hd
  have hsum : (J.card : ℝ) * ((11 / 4 : ℝ) * q * omega) ^ 2 ≤
      ∑ i ∈ J, (inner ℝ (v i) (Z - w)) ^ 2 := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hcoef
  have hB := hv.sum_inner_products_le (Z - w) (s := J)
  simp only [Real.norm_eq_abs, sq_abs] at hB
  have hcount := mul_le_mul_of_nonneg_right hcard (sq_nonneg ((11 / 4 : ℝ) * q * omega))
  have hDsq := distanceScale_sq q omega hq0
  have hD : 0 ≤ distanceScale q omega := by unfold distanceScale; positivity
  have hsq : ((9 / 4 : ℝ) * distanceScale q omega) ^ 2 ≤ ‖Z - w‖ ^ 2 := by
    nlinarith only [hcount, hsum, hB, hDsq, sq_nonneg (distanceScale q omega)]
  nlinarith only [hsq, hD, norm_nonneg (Z - w)]

theorem early_unrevealed_card (n q k : ℕ) (hfit : q ≤ n + 2) (hq : 8 ≤ q) (hk : k ≤ q / 8 + 1) :
    3 * (q : ℝ) / 4 ≤ ((unrevealedFirstTail n q k hfit).card : ℝ) := by
  have hfour : 4 * k ≤ q := by omega
  have hkq : k ≤ q := by omega
  rw [unrevealedFirstTail_card n q k hfit hkq, Nat.cast_sub hkq]
  have hfour' : 4 * (k : ℝ) ≤ (q : ℝ) := by exact_mod_cast hfour
  linarith only [hfour']

theorem gate_is_flat_outside_twice_radius (R : ℝ) (center z : E) (hR : 0 < R)
    (hz : 2 * R ≤ ‖z - center‖) :
    scaledGate theta R center =ᶠ[𝓝 z] (fun _ => 0) := by
  have hd : (7 / 4 : ℝ) * R < ‖z - center‖ := by linarith only [hR, hz]
  have hn : {u : E | (7 / 4 : ℝ) * R < ‖u - center‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hd
  filter_upwards [hn] with u hu
  unfold scaledGate
  apply theta_zero
  apply (le_div_iff₀ (sq_pos_of_pos hR)).mpr
  have hs : ((7 / 4 : ℝ) * R) ^ 2 ≤ ‖u - center‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hu.le
  nlinarith only [hs]

theorem gate_zero_jet_outside_twice_radius (R : ℝ) (center z : E) (hR : 0 < R)
    (hz : 2 * R ≤ ‖z - center‖) :
    scaledGate theta R center z = 0 ∧ fderiv ℝ (scaledGate theta R center) z = 0 ∧
      fderiv ℝ (fderiv ℝ (scaledGate theta R center)) z = 0 := by
  have heq := gate_is_flat_outside_twice_radius R center z hR hz
  refine ⟨heq.eq_of_nhds, ?_, ?_⟩
  · have hh := heq.fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (scaledGate theta R center) z = fderiv ℝ (0 : E → ℝ) z at hh
    simpa only [fderiv_zero, Pi.zero_apply] using hh
  · have hh := (heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    change fderiv ℝ (fderiv ℝ (scaledGate theta R center)) z =
      fderiv ℝ (fderiv ℝ (0 : E → ℝ)) z at hh
    simpa only [fderiv_zero, Pi.zero_apply] using hh


variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem actual_early_private_gate_flat (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (n q k : ℕ) (tail : Fin (n + 2) → W) (ht : Orthonormal ℝ tail)
    (hq : 8 ≤ q) (hfit : q ≤ n + 2) (hk : k ≤ q / 8 + 1)
    (delta omega beta lam a ell : ℝ)
    (hd : 0 ≤ delta) (hdw : delta ≤ omega) (hw : 0 < omega)
    (hb : 0 < beta) (hl : 0 < lam) (ha : 0 < a) (he : 0 < ell)
    (hell : ell = lam / beta * distanceScale q omega)
    (Z candidate : PhysicalSpace A B W)
    (hbulk : ∀ j : Fin (n + 3), (j.val : ℝ) ≤ q →
      3 * (q : ℝ) * omega ≤ inner ℝ (physicalFrame C h n tail j) Z)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val →
      |inner ℝ (physicalFrame C h n tail j) ((-beta / lam) • candidate)| ≤ delta / 4) :
    let xstar := (-lam / beta) • Z
    (9 / 4 : ℝ) * ell ≤ ‖candidate - xstar‖ ∧
    2 * ell < ‖candidate - xstar‖ ∧
    2 * (a * ell) < ‖a • candidate - a • xstar‖ ∧
    scaledGate theta (a * ell) (a • xstar) =ᶠ[𝓝 (a • candidate)] (fun _ => 0) := by
  intro xstar
  let J := unrevealedFirstTail n q k hfit
  have hkhalf : k ≤ q / 2 := by omega
  have hidx := actual_unrevealed_index_properties n q k hfit hkhalf
  have hcard := early_unrevealed_card n q k hfit hq hk
  have hsmall' : ∀ j ∈ J,
      |inner ℝ (physicalFrame C h n tail j) ((-beta / lam) • candidate)| ≤ omega / 4 := by
    intro j hj
    exact (hsmall j (hidx.1 j hj).2).trans (by linarith only [hdw])
  have hSep := early_distance_from_unrevealed_coefficients (physicalFrame C h n tail)
    (physicalFrame_orthonormal C h hh n tail ht) J Z ((-beta / lam) • candidate) q omega
    (by exact_mod_cast (show 1 ≤ q by omega)) hw.le hcard
    (fun j hj => hbulk j (hidx.1 j hj).1) hsmall'
  have hcoef : (lam / beta) * (-beta / lam) = -1 := by field_simp; try ring
  have halg : candidate - xstar = (lam / beta) • (Z - (-beta / lam) • candidate) := by
    rw [smul_sub, smul_smul, hcoef, neg_one_smul, sub_neg_eq_add]
    dsimp [xstar]
    rw [neg_div, neg_smul, sub_neg_eq_add]
    abel
  have hPrimal : (9 / 4 : ℝ) * ell ≤ ‖candidate - xstar‖ := by
    rw [halg, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hl hb), hell]
    convert! mul_le_mul_of_nonneg_left hSep (div_pos hl hb).le using 1 <;> ring
  have hOutside : 2 * ell < ‖candidate - xstar‖ := by linarith only [hPrimal, he]
  have hRelay : 2 * (a * ell) < ‖a • candidate - a • xstar‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    have hh := mul_lt_mul_of_pos_left hOutside ha
    nlinarith only [hh]
  exact ⟨hPrimal, hOutside, hRelay,
    gate_is_flat_outside_twice_radius (a * ell) (a • xstar) (a • candidate) (mul_pos ha he) hRelay.le⟩

end
end FangqingPreHitGateGeometry
end

section
-- Source component: PreHitRelayLocality.lean

open scoped BigOperators Topology

namespace FangqingPreHitRelayLocality

open FangqingRelayAnalyticAssembly FangqingRelayStationarity FangqingRelayBlockGeometry
  FangqingDisjointBlockBounds FangqingPreHitGateGeometry FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 3000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def fullReply {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f : X → ℝ) (z : X) : ℝ × X × (X →L[ℝ] X) :=
  (f z, gradient f z, fderiv ℝ (gradient f) z)

theorem fullReply_of_germ {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (f g : X → ℝ) (z : X) (h : f =ᶠ[𝓝 z] g) : fullReply f z = fullReply g z := by
  unfold fullReply
  rw [h.eq_of_nhds, h.gradient_eq, h.gradient.fderiv_eq]

def suppressOwnGate (n : ℕ) (own : Fin n) (gate : Fin n → E → ℝ) : Fin n → E → ℝ :=
  Function.update gate own (fun _ => 0)

theorem assembled_germ_of_gate_germs (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate other : Fin n → E → ℝ) (z : Joint n E)
    (hg : ∀ j, gate j =ᶠ[𝓝 (z (2, j.castSucc))] other j) :
    assembled n beta lam a sigma reward h0 h1 m0 m1 gate =ᶠ[𝓝 z]
      assembled n beta lam a sigma reward h0 h1 m0 m1 other := by
  have hlocal : ∀ j, ∀ᶠ w : Joint n E in 𝓝 z, gate j (w (2, j.castSucc)) = other j (w (2, j.castSucc)) := by
    intro j
    exact (hg j).comp_tendsto (coord n 2 j.castSucc).continuous.continuousAt
  filter_upwards [Filter.eventually_all.mpr hlocal] with w hw
  have hlinks : blockSum (link n) (localLink n reward h0 h1 m0 m1 gate) w =
      blockSum (link n) (localLink n reward h0 h1 m0 m1 other) w := by
    unfold blockSum
    apply Finset.sum_congr rfl
    intro j _
    change gate j (w (2, j.castSucc)) * _ = other j (w (2, j.castSucc)) * _
    rw [hw j]
  unfold assembled
  rw [hlinks]

theorem assembled_equals_own_suppressed_near_query (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (own : Fin n) (z : Joint n E)
    (hown : gate own =ᶠ[𝓝 (z (2, own.castSucc))] (fun _ => 0)) :
    assembled n beta lam a sigma reward h0 h1 m0 m1 gate =ᶠ[𝓝 z]
      assembled n beta lam a sigma reward h0 h1 m0 m1 (suppressOwnGate n own gate) := by
  apply assembled_germ_of_gate_germs
  intro j
  by_cases hj : j = own
  · subst j
    simpa [suppressOwnGate] using hown
  · apply Filter.Eventually.of_forall
    intro u
    simp only [suppressOwnGate, Function.update_of_ne hj]

theorem full_actual_relay_bundle_equals_own_suppressed (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (own : Fin n) (z : Joint n E)
    (hown : gate own =ᶠ[𝓝 (z (2, own.castSucc))] (fun _ => 0)) :
    fullReply (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) z =
      fullReply (assembled n beta lam a sigma reward h0 h1 m0 m1 (suppressOwnGate n own gate)) z :=
  fullReply_of_germ _ _ z (assembled_equals_own_suppressed_near_query n beta lam a sigma reward h0 h1 m0 m1 gate own z hown)

theorem actual_private_radial_gate_full_bundle_suppression (n : ℕ) (beta lam a sigma reward ell : ℝ)
    (h0 h1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (own : Fin n) (xstar : E) (z : Joint n E)
    (ha : 0 < a) (hell : 0 < ell)
    (hgate : gate own = scaledGate theta (a * ell) (a • xstar))
    (hOutside : 2 * (a * ell) ≤ ‖z (2, own.castSucc) - a • xstar‖) :
    fullReply (assembled n beta lam a sigma reward h0 h1 m0 m1 gate) z =
      fullReply (assembled n beta lam a sigma reward h0 h1 m0 m1 (suppressOwnGate n own gate)) z := by
  apply full_actual_relay_bundle_equals_own_suppressed
  rw [hgate]
  exact gate_is_flat_outside_twice_radius (a * ell) (a • xstar) (z (2, own.castSucc)) (mul_pos ha hell) hOutside

theorem assembled_germ_of_all_endpoint_germs (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 k0 k1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (z : Joint n E)
    (hh0 : ∀ t, h0 t =ᶠ[𝓝 (z (1, t))] k0 t) (hh1 : ∀ t, h1 t =ᶠ[𝓝 (z (1, t))] k1 t) :
    assembled n beta lam a sigma reward h0 h1 m0 m1 gate =ᶠ[𝓝 z]
      assembled n beta lam a sigma reward k0 k1 m0 m1 gate := by
  have hl0 : ∀ t, ∀ᶠ w : Joint n E in 𝓝 z, h0 t (w (1, t)) = k0 t (w (1, t)) := by
    intro t
    exact (hh0 t).comp_tendsto (coord n 1 t).continuous.continuousAt
  have hl1 : ∀ t, ∀ᶠ w : Joint n E in 𝓝 z, h1 t (w (1, t)) = k1 t (w (1, t)) := by
    intro t
    exact (hh1 t).comp_tendsto (coord n 1 t).continuous.continuousAt
  filter_upwards [Filter.eventually_all.mpr hl0, Filter.eventually_all.mpr hl1] with w hw0 hw1
  rw [assembled_eq_family, assembled_eq_family]
  simp only [family, endpoint, delta, hw0, hw1]


theorem family_eq_from_weighted_endpoint_values (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 k0 k1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (x y s : Fin (n + 1) → E)
    (hh0 : ∀ t, h0 t (y t) = k0 t (y t))
    (hh1 : ∀ t, incoming n gate s t ≠ 0 → h1 t (y t) = k1 t (y t)) :
    family n beta lam a sigma reward h0 h1 m0 m1 gate x y s =
      family n beta lam a sigma reward k0 k1 m0 m1 gate x y s := by
  have hsum : (∑ t, (endpoint beta lam (h0 t) (m0 t) (x t) (y t) +
      incoming n gate s t * delta (h0 t) (h1 t) (m0 t) (m1 t) (y t))) =
      ∑ t, (endpoint beta lam (k0 t) (m0 t) (x t) (y t) +
      incoming n gate s t * delta (k0 t) (k1 t) (m0 t) (m1 t) (y t)) := by
    apply Finset.sum_congr rfl
    intro t _
    by_cases hz : incoming n gate s t = 0
    · simp only [endpoint, delta, hh0 t, hz, zero_mul, add_zero]
    · simp only [endpoint, delta, hh0 t, hh1 t hz]
  unfold family
  rw [hsum]

theorem assembled_germ_from_weighted_endpoint_germs (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 k0 k1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (z : Joint n E)
    (hh0 : ∀ t, h0 t =ᶠ[𝓝 (z (1, t))] k0 t)
    (hh1 : ∀ t, (h1 t =ᶠ[𝓝 (z (1, t))] k1 t) ∨
      ((fun w : Joint n E => incoming n gate (fun u => w (2, u)) t) =ᶠ[𝓝 z] (fun _ => 0))) :
    assembled n beta lam a sigma reward h0 h1 m0 m1 gate =ᶠ[𝓝 z]
      assembled n beta lam a sigma reward k0 k1 m0 m1 gate := by
  have hl0 : ∀ t, ∀ᶠ w : Joint n E in 𝓝 z, h0 t (w (1, t)) = k0 t (w (1, t)) := by
    intro t
    exact (hh0 t).comp_tendsto (coord n 1 t).continuous.continuousAt
  have hl1 : ∀ t, ∀ᶠ w : Joint n E in 𝓝 z,
      incoming n gate (fun u => w (2, u)) t ≠ 0 → h1 t (w (1, t)) = k1 t (w (1, t)) := by
    intro t
    rcases hh1 t with hlocal | hzero
    · filter_upwards [hlocal.comp_tendsto (coord n 1 t).continuous.continuousAt] with w hw _
      exact hw
    · filter_upwards [hzero] with w hw hn
      exact (hn hw).elim
  filter_upwards [Filter.eventually_all.mpr hl0, Filter.eventually_all.mpr hl1] with w hw0 hw1
  rw [assembled_eq_family, assembled_eq_family]
  exact family_eq_from_weighted_endpoint_values n beta lam a sigma reward h0 h1 k0 k1 m0 m1 gate
    (fun t => w (0, t)) (fun t => w (1, t)) (fun t => w (2, t)) hw0 hw1

theorem incoming_private_gate_germ_zero_before_activation (n : ℕ) (gate : Fin n → E → ℝ)
    (j : Fin n) (a ell : ℝ) (previousPrivateCenter : E) (z : Joint n E)
    (ha : 0 < a) (he : 0 < ell)
    (hgate : gate j = scaledGate theta (a * ell) (a • previousPrivateCenter))
    (hout : 2 * (a * ell) ≤ ‖z (2, j.castSucc) - a • previousPrivateCenter‖) :
    (fun w : Joint n E => incoming n gate (fun t => w (2, t)) j.succ) =ᶠ[𝓝 z] (fun _ => 0) := by
  have hg : gate j =ᶠ[𝓝 (z (2, j.castSucc))] (fun _ => 0) := by
    rw [hgate]
    exact gate_is_flat_outside_twice_radius (a * ell) (a • previousPrivateCenter)
      (z (2, j.castSucc)) (mul_pos ha he) hout
  have hp := hg.comp_tendsto (coord n 2 j.castSucc).continuous.continuousAt
  filter_upwards [hp] with w hw
  exact hw

end
end FangqingPreHitRelayLocality
end

section
-- Source component: PreHitPhysicalPacketGerms.lean

open scoped Topology

namespace FangqingPreHitPhysicalPacketGerms

open FangqingPacketLeakage FangqingAmplifier OriginalPacketOrientationNormalization
  OriginalPhysicalPairedShellPrefix OriginalActualPairedPacketExecution FangqingPrefixAdaptedModel
  FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles

noncomputable section

set_option maxHeartbeats 2500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem column_bounds_give_strict_flat_edges
    (n k : ℕ) (v : Fin (n + 3) → E) (y : E) (delta : ℝ) (hd : 0 < delta)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (v j) y| ≤ delta / 8) :
    ∀ i : Fin (n + 2), k ≤ i.val → |inner ℝ (pathDirection n v i) y| < delta / 2 := by
  intro i hi
  have hleft := hsmall i.castSucc (by simpa only [Fin.val_castSucc] using hi)
  have hright := hsmall i.succ (by simp only [Fin.val_succ]; omega)
  rw [pathDirection, inner_sub_left]
  have hab := abs_sub (inner ℝ (v i.castSucc) y) (inner ℝ (v i.succ) y)
  linarith only [hab, hleft, hright, hd]

theorem actual_paired_germs_of_common_prefix
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n k : ℕ) (v w : Fin (n + 3) → E) (Q : E → ℝ) (phi : ℝ → ℝ)
    (scale R gain A amplitude : ℝ) (handle y : E)
    (hprefix : ∀ j : Fin (n + 3), j.val < k + 1 → v j = w j)
    (hsmall : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (v j) y| ≤ delta / 8)
    (hsmall' : ∀ j : Fin (n + 3), k ≤ j.val → |inner ℝ (w j) y| ≤ delta / 8) :
    (actualInactive P delta omega n v Q scale R gain =ᶠ[𝓝 y]
      actualInactive P delta omega n w Q scale R gain) ∧
    (actualActive P delta omega n v Q phi scale R gain A amplitude handle =ᶠ[𝓝 y]
      actualActive P delta omega n w Q phi scale R gain A amplitude handle) := by
  have hV0 := actualInactive_eventually_virtual P delta omega hd hdw n k v Q scale R gain y
    (column_bounds_give_strict_flat_edges n k v y delta hd hsmall)
  have hW0 := actualInactive_eventually_virtual P delta omega hd hdw n k w Q scale R gain y
    (column_bounds_give_strict_flat_edges n k w y delta hd hsmall')
  have hV1 := actualActive_eventually_virtual P delta omega hd hdw n k v Q phi scale R gain A amplitude handle y
    (column_bounds_give_strict_flat_edges n k v y delta hd hsmall)
  have hW1 := actualActive_eventually_virtual P delta omega hd hdw n k w Q phi scale R gain A amplitude handle y
    (column_bounds_give_strict_flat_edges n k w y delta hd hsmall')
  have hi := virtual_paired_prefix_invariant P delta omega n k v w hprefix Q phi scale R gain A amplitude handle
  rw [hi.1] at hV0
  rw [hi.2] at hV1
  exact ⟨hV0.trans hW0.symm, hV1.trans hW1.symm⟩

theorem actual_inactive_germ_public_before_handle
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (v : Fin (n + 3) → E) (Q : E → ℝ) (scale R gain : ℝ) (y : E)
    (hsmall : ∀ j : Fin (n + 3), |inner ℝ (v j) y| ≤ delta / 8) :
    actualInactive P delta omega n v Q scale R gain =ᶠ[𝓝 y] publicEndpoint Q R gain := by
  have he := actualInactive_eventually_virtual P delta omega hd hdw n 0 v Q scale R gain y
    (column_bounds_give_strict_flat_edges n 0 v y delta hd (fun j _ => hsmall j))
  filter_upwards [he] with z hz
  rw [hz]
  simp only [virtualInactive, FangqingShellPrefixLocality.prefixEdges, Nat.not_lt_zero, Finset.filter_false,
    FangqingShellPrefixLocality.selectedEdgeSum, Finset.sum_empty, mul_zero, inactiveShell, mul_zero, add_zero, publicEndpoint]

theorem subtract_public_quadratic_preserves_germ (f g : E → ℝ) (c : ℝ) (y : E)
    (h : f =ᶠ[𝓝 y] g) :
    (fun z => f z - c / 2 * ‖z‖ ^ 2) =ᶠ[𝓝 y] (fun z => g z - c / 2 * ‖z‖ ^ 2) := by
  filter_upwards [h] with z hz
  rw [hz]

variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_paired_germs_after_one_boundary
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n k : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain A amplitude : ℝ) (y : PhysicalSpace A0 B0 W)
    (hsmall : ∀ j : Fin (n + 2), k ≤ j.val → |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    let tail' := mask (min (k + 1) (n + 2)) tail
    (actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain =ᶠ[𝓝 y]
      actualInactive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) scale R gain) ∧
    (actualActive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain A amplitude (mkPhysical h 0 0) =ᶠ[𝓝 y]
      actualActive P delta omega n (physicalFrame C h n tail') (QPhysical q nu C) phi scale R gain A amplitude (mkPhysical h 0 0)) := by
  intro tail'
  exact actual_paired_germs_of_common_prefix P delta omega hd hdw n (k + 1)
    (physicalFrame C h n tail) (physicalFrame C h n tail') (QPhysical q nu C) phi scale R gain A amplitude
    (mkPhysical h 0 0) y (physical_masked_tail_preserves_one_boundary C h n k tail)
    (active_later_columns_small C h n k tail y delta hsmall)
    (active_later_columns_small C h n k tail' y delta
      (masked_tail_columns_small n k (min (k + 1) (n + 2)) tail y.snd delta hd hsmall))

end
end FangqingPreHitPhysicalPacketGerms
end

section
-- Source component: RelayOracleParameterRegularity.lean

open scoped BigOperators ContDiff

namespace FangqingRelayOracleParameterRegularity

open FangqingRelayStationarity FangqingRelayBlockGeometry FangqingRelayAnalyticAssembly
  FangqingDisjointBlockBounds FangqingPreHitRelayLocality

noncomputable section

set_option maxHeartbeats 3000000

variable {Parameter E : Type*}
  [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem endpoint_parameter_regular (beta lam : ℝ) (h : Parameter → E → ℝ) (m : Parameter → ℝ)
    (hh : ContDiff ℝ 2 (Function.uncurry h)) (hm : ContDiff ℝ 2 m)
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : X → Parameter) (x y : X → E) (hp : ContDiff ℝ 2 p) (hx : ContDiff ℝ 2 x) (hy : ContDiff ℝ 2 y) :
    ContDiff ℝ 2 (fun z => endpoint beta lam (h (p z)) (m (p z)) (x z) (y z)) := by
  exact (((contDiff_const.mul (hx.norm_sq ℝ)).add (contDiff_const.mul (hx.inner ℝ hy))).sub
    (hh.comp (hp.prodMk hy))).add (hm.comp hp)

theorem assembled_parameter_regular (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Parameter → Fin (n + 1) → E → ℝ) (m0 m1 : Parameter → Fin (n + 1) → ℝ)
    (gate : Parameter → Fin n → E → ℝ)
    (hh0 : ∀ t, ContDiff ℝ 2 (fun z : Parameter × E => h0 z.1 t z.2))
    (hh1 : ∀ t, ContDiff ℝ 2 (fun z : Parameter × E => h1 z.1 t z.2))
    (hm0 : ∀ t, ContDiff ℝ 2 (fun p => m0 p t))
    (hm1 : ∀ t, ContDiff ℝ 2 (fun p => m1 p t))
    (hg : ∀ j, ContDiff ℝ 2 (fun z : Parameter × E => gate z.1 j z.2)) :
    ContDiff ℝ 2 (fun z : Parameter × Joint n E =>
      assembled n beta lam a sigma reward (h0 z.1) (h1 z.1) (m0 z.1) (m1 z.1) (gate z.1) z.2) := by
  have hc (axis : Fin 3) (t : Fin (n + 1)) :
      ContDiff ℝ 2 (fun z : Parameter × Joint n E => z.2 (axis, t)) :=
    by
    convert! (coord (E := E) n axis t).contDiff.comp
      (contDiff_snd : ContDiff ℝ 2 (fun z : Parameter × Joint n E => z.2)) using 1
  have hh0c (t : Fin (n + 1)) : ContDiff ℝ 2 (fun z : Parameter × Joint n E => h0 z.1 t (z.2 (1, t))) :=
    (hh0 t).comp (contDiff_fst.prodMk (hc 1 t))
  have hh1c (t : Fin (n + 1)) : ContDiff ℝ 2 (fun z : Parameter × Joint n E => h1 z.1 t (z.2 (1, t))) :=
    (hh1 t).comp (contDiff_fst.prodMk (hc 1 t))
  have hp : ∀ t, ContDiff ℝ 2 (fun z : Parameter × Joint n E =>
      localPacket n beta lam (h0 z.1) (h1 z.1) (m0 z.1) (m1 z.1) t (packet n t z.2)) := by
    intro t
    refine Fin.cases ?_ (fun j => ?_) t
    · exact endpoint_parameter_regular beta lam (fun p => h1 p 0) (fun p => m1 p 0) (hh1 0) (hm1 0)
        Prod.fst (fun z : Parameter × Joint n E => z.2 (0, 0)) (fun z => z.2 (1, 0)) contDiff_fst (hc 0 0) (hc 1 0)
    · exact endpoint_parameter_regular beta lam (fun p => h0 p j.succ) (fun p => m0 p j.succ) (hh0 j.succ) (hm0 j.succ)
        Prod.fst (fun z : Parameter × Joint n E => z.2 (0, j.succ)) (fun z => z.2 (1, j.succ))
        contDiff_fst (hc 0 j.succ) (hc 1 j.succ)
  have hr : ∀ t, ContDiff ℝ 2 (fun z : Parameter × Joint n E => localRelay a sigma (relay n t z.2)) := by
    intro t
    exact contDiff_const.mul (((hc 2 t).sub ((hc 0 t).const_smul a)).norm_sq ℝ)
  have hl : ∀ j, ContDiff ℝ 2 (fun z : Parameter × Joint n E =>
      localLink n reward (h0 z.1) (h1 z.1) (m0 z.1) (m1 z.1) (gate z.1) j (link n j z.2)) := by
    intro j
    exact ((hg j).comp (contDiff_fst.prodMk (hc 2 j.castSucc))).mul
      (((((hh0c j.succ).sub (hh1c j.succ)).add ((hm1 j.succ).comp contDiff_fst)).sub
        ((hm0 j.succ).comp contDiff_fst)).sub contDiff_const)
  exact ((ContDiff.sum (fun t _ => hp t)).add (ContDiff.sum (fun t _ => hr t))).add
    (ContDiff.sum (fun j _ => hl j))

theorem actual_joint_oracle_continuous_in_parameters (n : ℕ) (beta lam a sigma reward : ℝ)
    (h0 h1 : Parameter → Fin (n + 1) → E → ℝ) (m0 m1 : Parameter → Fin (n + 1) → ℝ)
    (gate : Parameter → Fin n → E → ℝ)
    (hh0 : ∀ t, ContDiff ℝ 2 (fun z : Parameter × E => h0 z.1 t z.2))
    (hh1 : ∀ t, ContDiff ℝ 2 (fun z : Parameter × E => h1 z.1 t z.2))
    (hm0 : ∀ t, ContDiff ℝ 2 (fun p => m0 p t))
    (hm1 : ∀ t, ContDiff ℝ 2 (fun p => m1 p t))
    (hg : ∀ j, ContDiff ℝ 2 (fun z : Parameter × E => gate z.1 j z.2)) :
    Continuous (fun z : Parameter × Joint n E => fullReply
      (assembled n beta lam a sigma reward (h0 z.1) (h1 z.1) (m0 z.1) (m1 z.1) (gate z.1)) z.2) :=
by
  change Continuous (fun z : Parameter × Joint n E => FangqingShellPrefixLocality.bundle
    (assembled n beta lam a sigma reward (h0 z.1) (h1 z.1) (m0 z.1) (m1 z.1) (gate z.1)) z.2)
  exact FangqingContinuousOracleFamily.continuous_actual_oracle_family
    (fun p : Parameter => assembled n beta lam a sigma reward (h0 p) (h1 p) (m0 p) (m1 p) (gate p))
    (assembled_parameter_regular n beta lam a sigma reward h0 h1 m0 m1 gate hh0 hh1 hm0 hm1 hg)

end
end FangqingRelayOracleParameterRegularity
end

section
-- Source component: StoppedTwoGroupReplay.lean

namespace FangqingStoppedTwoGroupReplay

open OriginalPrefixOracleReplay OriginalTwoGroupPrefixExecution

set_option maxHeartbeats 2500000

theorem before_firstHit_is_false (N : ℕ) (b : ℕ → Bool) (j : ℕ)
    (hj : j < firstHitUntil N b) : b j = false := by
  induction N generalizing b j with
  | zero => simp only [firstHitUntil] at hj; omega
  | succ N ih =>
      by_cases hb : b 0 = true
      · simp [firstHitUntil, hb] at hj
      · have hb0 : b 0 = false := by cases h : b 0 <;> simp_all
        simp [firstHitUntil, hb] at hj
        cases j with
        | zero => exact hb0
        | succ j => exact ih (fun n => b (n + 1)) j (by omega)

theorem firstHit_is_hit_when_lt (N : ℕ) (b : ℕ → Bool)
    (h : firstHitUntil N b < N) : b (firstHitUntil N b) = true := by
  induction N generalizing b with
  | zero => omega
  | succ N ih =>
      by_cases hb : b 0 = true
      · simpa [firstHitUntil, hb] using hb
      · simp [firstHitUntil, hb] at h ⊢
        exact ih (fun n => b (n + 1)) (by omega)

theorem firstHit_le_of_hit (N : ℕ) (b : ℕ → Bool) (j : ℕ)
    (hj : j < N) (hbj : b j = true) : firstHitUntil N b ≤ j := by
  induction N generalizing b j with
  | zero => omega
  | succ N ih =>
      by_cases hb : b 0 = true
      · simp [firstHitUntil, hb]
      · simp [firstHitUntil, hb]
        cases j with
        | zero => exact False.elim (hb hbj)
        | succ j =>
            have hh := ih (fun n => b (n + 1)) j (by omega) hbj
            omega

variable {Seed Side H W Q A : Type*} {m : ℕ} [Zero H] [Zero W] [Zero A]

theorem literal_replay_stopped_at_virtual_first_hit
    (query : OriginalTwoGroupPrefixExecution.Query Seed A Q) (dec : Activation Side A Q)
    (realReply virtualReply : Reply Seed Side H W A Q m)
    (hit : Q → Bool) (out : Seed → OriginalTwoGroupPrefixExecution.History A → Q)
    (N : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W)
    (hlocal : ∀ j < N,
      let st := run query dec virtualReply j seed side handle tail
      let z := query j seed st.2.2
      hit z = false →
      let kh := nextHandle dec j side st z
      let kt := nextTail (m := m) st
      realReply j seed side st kh kt handle tail z = virtualReply j seed side st kh kt
        (FangqingPrefixAdaptedModel.mask kh handle) (FangqingPrefixAdaptedModel.mask kt tail) z) :
    let vhit := fun j => hit (query j seed (run query dec virtualReply j seed side handle tail).2.2)
    let stop := firstHitUntil N vhit
    (∀ j ≤ stop, fullRun query dec realReply j seed side handle tail = run query dec virtualReply j seed side handle tail) ∧
    firstHitUntil N (fun j => hit (query j seed (fullRun query dec realReply j seed side handle tail).2.2)) = stop ∧
    (stop = N → out seed (fullRun query dec realReply N seed side handle tail).2.2 =
      out seed (run query dec virtualReply N seed side handle tail).2.2) := by
  intro vhit stop
  have hStopN : stop ≤ N := firstHitUntil_le N vhit
  have hlocalStop : ∀ j < stop,
      let st := run query dec virtualReply j seed side handle tail
      let z := query j seed st.2.2
      let kh := nextHandle dec j side st z
      let kt := nextTail (m := m) st
      realReply j seed side st kh kt handle tail z = virtualReply j seed side st kh kt
        (FangqingPrefixAdaptedModel.mask kh handle) (FangqingPrefixAdaptedModel.mask kt tail) z := by
    intro j hj
    exact hlocal j (lt_of_lt_of_le hj hStopN) (before_firstHit_is_false N vhit j hj)
  obtain ⟨hstate, hqueries⟩ := literal_real_virtual_replay query dec realReply virtualReply stop seed side handle tail hlocalStop
  let rhit := fun j => hit (query j seed (fullRun query dec realReply j seed side handle tail).2.2)
  have hnoReal : ∀ j < stop, rhit j = false := by
    intro j hj
    dsimp [rhit]
    rw [hqueries j hj]
    exact before_firstHit_is_false N vhit j hj
  have hLower : stop ≤ firstHitUntil N rhit := firstHitUntil_lower_bound N stop rhit hStopN hnoReal
  have hFirstEq : firstHitUntil N rhit = stop := by
    by_cases hEq : stop = N
    · have hh := firstHitUntil_le N rhit
      omega
    · have hlt : stop < N := by omega
      have hv := firstHit_is_hit_when_lt N vhit hlt
      have hr : rhit stop = true := by
        dsimp [rhit]
        rw [hstate stop le_rfl]
        exact hv
      exact le_antisymm (firstHit_le_of_hit N rhit stop hlt hr) hLower
  refine ⟨hstate, hFirstEq, ?_⟩
  intro hEq
  exact congrArg (fun st : OriginalTwoGroupPrefixExecution.State A => out seed st.2.2) (hstate N (by omega))

end FangqingStoppedTwoGroupReplay
end

section
-- Source component: PreHitRelayPacketReplacement.lean

open scoped Topology

namespace FangqingPreHitRelayPacketReplacement

open FangqingRelayAnalyticAssembly FangqingRelayStationarity FangqingRelayBlockGeometry
  FangqingPreHitRelayLocality FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section

set_option maxHeartbeats 2500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem updated_endpoint_family_germ (n : ℕ) (base : Fin (n + 1) → E → ℝ)
    (packet : Fin (n + 1)) (f g : E → ℝ) (z : Joint n E)
    (h : f =ᶠ[𝓝 (z (1, packet))] g) :
    ∀ t, Function.update base packet f t =ᶠ[𝓝 (z (1, t))] Function.update base packet g t := by
  intro t
  by_cases ht : t = packet
  · subst t
    simpa using h
  · simp only [Function.update_of_ne ht]
    exact Filter.Eventually.of_forall (fun _ => rfl)

theorem literal_full_reply_packet_replacement (n : ℕ) (beta lam a sigma reward : ℝ)
    (base0 base1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (gate : Fin n → E → ℝ) (packet : Fin (n + 1)) (f0 f1 g0 g1 : E → ℝ) (z : Joint n E)
    (h0 : f0 =ᶠ[𝓝 (z (1, packet))] g0)
    (h1 : (f1 =ᶠ[𝓝 (z (1, packet))] g1) ∨
      ((fun w : Joint n E => incoming n gate (fun t => w (2, t)) packet) =ᶠ[𝓝 z] (fun _ => 0))) :
    fullReply (assembled n beta lam a sigma reward (Function.update base0 packet f0)
      (Function.update base1 packet f1) m0 m1 gate) z =
    fullReply (assembled n beta lam a sigma reward (Function.update base0 packet g0)
      (Function.update base1 packet g1) m0 m1 gate) z := by
  apply fullReply_of_germ
  apply assembled_germ_from_weighted_endpoint_germs
  · exact updated_endpoint_family_germ n base0 packet f0 g0 z h0
  · intro t
    by_cases ht : t = packet
    · subst t
      simpa using h1
    · left
      simp only [Function.update_of_ne ht]
      exact Filter.Eventually.of_forall (fun _ => rfl)

theorem suppress_updated_own_gate (n : ℕ) (own : Fin n) (base : Fin n → E → ℝ) (privateGate : E → ℝ) :
    suppressOwnGate n own (Function.update base own privateGate) = suppressOwnGate n own base := by
  funext j u
  by_cases hj : j = own
  · subst j
    simp [suppressOwnGate]
  · simp only [suppressOwnGate, Function.update_of_ne hj]

theorem actual_relay_pre_hit_packet_prefix_reply (n : ℕ) (beta lam a sigma reward ell : ℝ)
    (base0 base1 : Fin (n + 1) → E → ℝ) (m0 m1 : Fin (n + 1) → ℝ)
    (baseGate : Fin n → E → ℝ) (own : Fin n) (packet : Fin (n + 1))
    (f0 f1 g0 g1 : E → ℝ) (privateCenter : E) (z : Joint n E)
    (ha : 0 < a) (hell : 0 < ell)
    (hout : 2 * (a * ell) ≤ ‖z (2, own.castSucc) - a • privateCenter‖)
    (h0 : f0 =ᶠ[𝓝 (z (1, packet))] g0)
    (h1 : (f1 =ᶠ[𝓝 (z (1, packet))] g1) ∨
      ((fun w : Joint n E => incoming n (suppressOwnGate n own baseGate) (fun t => w (2, t)) packet) =ᶠ[𝓝 z] (fun _ => 0))) :
    fullReply (assembled n beta lam a sigma reward (Function.update base0 packet f0)
      (Function.update base1 packet f1) m0 m1
      (Function.update baseGate own (scaledGate theta (a * ell) (a • privateCenter)))) z =
    fullReply (assembled n beta lam a sigma reward (Function.update base0 packet g0)
      (Function.update base1 packet g1) m0 m1 (suppressOwnGate n own baseGate)) z := by
  have hSuppress := actual_private_radial_gate_full_bundle_suppression n beta lam a sigma reward ell
    (Function.update base0 packet f0) (Function.update base1 packet f1) m0 m1
    (Function.update baseGate own (scaledGate theta (a * ell) (a • privateCenter))) own privateCenter z ha hell
    (by simp) hout
  rw [suppress_updated_own_gate] at hSuppress
  exact hSuppress.trans (literal_full_reply_packet_replacement n beta lam a sigma reward base0 base1 m0 m1
    (suppressOwnGate n own baseGate) packet f0 f1 g0 g1 z h0 h1)

end
end FangqingPreHitRelayPacketReplacement
end

section
-- Source component: ConditionalFrameFibers.lean

open MeasureTheory ProbabilityTheory

namespace FangqingConditionalFrameFibers

noncomputable section

set_option maxHeartbeats 2000000

variable {Side Frame : Type*} [mSide : MeasurableSpace Side] [mFrame : MeasurableSpace Frame]

theorem product_fiber_integral_is_conditional_expectation
    (sigma : Measure Side) (nu : Measure Frame) [IsProbabilityMeasure sigma] [IsProbabilityMeasure nu]
    (f : Side × Frame → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f (sigma.prod nu)) :
    (fun p : Side × Frame => ∫ v, f (p.1, v) ∂nu) =ᵐ[sigma.prod nu]
      (sigma.prod nu)[f | MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side)] := by
  let G := MeasurableSpace.comap (Prod.fst : Side × Frame → Side) (inferInstance : MeasurableSpace Side)
  let g : Side → ℝ := fun s => ∫ v, f (s, v) ∂nu
  have hle : G ≤ mSide.prod mFrame := (@measurable_fst Side Frame mSide mFrame).comap_le
  have hg : StronglyMeasurable g := hf.integral_prod_right'
  have hgi : Integrable g sigma := hfint.integral_prod_left
  have hgm : StronglyMeasurable[G] (fun p : Side × Frame => g p.1) :=
    hg.comp_measurable (comap_measurable Prod.fst)
  change (fun p : Side × Frame => g p.1) =ᵐ[sigma.prod nu] (sigma.prod nu)[f | G]
  refine ae_eq_condExp_of_forall_setIntegral_eq (m := G) (m₀ := mSide.prod mFrame)
    (μ := sigma.prod nu) (f := f) (g := fun p : Side × Frame => g p.1) hle hfint ?_ ?_ ?_
  · intro A hA hfinite
    exact (hgi.comp_fst nu).integrableOn
  · intro A hA hfinite
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    have hpre : MeasurableSet[mSide.prod mFrame] ((Prod.fst : Side × Frame → Side) ⁻¹' B) :=
      hB.preimage (@measurable_fst Side Frame mSide mFrame)
    rw [← integral_indicator hpre, ← integral_indicator hpre]
    have hl : ((Prod.fst : Side × Frame → Side) ⁻¹' B).indicator (fun p => g p.1) =
        fun p => (B.indicator g) p.1 := by
      funext p
      by_cases hp : p.1 ∈ B <;> simp [Set.indicator, hp]
    rw [hl, integral_fun_fst]
    simp only [measureReal_univ_eq_one, one_smul]
    rw [integral_prod _ (hfint.indicator hpre)]
    apply integral_congr_ae
    filter_upwards with s
    by_cases hs : s ∈ B
    · simp only [Set.indicator_of_mem hs]
      change g s = ∫ v, (((Prod.fst : Side × Frame → Side) ⁻¹' B).indicator f) (s, v) ∂nu
      simp only [Set.indicator_of_mem (show (s, _) ∈ (Prod.fst : Side × Frame → Side) ⁻¹' B from hs)]
      rfl
    · simp only [Set.indicator_of_notMem hs]
      have hz : (fun v => (((Prod.fst : Side × Frame → Side) ⁻¹' B).indicator f) (s, v)) = fun _ => 0 := by
        funext v
        exact Set.indicator_of_notMem (show (s, v) ∉ (Prod.fst : Side × Frame → Side) ⁻¹' B from hs) f
      rw [hz, integral_zero]
  · exact hgm.aestronglyMeasurable

theorem uniform_fiber_bound_gives_side_conditional_bound
    (sigma : Measure Side) (nu : Measure Frame) [IsProbabilityMeasure sigma] [IsProbabilityMeasure nu]
    (f : Side × Frame → ℝ) (hf : StronglyMeasurable f) (hfint : Integrable f (sigma.prod nu))
    (zeta : ℝ) (hbound : ∀ s, (∫ v, f (s, v) ∂nu) ≤ zeta) :
    ∀ᵐ p ∂sigma.prod nu,
      (sigma.prod nu)[f | MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace Side)] p ≤ zeta := by
  filter_upwards [product_fiber_integral_is_conditional_expectation sigma nu f hf hfint] with p hp
  rw [← hp]
  exact hbound p.1

end
end FangqingConditionalFrameFibers
end

section
-- Source component: ActivationPacketGerms.lean

open scoped Topology

namespace FangqingActivationPacketGerms

open FangqingAmplifier FangqingPacketLeakage OriginalPacketOrientationNormalization
  OriginalPhysicalPairedShellPrefix OriginalActualPairedPacketExecution
  FangqingPreHitPhysicalPacketGerms FangqingPrefixAdaptedModel

noncomputable section

set_option maxHeartbeats 2500000

variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_inactive_germ_no_selected_handle
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (q nu scale R gain : ℝ) (y : PhysicalSpace A0 B0 W)
    (hhandle : |inner ℝ h (C.symm y.fst.snd)| ≤ delta / 8)
    (htail : ∀ j, |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain =ᶠ[𝓝 y]
      publicEndpoint (QPhysical q nu C) R gain :=
  actual_inactive_germ_public_before_handle P delta omega hd hdw n (physicalFrame C h n tail)
    (QPhysical q nu C) scale R gain y (inactive_columns_small C h n tail y delta hhandle htail)

theorem actual_activation_germs_grant_handle_without_tail
    (P : FlatCubic.Profile) (delta omega : ℝ) (hd : 0 < delta) (hdw : delta ≤ omega)
    (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain A amplitude : ℝ) (y : PhysicalSpace A0 B0 W)
    (hhandle : |inner ℝ h (C.symm y.fst.snd)| ≤ delta / 8)
    (htail : ∀ j, |inner ℝ (tail j) y.snd| ≤ delta / 8) :
    (actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain =ᶠ[𝓝 y]
      actualInactive P delta omega n (physicalFrame C h n (0 : Fin (n + 2) → W)) (QPhysical q nu C) scale R gain) ∧
    (actualActive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain A amplitude (mkPhysical h 0 0) =ᶠ[𝓝 y]
      actualActive P delta omega n (physicalFrame C h n (0 : Fin (n + 2) → W)) (QPhysical q nu C) phi scale R gain A amplitude (mkPhysical h 0 0)) := by
  have hprefix : ∀ j : Fin (n + 3), j.val < 0 + 1 →
      physicalFrame C h n tail j = physicalFrame C h n (0 : Fin (n + 2) → W) j := by
    intro j hj
    have hj0 : j = 0 := by apply Fin.ext; simp only [Fin.val_zero]; omega
    subst j
    rfl
  have hs0 : ∀ j : Fin (n + 2), |inner ℝ ((0 : Fin (n + 2) → W) j) y.snd| ≤ delta / 8 := by
    intro j
    simp only [Pi.zero_apply, inner_zero_left, abs_zero]
    positivity
  exact actual_paired_germs_of_common_prefix P delta omega hd hdw n 0 (physicalFrame C h n tail)
    (physicalFrame C h n (0 : Fin (n + 2) → W)) (QPhysical q nu C) phi scale R gain A amplitude (mkPhysical h 0 0) y hprefix
    (fun j _ => inactive_columns_small C h n tail y delta hhandle htail j)
    (fun j _ => inactive_columns_small C h n (0 : Fin (n + 2) → W) y delta hhandle hs0 j)

end
end FangqingActivationPacketGerms
end

section
-- Source component: OrthonormalFrameRotation.lean

namespace OriginalOrthonormalFrameRotation

noncomputable section
set_option maxHeartbeats 1000000

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem exists_rotation_between_orthonormal_frames
    {m : ℕ} (v w : Fin m → W) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w) :
    ∃ V : W ≃ₗᵢ[ℝ] W, ∀ j, V (v j) = w j := by
  classical
  let s : Finset (Fin m) := Finset.univ
  let b0 := OrthonormalBasis.span hv s
  let b1 := OrthonormalBasis.span hw s
  let S0 := Submodule.span ℝ (s.image v : Set W)
  let S1 := Submodule.span ℝ (s.image w : Set W)
  let L : S0 →ₗᵢ[ℝ] W := S1.subtypeₗᵢ.comp (b0.equiv b1 (Equiv.refl _)).toLinearIsometry
  let T : W →ₗᵢ[ℝ] W := L.extend
  have hs : Function.Surjective T :=
    (LinearMap.injective_iff_surjective (f := T.toLinearMap)).mp T.injective
  refine ⟨LinearIsometryEquiv.ofSurjective T hs, ?_⟩
  intro j
  let j' : s := ⟨j, Finset.mem_univ j⟩
  have h0 : (b0 j' : W) = v j := OrthonormalBasis.span_apply hv s j'
  have h1 : (b1 j' : W) = w j := OrthonormalBasis.span_apply hw s j'
  change L.extend (v j) = w j
  rw [← h0, L.extend_apply]
  change ((b0.equiv b1 (Equiv.refl _) (b0 j')) : W) = w j
  rw [OrthonormalBasis.equiv_apply_basis]
  exact h1

end
end OriginalOrthonormalFrameRotation
end

section
-- Source component: PreHitShellNormalizers.lean

open scoped BigOperators Topology

namespace FangqingPreHitShellNormalizers

open FangqingAmplifier FangqingPacketLeakage FangqingLocalizedSeedJets FangqingPublicShellProfiles
  FangqingInactiveShellClass FangqingRadialGateBounds OriginalPacketOrientationNormalization
  OriginalPhysicalPairedShellPrefix FangqingPathEdgeRegularity

noncomputable section

set_option maxHeartbeats 2500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

theorem unit_vector_rotation (h0 h1 : A) (hh0 : ‖h0‖ = 1) (hh1 : ‖h1‖ = 1) :
    ∃ U : A ≃ₗᵢ[ℝ] A, U h0 = h1 := by
  have hv0 : Orthonormal ℝ (fun _ : Fin 1 => h0) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [ite_true, real_inner_self_eq_norm_sq, hh0, one_pow]
  have hv1 : Orthonormal ℝ (fun _ : Fin 1 => h1) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp only [ite_true, real_inner_self_eq_norm_sq, hh1, one_pow]
  obtain ⟨U, hU⟩ := OriginalOrthonormalFrameRotation.exists_rotation_between_orthonormal_frames
    (fun _ : Fin 1 => h0) (fun _ : Fin 1 => h1) hv0 hv1
  exact ⟨U, hU 0⟩

theorem actual_paired_shell_rotation
    (P : FlatCubic.Profile) (delta omega : ℝ) (n : ℕ) (C : A ≃ₗᵢ[ℝ] B)
    (U : A ≃ₗᵢ[ℝ] A) (V : W ≃ₗᵢ[ℝ] W) (h : A) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain width amplitude : ℝ) (z : PhysicalSpace A B W) :
    actualInactive P delta omega n (physicalFrame C (U h) n (fun j => V (tail j)))
      (QPhysical q nu C) scale R gain (rotation C U V z) =
      actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain z ∧
    actualActive P delta omega n (physicalFrame C (U h) n (fun j => V (tail j)))
      (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical (U h) 0 0) (rotation C U V z) =
      actualActive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h 0 0) z := by
  have hQ := actual_public_amplifier_invariant C U V q nu z
  have hd : pathDirection n (physicalFrame C (U h) n (fun j => V (tail j))) =
      fun i => rotation C U V (pathDirection n (physicalFrame C h n tail) i) :=
    funext (physicalPath_rotates C U V h n tail)
  have hh : mkPhysical (U h) (0 : B) (0 : W) = rotation C U V (mkPhysical h 0 0) := by simp [rotation_mk]
  have hg := actual_edgeSum_equivariant (rotation C U V) (FlatCubic.edge P delta omega)
    (pathDirection n (physicalFrame C h n tail)) z
  have hgate : scaledGate theta R 0 (rotation C U V z) = scaledGate theta R 0 z := by
    simp only [scaledGate, sub_zero, LinearIsometryEquiv.norm_map]
  have hcol : FangqingRadialCollar.collar psi R (rotation C U V z) = FangqingRadialCollar.collar psi R z := by
    simp only [FangqingRadialCollar.collar, LinearIsometryEquiv.norm_map]
  have hpath (v : Fin (n + 3) → PhysicalSpace A B W) (y : PhysicalSpace A B W) :
      pathEdge P delta omega (n + 2) v y = edgeSum (FlatCubic.edge P delta omega) (pathDirection n v) y := rfl
  have hI : actualInactive P delta omega n (physicalFrame C (U h) n (fun j => V (tail j)))
      (QPhysical q nu C) scale R gain (rotation C U V z) =
      actualInactive P delta omega n (physicalFrame C h n tail) (QPhysical q nu C) scale R gain z := by
    simp only [actualInactive, inactiveShell, hpath, hd, hg, hQ, hgate, hcol]
  refine ⟨hI, ?_⟩
  dsimp only [actualActive]
  rw [hI]
  unfold localizedSeed FangqingLinearProfileJetBounds.linearProfile
  rw [hh, (rotation C U V).inner_map_map, hgate]

theorem actual_paired_normalizers_are_frame_independent
    (P : FlatCubic.Profile) (delta omega : ℝ) (n : ℕ) (C : A ≃ₗᵢ[ℝ] B)
    (h0 h1 : A) (hh0 : ‖h0‖ = 1) (hh1 : ‖h1‖ = 1)
    (tail0 tail1 : Fin (n + 2) → W) (ht0 : Orthonormal ℝ tail0) (ht1 : Orthonormal ℝ tail1)
    (phi : ℝ → ℝ) (q nu scale R gain width amplitude : ℝ) :
    sInf (Set.range (actualInactive P delta omega n (physicalFrame C h0 n tail0) (QPhysical q nu C) scale R gain)) =
      sInf (Set.range (actualInactive P delta omega n (physicalFrame C h1 n tail1) (QPhysical q nu C) scale R gain)) ∧
    sInf (Set.range (actualActive P delta omega n (physicalFrame C h0 n tail0) (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h0 0 0))) =
      sInf (Set.range (actualActive P delta omega n (physicalFrame C h1 n tail1) (QPhysical q nu C) phi scale R gain width amplitude (mkPhysical h1 0 0))) := by
  obtain ⟨U, hU⟩ := unit_vector_rotation h0 h1 hh0 hh1
  obtain ⟨V, hV⟩ := OriginalOrthonormalFrameRotation.exists_rotation_between_orthonormal_frames tail0 tail1 ht0 ht1
  have htail : (fun j => V (tail0 j)) = tail1 := funext hV
  have he := actual_paired_shell_rotation P delta omega n C U V h0 tail0 phi q nu scale R gain width amplitude
  simp only [hU, htail] at he
  exact ⟨(congrArg sInf (range_of_rotation (rotation C U V) _ _ (fun z => (he z).1))).symm,
    (congrArg sInf (range_of_rotation (rotation C U V) _ _ (fun z => (he z).2))).symm⟩

theorem attained_minimum_equals_infimum {E : Type*} (H : E → ℝ) (z : E) (hz : ∀ y, H z ≤ H y) :
    H z = sInf (Set.range H) := by
  have hb : BddBelow (Set.range H) := ⟨H z, by rintro _ ⟨y, rfl⟩; exact hz y⟩
  symm
  apply le_antisymm
  · exact csInf_le hb ⟨z, rfl⟩
  · exact le_csInf ⟨H z, z, rfl⟩ (by rintro _ ⟨y, rfl⟩; exact hz y)

end
end FangqingPreHitShellNormalizers
end

section
-- Source component: CanonicalRelayParameterFamily.lean

open scoped BigOperators ContDiff

namespace FangqingCanonicalRelayParameterFamily

open FangqingAmplifier OriginalPhysicalPacketMinimizer OriginalPacketOrientationNormalization
  OriginalActualPhysicalEndpointOracleFamily FangqingCanonicalLateGateFamily
  FangqingRelayStationarity FangqingRelayAnalyticAssembly FangqingRelayBlockGeometry
  FangqingLocalizedSeedJets FangqingPublicShellProfiles FangqingRadialGateBounds
  FangqingRelayOracleParameterRegularity FangqingPreHitRelayLocality

noncomputable section

set_option maxHeartbeats 3500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

abbrev LocalParameters (A W : Type*) (nt : ℕ) := A × (Fin (nt + 2) → W)
abbrev Parameters (A W : Type*) (outer nt : ℕ) := Fin (outer + 1) → LocalParameters A W nt

def reducedZero {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (p : LocalParameters A W nt) : PhysicalSpace A B W → ℝ :=
  FangqingRelayFenchelInterfaces.reduced (H0 c C p.1 p.2) c.mu

def reducedOne {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (p : LocalParameters A W nt) : PhysicalSpace A B W → ℝ :=
  FangqingRelayFenchelInterfaces.reduced (H1 c C p.1 p.2) c.mu

def center {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) (p : LocalParameters A W nt) : PhysicalSpace A B W :=
  (-c.lam / c.beta) • Z c C p.1 p.2

def hZero {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) : Fin (outer + 1) → PhysicalSpace A B W → ℝ :=
  fun t => reducedZero c (C t) (p t)

def hOne {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) : Fin (outer + 1) → PhysicalSpace A B W → ℝ :=
  fun t => reducedOne c (C t) (p t)

def gates {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (p : Parameters A W outer nt) : Fin outer → PhysicalSpace A B W → ℝ :=
  fun j => scaledGate theta (c.a * c.ell) (c.a • center c (C j.castSucc) (p j.castSucc))

def family {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer + 1) → ℝ) (p : Parameters A W outer nt) : Joint outer (PhysicalSpace A B W) → ℝ :=
  assembled outer c.beta c.lam c.a c.sigma c.reward (hZero c C p) (hOne c C p) m0 m1 (gates c C p)

theorem reduced_zero_joint_regular {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) :
    ContDiff ℝ 2 (Function.uncurry (reducedZero (W := W) c C)) := by
  have hh := endpoint_zero_joint_contDiff (W := W) c.profile c.delta c.omega hd hdw nt C
    c.q (c.scale * c.barlam) c.scale c.R c.gain
  exact hh.sub (contDiff_const.mul (contDiff_snd.norm_sq ℝ))

theorem reduced_one_joint_regular {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    ContDiff ℝ 2 (Function.uncurry (reducedOne (W := W) c C)) := by
  have hh := endpoint_one_joint_contDiff (W := W) c.profile c.delta c.omega hd hdw nt C c.phi hp
    c.q (c.scale * c.barlam) c.scale c.R c.gain c.A (c.seed * c.A)
  exact hh.sub (contDiff_const.mul (contDiff_snd.norm_sq ℝ))

theorem coordinate_point_regular (nt : ℕ) (C : A ≃ₗᵢ[ℝ] B) (alpha : ℝ) (z : Fin (nt + 3) → ℝ) :
    ContDiff ℝ 2 (fun p : LocalParameters A W nt => coordinatePoint C p.1 nt p.2 alpha z) := by
  have ha : ContDiff ℝ 2 (fun p : LocalParameters A W nt => alpha • p.1) := contDiff_fst.const_smul alpha
  have hb : ContDiff ℝ 2 (fun p : LocalParameters A W nt => z 0 • C p.1) :=
    (C.contDiff.comp contDiff_fst).const_smul (z 0)
  have hw : ContDiff ℝ 2 (fun p : LocalParameters A W nt => ∑ j, z j.succ • p.2 j) := by
    apply ContDiff.sum
    intro j _
    exact ((contDiff_apply ℝ W j).comp contDiff_snd).const_smul (z j.succ)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (A × B)) W).symm.contDiff.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.contDiff.comp (ha.prodMk hb)).prodMk hw)

theorem private_center_regular {nt : ℕ} (c : Config nt) (C : A ≃ₗᵢ[ℝ] B) :
    ContDiff ℝ 2 (center (W := W) c C) :=
  (coordinate_point_regular nt C (publicPair c).1 (publicPair c).2).const_smul (-c.lam / c.beta)

theorem canonical_gate_joint_regular {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (j : Fin outer) :
    ContDiff ℝ 2 (fun p : Parameters A W outer nt × PhysicalSpace A B W => gates c C p.1 j p.2) := by
  have hc : ContDiff ℝ 2 (fun p : Parameters A W outer nt × PhysicalSpace A B W =>
      center c (C j.castSucc) (p.1 j.castSucc)) :=
    (private_center_regular (W := W) c (C j.castSucc)).comp
      ((contDiff_apply ℝ (LocalParameters A W nt) j.castSucc).comp contDiff_fst)
  exact (theta_smooth.of_le (by decide)).comp
    (((contDiff_snd.sub (hc.const_smul c.a)).norm_sq ℝ).div_const ((c.a * c.ell) ^ 2))

theorem zero_full_parameters_regular {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (t : Fin (outer + 1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) :
    ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => hZero c C z.1 t z.2) := by
  have hreg : ContDiff ℝ 2 (fun z : LocalParameters A W nt × PhysicalSpace A B W =>
      reducedZero c (C t) z.1 z.2) := reduced_zero_joint_regular (W := W) c (C t) hd hdw
  have hproj : ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => (z.1 t, z.2)) :=
    (((contDiff_apply ℝ (LocalParameters A W nt) t).comp
      (contDiff_fst : ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => z.1))).prodMk contDiff_snd)
  simpa only [hZero, Function.comp_def] using! hreg.comp hproj

theorem one_full_parameters_regular {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (t : Fin (outer + 1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => hOne c C z.1 t z.2) := by
  have hreg : ContDiff ℝ 2 (fun z : LocalParameters A W nt × PhysicalSpace A B W =>
      reducedOne c (C t) z.1 z.2) := reduced_one_joint_regular (W := W) c (C t) hd hdw hp
  have hproj : ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => (z.1 t, z.2)) :=
    (((contDiff_apply ℝ (LocalParameters A W nt) t).comp
      (contDiff_fst : ContDiff ℝ 2 (fun z : Parameters A W outer nt × PhysicalSpace A B W => z.1))).prodMk contDiff_snd)
  simpa only [hOne, Function.comp_def] using! hreg.comp hproj

theorem actual_full_family_parameter_regular {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    ContDiff ℝ 2 (Function.uncurry (family (W := W) c C m0 m1)) := by
  change ContDiff ℝ 2 (fun z : Parameters A W outer nt × Joint outer (PhysicalSpace A B W) =>
    assembled outer c.beta c.lam c.a c.sigma c.reward (hZero c C z.1) (hOne c C z.1) m0 m1 (gates c C z.1) z.2)
  apply assembled_parameter_regular (Parameter := Parameters A W outer nt) (E := PhysicalSpace A B W) outer c.beta c.lam c.a c.sigma c.reward (hZero c C) (hOne c C)
    (fun _ => m0) (fun _ => m1) (gates c C)
  · intro t
    exact zero_full_parameters_regular (W := W) c C t hd hdw
  · intro t
    exact one_full_parameters_regular (W := W) c C t hd hdw hp
  · intro t
    exact contDiff_const
  · intro t
    exact contDiff_const
  · intro j
    exact canonical_gate_joint_regular (W := W) c C j

theorem actual_full_oracle_parameter_continuous {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    Continuous (fun p : Parameters A W outer nt × Joint outer (PhysicalSpace A B W) =>
      fullReply (family c C m0 m1 p.1) p.2) := by
  exact FangqingContinuousOracleFamily.continuous_actual_oracle_family
    (family (W := W) c C m0 m1)
    (actual_full_family_parameter_regular (W := W) c C m0 m1 hd hdw hp)

end
end FangqingCanonicalRelayParameterFamily
end

section
-- Source component: CanonicalSuppressedRelay.lean

open scoped Topology ContDiff

namespace FangqingCanonicalSuppressedRelay

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingRelayAnalyticAssembly FangqingRelayStationarity FangqingRelayBlockGeometry
  FangqingPreHitRelayLocality FangqingPreHitRelayPacketReplacement FangqingPreHitGateGeometry
  FangqingPublicShellProfiles FangqingRadialGateBounds FangqingRelayOracleParameterRegularity

noncomputable section

set_option maxHeartbeats 3500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

def frameOverride {outer nt : ℕ} (p : Parameters A W outer nt) (packet : Fin (outer + 1))
    (v : LocalParameters A W nt) : Parameters A W outer nt := Function.update p packet v

def suppressForPacket {E : Type*} (outer : ℕ) (packet : Fin (outer + 1))
    (gate : Fin outer → E → ℝ) : Fin outer → E → ℝ :=
  fun j => if j.castSucc = packet then (fun _ => 0) else gate j

def suppressedFamily {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (p : Parameters A W outer nt) : Joint outer (PhysicalSpace A B W) → ℝ :=
  assembled outer c.beta c.lam c.a c.sigma c.reward (hZero c C p) (hOne c C p) m0 m1
    (suppressForPacket outer packet (gates c C p))

def realFamily {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (v : LocalParameters A W nt) : Joint outer (PhysicalSpace A B W) → ℝ :=
  FangqingCanonicalRelayParameterFamily.family c C m0 m1 (frameOverride side packet v)

def virtualFamily {outer nt : ℕ} (c : Config nt) (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B)
    (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (v : LocalParameters A W nt) : Joint outer (PhysicalSpace A B W) → ℝ :=
  suppressedFamily c C m0 m1 packet (frameOverride side packet v)

theorem suppressed_gates_ignore_own_frame {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (v : LocalParameters A W nt) :
    suppressForPacket outer packet (gates c C (frameOverride side packet v)) =
      suppressForPacket outer packet (gates c C side) := by
  funext j y
  by_cases hj : j.castSucc = packet
  · simp only [suppressForPacket, if_pos hj, Pi.zero_apply]
  · simp only [suppressForPacket, if_neg hj, gates, frameOverride, Function.update_of_ne hj]

theorem zero_array_override {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (v : LocalParameters A W nt) :
    hZero c C (frameOverride side packet v) = Function.update (hZero c C side) packet (reducedZero c (C packet) v) := by
  funext t y
  by_cases ht : t = packet
  · subst t
    simp [hZero, frameOverride]
  · simp only [hZero, frameOverride, Function.update_of_ne ht]

theorem one_array_override {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (v : LocalParameters A W nt) :
    hOne c C (frameOverride side packet v) = Function.update (hOne c C side) packet (reducedOne c (C packet) v) := by
  funext t y
  by_cases ht : t = packet
  · subst t
    simp [hOne, frameOverride]
  · simp only [hOne, frameOverride, Function.update_of_ne ht]

theorem actual_real_family_germ_equals_own_suppressed {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (packet : Fin (outer + 1)) (side : Parameters A W outer nt) (v : LocalParameters A W nt)
    (z : Joint outer (PhysicalSpace A B W)) (ha : 0 < c.a) (hell : 0 < c.ell)
    (hout : 2 * (c.a * c.ell) ≤ ‖z (2, packet) - c.a • center c (C packet) v‖) :
    realFamily c C m0 m1 packet side v =ᶠ[𝓝 z] virtualFamily c C m0 m1 packet side v := by
  apply assembled_germ_of_gate_germs
  intro j
  by_cases hj : j.castSucc = packet
  · have hg := gate_is_flat_outside_twice_radius (c.a * c.ell) (c.a • center c (C packet) v)
      (z (2, packet)) (mul_pos ha hell) hout
    simpa [gates, frameOverride, suppressForPacket, hj] using hg
  · apply Filter.Eventually.of_forall
    intro y
    simp only [suppressForPacket, if_neg hj]

theorem literal_full_relay_reply_from_packet_germs {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (packet : Fin (outer + 1)) (side : Parameters A W outer nt) (actual masked : LocalParameters A W nt)
    (z : Joint outer (PhysicalSpace A B W)) (ha : 0 < c.a) (hell : 0 < c.ell)
    (hout : 2 * (c.a * c.ell) ≤ ‖z (2, packet) - c.a • center c (C packet) actual‖)
    (h0 : reducedZero c (C packet) actual =ᶠ[𝓝 (z (1, packet))] reducedZero c (C packet) masked)
    (h1 : (reducedOne c (C packet) actual =ᶠ[𝓝 (z (1, packet))] reducedOne c (C packet) masked) ∨
      ((fun w : Joint outer (PhysicalSpace A B W) => incoming outer (suppressForPacket outer packet (gates c C side))
        (fun t => w (2, t)) packet) =ᶠ[𝓝 z] (fun _ => 0))) :
    fullReply (realFamily c C m0 m1 packet side actual) z =
      fullReply (virtualFamily c C m0 m1 packet side masked) z := by
  have hSuppress := fullReply_of_germ _ _ z
    (actual_real_family_germ_equals_own_suppressed c C m0 m1 packet side actual z ha hell hout)
  have hSwap := literal_full_reply_packet_replacement outer c.beta c.lam c.a c.sigma c.reward
    (hZero c C side) (hOne c C side) m0 m1 (suppressForPacket outer packet (gates c C side)) packet
    (reducedZero c (C packet) actual) (reducedOne c (C packet) actual)
    (reducedZero c (C packet) masked) (reducedOne c (C packet) masked) z h0 h1
  unfold virtualFamily suppressedFamily at hSuppress ⊢
  rw [suppressed_gates_ignore_own_frame, zero_array_override, one_array_override] at hSuppress
  rw [suppressed_gates_ignore_own_frame, zero_array_override, one_array_override]
  exact hSuppress.trans hSwap

theorem frame_override_regular {outer nt : ℕ} (packet : Fin (outer + 1)) :
    ContDiff ℝ 2 (fun p : Parameters A W outer nt × LocalParameters A W nt => frameOverride p.1 packet p.2) := by
  apply contDiff_pi.mpr
  intro t
  by_cases ht : t = packet
  · subst t
    simpa [frameOverride] using (contDiff_snd : ContDiff ℝ 2 (fun p : Parameters A W outer nt × LocalParameters A W nt => p.2))
  · simpa only [frameOverride, Function.update_of_ne ht, Function.comp_def] using!
      (contDiff_apply ℝ (LocalParameters A W nt) t).comp
        (contDiff_fst : ContDiff ℝ 2 (fun p : Parameters A W outer nt × LocalParameters A W nt => p.1))


theorem suppressed_family_parameter_regular {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (packet : Fin (outer + 1)) (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    ContDiff ℝ 2 (Function.uncurry (suppressedFamily (W := W) c C m0 m1 packet)) := by
  change ContDiff ℝ 2 (fun z : Parameters A W outer nt × Joint outer (PhysicalSpace A B W) =>
    assembled outer c.beta c.lam c.a c.sigma c.reward (hZero c C z.1) (hOne c C z.1) m0 m1
      (suppressForPacket outer packet (gates c C z.1)) z.2)
  apply assembled_parameter_regular (Parameter := Parameters A W outer nt) (E := PhysicalSpace A B W) outer c.beta c.lam c.a c.sigma c.reward (hZero c C) (hOne c C)
    (fun _ => m0) (fun _ => m1) (fun p => suppressForPacket outer packet (gates c C p))
  · intro t
    exact zero_full_parameters_regular (W := W) c C t hd hdw
  · intro t
    exact one_full_parameters_regular (W := W) c C t hd hdw hp
  · intro t
    exact contDiff_const
  · intro t
    exact contDiff_const
  · intro j
    by_cases hj : j.castSucc = packet
    · simpa only [suppressForPacket, if_pos hj] using
        (contDiff_const : ContDiff ℝ 2 (fun _ : Parameters A W outer nt × PhysicalSpace A B W => (0 : ℝ)))
    · simpa only [suppressForPacket, if_neg hj] using canonical_gate_joint_regular (W := W) c C j

theorem virtual_oracle_continuous {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (packet : Fin (outer + 1)) (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    Continuous (fun p : (Parameters A W outer nt × LocalParameters A W nt) × Joint outer (PhysicalSpace A B W) =>
      fullReply (virtualFamily c C m0 m1 packet p.1.1 p.1.2) p.2) := by
  have ho := FangqingContinuousOracleFamily.continuous_actual_oracle_family
    (suppressedFamily (W := W) c C m0 m1 packet) (suppressed_family_parameter_regular (W := W) c C m0 m1 packet hd hdw hp)
  have hm : Continuous (fun p : (Parameters A W outer nt × LocalParameters A W nt) × Joint outer (PhysicalSpace A B W) =>
      (frameOverride p.1.1 packet p.1.2, p.2)) :=
    ((frame_override_regular (A := A) (W := W) packet).continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def, virtualFamily, fullReply, FangqingShellPrefixLocality.bundle] using! ho.comp hm

theorem real_oracle_continuous {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ)
    (packet : Fin (outer + 1)) (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) :
    Continuous (fun p : (Parameters A W outer nt × LocalParameters A W nt) × Joint outer (PhysicalSpace A B W) =>
      fullReply (realFamily c C m0 m1 packet p.1.1 p.1.2) p.2) := by
  have ho := actual_full_oracle_parameter_continuous (W := W) c C m0 m1 hd hdw hp
  have hm : Continuous (fun p : (Parameters A W outer nt × LocalParameters A W nt) × Joint outer (PhysicalSpace A B W) =>
      (frameOverride p.1.1 packet p.1.2, p.2)) :=
    ((frame_override_regular (A := A) (W := W) packet).continuous.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def, realFamily] using! ho.comp hm

end
end FangqingCanonicalSuppressedRelay
end

section
-- Source component: ActualPaddedRelayReplies.lean

open scoped Topology
open MeasureTheory

namespace FangqingActualPaddedRelayReplies

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingRelayBlockGeometry FangqingPreHitRelayLocality
  OriginalTwoGroupPrefixExecution FangqingPrefixAdaptedModel

noncomputable section

set_option maxHeartbeats 3500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

abbrev Point (A B W : Type*) (outer : ℕ) := Joint outer (PhysicalSpace A B W)
abbrev Response (A B W : Type*) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [NormedAddCommGroup W] [InnerProductSpace ℝ W] (outer : ℕ) :=
  ℝ × Point A B W outer × (Point A B W outer →L[ℝ] Point A B W outer)
abbrev AugResponse (A B W : Type*) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (outer nt : ℕ) := Response A B W outer × Parameters A W outer nt × (Fin 1 → A) × (Fin (nt + 2) → W)

def initialCoefficient {nt : ℕ} (c : Config nt) {outer : ℕ} (i : Fin 3 × Fin (outer + 1)) : ℝ :=
  if i.2 = 0 then (if i.1 = 0 then -(c.seed / c.lam) else if i.1 = 2 then c.a * (-(c.seed / c.lam)) else 0) else 0

def publicInitialPoint {outer nt : ℕ} (c : Config nt) (handle : A) : Point A B W outer :=
  WithLp.toLp 2 (fun i => initialCoefficient c i • mkPhysical handle (0 : B) (0 : W))

def initialHandle {outer nt : ℕ} (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) : A :=
  (frameOverride side packet (handle 0, tail) 0).1

def publicRecord {outer nt : ℕ} (c : Config nt) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) : Response A B W outer :=
  (0, publicInitialPoint c (initialHandle packet side handle tail), 0)

def kernelReply {Seed : Type*} {outer nt : ℕ} (c : Config nt) (packet : Fin (outer + 1))
    (oracle : Parameters A W outer nt → LocalParameters A W nt → Point A B W outer → Response A B W outer) :
    Reply Seed (Parameters A W outer nt) A W (AugResponse A B W outer nt) (Point A B W outer) (nt + 2) :=
  fun n _ side _ kh kt handle tail z =>
    ((if n = 0 then publicRecord c packet side handle tail else oracle side (handle 0, tail) z),
      side, mask kh handle, mask kt tail)

def realReply {Seed : Type*} {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1)) :
    Reply Seed (Parameters A W outer nt) A W (AugResponse A B W outer nt) (Point A B W outer) (nt + 2) :=
  kernelReply c packet (fun side v z => fullReply (realFamily c C m0 m1 packet side v) z)

def virtualReply {Seed : Type*} {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1)) :
    Reply Seed (Parameters A W outer nt) A W (AugResponse A B W outer nt) (Point A B W outer) (nt + 2) :=
  kernelReply c packet (fun side v z => fullReply (virtualFamily c C m0 m1 packet side v) z)

def activation {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1)) :
    Activation (Parameters A W outer nt) (AugResponse A B W outer nt) (Point A B W outer) :=
  fun n side _ z => if n = 0 then decide (packet = 0) else
    Fin.cases true (fun j => decide (‖z (2, j.castSucc) - c.a • center c (C j.castSucc) (side j.castSucc)‖ <
      2 * (c.a * c.ell))) packet

def ownRelayHit {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (z : Point A B W outer) : Bool :=
  decide (‖z (2, packet) - c.a • center c (C packet) (handle 0, tail)‖ < 2 * (c.a * c.ell))

def packetOutputHit {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (z : Point A B W outer) : Bool :=
  decide (‖z (0, packet) - center c (C packet) (handle 0, tail)‖ < 2 * c.ell)

theorem embed_handle_continuous : Continuous (fun h : A => mkPhysical h (0 : B) (0 : W)) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (WithLp 2 (A × B)) W).symm.continuous.comp
    (((WithLp.prodContinuousLinearEquiv 2 ℝ A B).symm.continuous.comp
      (continuous_id.prodMk continuous_const)).prodMk continuous_const)

theorem publicInitialPoint_continuous {outer nt : ℕ} (c : Config nt) :
    Continuous (publicInitialPoint (A := A) (B := B) (W := W) (outer := outer) c) := by
  unfold publicInitialPoint
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin (outer + 1) => PhysicalSpace A B W)).comp
  apply continuous_pi
  intro i
  exact embed_handle_continuous.const_smul (initialCoefficient c i)

theorem public_initial_x {outer nt : ℕ} (c : Config nt) (handle : A) (t : Fin (outer + 1)) :
    publicInitialPoint (B := B) (W := W) c handle (0, t) =
      if t = 0 then (-(c.seed / c.lam)) • mkPhysical handle (0 : B) (0 : W) else 0 := by
  simp only [publicInitialPoint, PiLp.toLp_apply, initialCoefficient, ite_true]
  split_ifs <;> simp_all

theorem public_initial_y {outer nt : ℕ} (c : Config nt) (handle : A) (t : Fin (outer + 1)) :
    publicInitialPoint (B := B) (W := W) c handle (1, t) = 0 := by
  simp [publicInitialPoint, initialCoefficient]

theorem public_initial_s {outer nt : ℕ} (c : Config nt) (handle : A) (t : Fin (outer + 1)) :
    publicInitialPoint (B := B) (W := W) c handle (2, t) = c.a • publicInitialPoint (B := B) (W := W) c handle (0, t) := by
  rw [public_initial_x]
  simp only [publicInitialPoint, PiLp.toLp_apply, initialCoefficient]
  split_ifs <;> simp_all [mul_smul]

theorem real_paid_reply_is_literal_full_bundle {Seed : Type*} {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (n : ℕ) (hn : 0 < n) (seed : Seed) (side : Parameters A W outer nt) (st : State (AugResponse A B W outer nt))
    (kh kt : ℕ) (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (z : Point A B W outer) :
    (realReply c C m0 m1 packet n seed side st kh kt handle tail z).1 =
      fullReply (realFamily c C m0 m1 packet side (handle 0, tail)) z := by
  simp only [realReply, kernelReply, Nat.ne_of_gt hn, if_false]

theorem zero_slot_is_only_public_input {Seed : Type*} {outer nt : ℕ} (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (seed : Seed) (side : Parameters A W outer nt) (st : State (AugResponse A B W outer nt))
    (kh kt : ℕ) (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (z : Point A B W outer) :
    (realReply c C m0 m1 packet 0 seed side st kh kt handle tail z).1 = publicRecord c packet side handle tail := by
  simp [realReply, kernelReply]


section Measurability

variable {Seed : Type*} {outer nt : ℕ}
  [MeasurableSpace Seed] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology A] [SecondCountableTopology W]
  [MeasurableSpace (PhysicalSpace A B W)] [BorelSpace (PhysicalSpace A B W)]
  [SecondCountableTopology (PhysicalSpace A B W)]
  [MeasurableSpace (Point A B W outer)] [BorelSpace (Point A B W outer)]
  [MeasurableSpace (Point A B W outer →L[ℝ] Point A B W outer)]
  [BorelSpace (Point A B W outer →L[ℝ] Point A B W outer)]

abbrev PaddedReplyInput (Seed A B W : Type*) [NormedAddCommGroup A] [InnerProductSpace ℝ A]
    [NormedAddCommGroup B] [InnerProductSpace ℝ B] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    (outer nt : ℕ) :=
  Seed × Parameters A W outer nt × State (AugResponse A B W outer nt) × ℕ × ℕ ×
    (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer

theorem kernel_reply_measurable (c : Config nt) (packet : Fin (outer + 1))
    (oracle : Parameters A W outer nt → LocalParameters A W nt → Point A B W outer → Response A B W outer)
    (hOracle : Continuous (fun p : (Parameters A W outer nt × LocalParameters A W nt) × Point A B W outer =>
      oracle p.1.1 p.1.2 p.2)) (n : ℕ) :
    Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      kernelReply c packet oracle n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2) := by
  classical
  have hparam : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      (x.2.1, (x.2.2.2.2.2.1 0, x.2.2.2.2.2.2.1))) := by fun_prop
  have hparamq : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      ((x.2.1, (x.2.2.2.2.2.1 0, x.2.2.2.2.2.2.1)), x.2.2.2.2.2.2.2)) := by fun_prop
  have hctx : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      frameOverride x.2.1 packet (x.2.2.2.2.2.1 0, x.2.2.2.2.2.2.1)) :=
    (frame_override_regular (A := A) (W := W) packet).continuous.measurable.comp hparam
  have hhandle : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      (frameOverride x.2.1 packet (x.2.2.2.2.2.1 0, x.2.2.2.2.2.2.1) 0).1) :=
    measurable_fst.comp ((measurable_pi_apply 0).comp hctx)
  have hpublic : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      publicRecord (A := A) (B := B) (W := W) (outer := outer) c packet x.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1) := by
    exact measurable_const.prodMk (((publicInitialPoint_continuous (A := A) (B := B) (W := W) (outer := outer) c).measurable.comp hhandle).prodMk measurable_const)
  have hbody : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      if n = 0 then publicRecord (A := A) (B := B) (W := W) (outer := outer) c packet x.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 else
        oracle x.2.1 (x.2.2.2.2.2.1 0, x.2.2.2.2.2.2.1) x.2.2.2.2.2.2.2) := by
    by_cases hn : n = 0
    · simpa only [if_pos hn] using hpublic
    · simpa only [if_neg hn, Function.comp_def] using! hOracle.measurable.comp hparamq
  have hside : Measurable (fun x : PaddedReplyInput Seed A B W outer nt => x.2.1) := by fun_prop
  have hh : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      mask x.2.2.2.1 x.2.2.2.2.2.1) :=
    OriginalTwoGroupPrefixExecution.mask_measurable _ _ (by fun_prop) (by fun_prop)
  have ht : Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      mask x.2.2.2.2.1 x.2.2.2.2.2.2.1) :=
    OriginalTwoGroupPrefixExecution.mask_measurable _ _ (by fun_prop) (by fun_prop)
  exact hbody.prodMk (hside.prodMk (hh.prodMk ht))

theorem actual_real_reply_measurable (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) (n : ℕ) :
    Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      realReply c C m0 m1 packet n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2) :=
  kernel_reply_measurable c packet _ (real_oracle_continuous (W := W) c C m0 m1 packet hd hdw hp) n

theorem actual_virtual_reply_measurable (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hp : ContDiff ℝ 3 c.phi) (n : ℕ) :
    Measurable (fun x : PaddedReplyInput Seed A B W outer nt =>
      virtualReply c C m0 m1 packet n x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1
        x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 x.2.2.2.2.2.2.2) :=
  kernel_reply_measurable c packet _ (virtual_oracle_continuous (W := W) c C m0 m1 packet hd hdw hp) n


theorem activation_measurable (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1)) (n : ℕ) :
    Measurable (fun p : Parameters A W outer nt × State (AugResponse A B W outer nt) × Point A B W outer =>
      activation c C packet n p.1 p.2.1 p.2.2) := by
  classical
  by_cases hn : n = 0
  · simpa only [activation, if_pos hn] using measurable_const
  simp only [activation, if_neg hn]
  refine Fin.cases ?_ (fun j => ?_) packet
  · exact measurable_const
  · apply measurable_to_bool
    have hc : Measurable (fun p : Parameters A W outer nt × State (AugResponse A B W outer nt) × Point A B W outer =>
        ‖p.2.2 (2, j.castSucc) - c.a • center c (C j.castSucc) (p.1 j.castSucc)‖) := by
      have hctr := (private_center_regular (W := W) c (C j.castSucc)).continuous.measurable
      exact ((by fun_prop : Measurable (fun p : Parameters A W outer nt × State (AugResponse A B W outer nt) × Point A B W outer => p.2.2 (2,j.castSucc))).sub
        ((hctr.comp (by fun_prop)).const_smul c.a)).norm
    simpa only [Set.preimage, Set.mem_singleton_iff, Fin.cases_succ, decide_eq_true_eq] using
      (measurableSet_lt hc (measurable_const : Measurable (fun _ : Parameters A W outer nt × State (AugResponse A B W outer nt) × Point A B W outer => 2 * (c.a * c.ell))))

theorem ownRelayHit_measurable (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1)) :
    Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer =>
      ownRelayHit c C packet p.1 p.2.1 p.2.2) := by
  apply measurable_to_bool
  have hc : Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer =>
      ‖p.2.2 (2, packet) - c.a • center c (C packet) (p.1 0, p.2.1)‖) := by
    have hctr := (private_center_regular (W := W) c (C packet)).continuous.measurable
    exact ((by fun_prop : Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer => p.2.2 (2,packet))).sub
      ((hctr.comp (by fun_prop)).const_smul c.a)).norm
  simpa only [ownRelayHit, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (measurableSet_lt hc (measurable_const : Measurable (fun _ : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer => 2 * (c.a * c.ell))))

theorem packetOutputHit_measurable (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1)) :
    Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer =>
      packetOutputHit c C packet p.1 p.2.1 p.2.2) := by
  apply measurable_to_bool
  have hc : Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer =>
      ‖p.2.2 (0, packet) - center c (C packet) (p.1 0, p.2.1)‖) := by
    have hctr := (private_center_regular (W := W) c (C packet)).continuous.measurable
    exact ((by fun_prop : Measurable (fun p : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer => p.2.2 (0,packet))).sub
      (hctr.comp (by fun_prop))).norm
  simpa only [packetOutputHit, Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (measurableSet_lt hc (measurable_const : Measurable (fun _ : (Fin 1 → A) × (Fin (nt + 2) → W) × Point A B W outer => 2 * c.ell)))

end Measurability

end
end FangqingActualPaddedRelayReplies
end

section
-- Source component: PaddedPublicInputProgram.lean

namespace FangqingPaddedPublicInputProgram

open OriginalTwoGroupPrefixExecution

set_option maxHeartbeats 2500000

variable {Seed Side H W Public Q R A : Type*} {m : ℕ} [Zero H] [Zero W] [Zero A] [Zero R]

abbrev PublicQuery (Seed Public R Q : Type*) := ℕ → Seed → Public → (ℕ → R) → Q

def ordinaryRun (q : PublicQuery Seed Public R Q) (oracle : Q → R) (seed : Seed) (publicInput : Public) : ℕ → (ℕ → R)
  | 0 => 0
  | n + 1 =>
    let hist := ordinaryRun q oracle seed publicInput n
    Function.update hist n (oracle (q n seed publicInput hist))

def paidHistory (view : A → R) (hist : History A) : ℕ → R := fun n => view (hist (n + 1))

def paddedQuery (query : PublicQuery Seed Public R Q) (decode : A → Public) (view : A → R) (dummy : Q) : Query Seed A Q :=
  fun n seed hist => if n = 0 then dummy else query (n - 1) seed (decode (hist 0)) (paidHistory view hist)

def paddedOutput (out : Seed → Public → (ℕ → R) → Q) (decode : A → Public) (view : A → R) : Seed → History A → Q :=
  fun seed hist => out seed (decode (hist 0)) (paidHistory view hist)

theorem paidHistory_update (view : A → R) (hist : History A) (n : ℕ) (answer : A) :
    paidHistory view (Function.update hist (n + 1) answer) = Function.update (paidHistory view hist) n (view answer) := by
  funext j
  by_cases hj : j = n
  · subst j
    simp [paidHistory]
  · have hjs : j + 1 ≠ n + 1 := by omega
    simp only [paidHistory, Function.update_of_ne hjs, Function.update_of_ne hj]

theorem zero_cost_public_input_embedding
    (query : PublicQuery Seed Public R Q) (oracle : Q → R) (decode : A → Public) (view : A → R) (dummy : Q)
    (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W) (publicInput : Public)
    (hview0 : view (0 : A) = 0)
    (hpublic : ∀ st kh kt point, decode (reply 0 seed side st kh kt handle tail point) = publicInput)
    (hpaid : ∀ n, 0 < n → ∀ st kh kt point,
      view (reply n seed side st kh kt handle tail point) = oracle point) :
    ∀ N : ℕ,
      let st := fullRun (paddedQuery query decode view dummy) dec reply (N + 1) seed side handle tail
      decode (st.2.2 0) = publicInput ∧ paidHistory view st.2.2 = ordinaryRun query oracle seed publicInput N := by
  intro N
  induction N with
  | zero =>
      constructor
      · simp only [fullRun, fullStep, paddedQuery, if_pos rfl, Function.update_self]
        exact hpublic _ _ _ _
      · funext j
        simp only [paidHistory, fullRun, fullStep, ordinaryRun,
          Function.update_of_ne (by omega : j + 1 ≠ 0), Pi.zero_apply, hview0]
  | succ N ih =>
      let st := fullRun (paddedQuery query decode view dummy) dec reply (N + 1) seed side handle tail
      let chosen := query N seed publicInput (ordinaryRun query oracle seed publicInput N)
      have hquery : paddedQuery query decode view dummy (N + 1) seed st.2.2 = chosen := by
        simp only [paddedQuery, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
        rw [ih.1, ih.2]
      let kh := nextHandle dec (N + 1) side st chosen
      let kt := nextTail (m := m) st
      let answer := reply (N + 1) seed side st kh kt handle tail chosen
      have hstep : (fullRun (paddedQuery query decode view dummy) dec reply (N + 1 + 1) seed side handle tail).2.2 =
          Function.update st.2.2 (N + 1) answer := by
        change Function.update st.2.2 (N + 1) _ = _
        rw [hquery]
      constructor
      · rw [hstep, Function.update_of_ne (by omega : 0 ≠ N + 1)]
        exact ih.1
      · rw [hstep, paidHistory_update, ih.2]
        change Function.update (ordinaryRun query oracle seed publicInput N) N (view answer) = _
        rw [hpaid (N + 1) (by omega) st kh kt chosen]
        rfl

theorem original_output_equals_padded_output
    (query : PublicQuery Seed Public R Q) (oracle : Q → R) (out : Seed → Public → (ℕ → R) → Q)
    (decode : A → Public) (view : A → R) (dummy : Q)
    (dec : Activation Side A Q) (reply : Reply Seed Side H W A Q m)
    (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → W) (publicInput : Public)
    (hview0 : view (0 : A) = 0)
    (hpublic : ∀ st kh kt point, decode (reply 0 seed side st kh kt handle tail point) = publicInput)
    (hpaid : ∀ n, 0 < n → ∀ st kh kt point,
      view (reply n seed side st kh kt handle tail point) = oracle point) (N : ℕ) :
    paddedOutput out decode view seed
      (fullRun (paddedQuery query decode view dummy) dec reply (N + 1) seed side handle tail).2.2 =
        out seed publicInput (ordinaryRun query oracle seed publicInput N) := by
  obtain ⟨h0, hh⟩ := zero_cost_public_input_embedding query oracle decode view dummy dec reply seed side handle tail
    publicInput hview0 hpublic hpaid N
  unfold paddedOutput
  rw [h0, hh]

end FangqingPaddedPublicInputProgram
end

section
-- Source component: PaddedPublicInputMeasurability.lean

open MeasureTheory

namespace FangqingPaddedPublicInputProgram

variable {Seed Public Aug R Q : Type*}
  [MeasurableSpace Seed] [MeasurableSpace Public] [MeasurableSpace Aug]
  [MeasurableSpace R] [MeasurableSpace Q]

theorem paidHistory_measurable (view : Aug → R) (hv : Measurable view) :
    Measurable (paidHistory view) := by
  apply measurable_pi_lambda
  intro n
  exact hv.comp (measurable_pi_apply (n+1))

theorem paddedQuery_measurable (q : PublicQuery Seed Public R Q)
    (hq : ∀ n, Measurable (fun p : Seed × Public × (ℕ → R) => q n p.1 p.2.1 p.2.2))
    (decode : Aug → Public) (hd : Measurable decode) (view : Aug → R) (hv : Measurable view)
    (dummy : Q) (n : ℕ) :
    Measurable (fun p : Seed × (ℕ → Aug) => paddedQuery q decode view dummy n p.1 p.2) := by
  by_cases hn : n = 0
  · simpa only [paddedQuery, if_pos hn] using measurable_const
  · simpa only [paddedQuery, if_neg hn, Function.comp_def] using
      (hq (n-1)).comp (measurable_fst.prodMk
        ((hd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
          ((paidHistory_measurable view hv).comp measurable_snd)))

theorem paddedOutput_measurable (out : Seed → Public → (ℕ → R) → Q)
    (ho : Measurable (fun p : Seed × Public × (ℕ → R) => out p.1 p.2.1 p.2.2))
    (decode : Aug → Public) (hd : Measurable decode) (view : Aug → R) (hv : Measurable view) :
    Measurable (fun p : Seed × (ℕ → Aug) => paddedOutput out decode view p.1 p.2) := by
  exact ho.comp (measurable_fst.prodMk
    ((hd.comp ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      ((paidHistory_measurable view hv).comp measurable_snd)))

end FangqingPaddedPublicInputProgram
end

section
-- Source component: PhysicalPairedShellOuterPublic.lean

open scoped Topology BigOperators

namespace OriginalPhysicalPairedShellPrefix
open FangqingPacketLeakage FangqingShellPrefixLocality
open FangqingInactiveShellClass FangqingLocalizedSeedJets FangqingPublicShellProfiles
open FangqingAmplifier OriginalPacketOrientationNormalization FangqingPathEdgeRegularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem actual_cutoff_eventually_zero_outer (R : ℝ) (hR : 0 < R) (y : E) (hout : 2 * R < ‖y‖) :
    (FangqingRadialGateBounds.scaledGate theta R (0 : E)) =ᶠ[𝓝 y] (fun _ => 0) := by
  have hn : {z : E | 2 * R < ‖z‖} ∈ 𝓝 y := (isOpen_lt continuous_const continuous_norm).mem_nhds hout
  filter_upwards [hn] with z hz
  have hr : (2 : ℝ) < ‖z‖ / R := (lt_div_iff₀ hR).mpr (by nlinarith only [hz])
  have hs : (49 / 16 : ℝ) ≤ ‖z‖ ^ 2 / R ^ 2 := by
    rw [← div_pow]
    nlinarith only [hr]
  simpa only [FangqingRadialGateBounds.scaledGate, sub_zero] using theta_zero _ hs

theorem actual_paired_eventually_public_outer
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (hR : 0 < R) (handle y : E)
    (hout : 2 * R < ‖y‖) :
    actualInactive P delta Delta n v Q scale R gain =ᶠ[𝓝 y] publicEndpoint Q R gain ∧
      actualActive P delta Delta n v Q phi scale R gain A amplitude handle =ᶠ[𝓝 y] publicEndpoint Q R gain := by
  have he := actual_cutoff_eventually_zero_outer R hR y hout
  constructor
  · filter_upwards [he] with z hz
    simp only [actualInactive, inactiveShell, hz, zero_mul, add_zero, publicEndpoint]
  · filter_upwards [he] with z hz
    simp only [actualActive, actualInactive, inactiveShell, localizedSeed, hz, zero_mul, mul_zero, add_zero, sub_zero, publicEndpoint]

theorem actual_paired_full_bundle_public_outer
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ) (v : Fin (n + 3) → E)
    (Q : E → ℝ) (phi : ℝ → ℝ) (scale R gain A amplitude : ℝ) (hR : 0 < R) (handle y : E)
    (hout : 2 * R < ‖y‖) :
    bundle (actualInactive P delta Delta n v Q scale R gain) y = bundle (publicEndpoint Q R gain) y ∧
      bundle (actualActive P delta Delta n v Q phi scale R gain A amplitude handle) y = bundle (publicEndpoint Q R gain) y := by
  have he := actual_paired_eventually_public_outer P delta Delta n v Q phi scale R gain A amplitude hR handle y hout
  exact ⟨bundle_of_eventuallyEq _ _ y he.1, bundle_of_eventuallyEq _ _ y he.2⟩

section Physical
variable {A0 B0 W : Type*}
  [NormedAddCommGroup A0] [InnerProductSpace ℝ A0] [CompleteSpace A0]
  [NormedAddCommGroup B0] [InnerProductSpace ℝ B0] [CompleteSpace B0]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

theorem actual_physical_paired_outer_full_bundle_public
    (P : FlatCubic.Profile) (delta Delta : ℝ) (n : ℕ) (C : A0 ≃ₗᵢ[ℝ] B0) (h : A0) (tail : Fin (n + 2) → W)
    (phi : ℝ → ℝ) (q nu scale R gain A amplitude : ℝ) (hR : 0 < R) (y : PhysicalSpace A0 B0 W)
    (hout : 2 * R < ‖y‖) :
    let v := physicalFrame C h n tail
    let Q := QPhysical q nu C
    let H0 := inactiveShell Q (fun z => scale * pathEdge P delta Delta (n + 2) v z) R gain
    let H1 := fun z => H0 z - localizedSeed theta phi R A amplitude (mkPhysical h (0 : B0) (0 : W)) z
    bundle H0 y = bundle (publicEndpoint Q R gain) y ∧ bundle H1 y = bundle (publicEndpoint Q R gain) y :=
  actual_paired_full_bundle_public_outer P delta Delta n (physicalFrame C h n tail) (QPhysical q nu C) phi scale R gain A amplitude
    hR (mkPhysical h (0 : B0) (0 : W)) y hout

end Physical
end OriginalPhysicalPairedShellPrefix
end

section
-- Source component: ActualPaddedRelayLocalReplay.lean

open scoped Topology

namespace FangqingActualPaddedRelayLocalReplay

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingCanonicalSuppressedRelay FangqingActualPaddedRelayReplies FangqingRelayBlockGeometry
  FangqingPreHitRelayLocality FangqingPreHitPhysicalPacketGerms FangqingActivationPacketGerms
  OriginalTwoGroupPrefixExecution FangqingPrefixAdaptedModel OriginalPacketOrientationNormalization
  OriginalPhysicalPairedShellPrefix FangqingRelayStationarity
  FangqingRelayFenchelInterfaces FangqingPublicShellProfiles FangqingRadialGateBounds

noncomputable section
set_option maxHeartbeats 3500000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

variable {Seed : Type*} {outer nt : ℕ}


theorem next_tail_when_unactivated {R : Type*} {m : ℕ}
    (st : State R) (hzero : st.1 = 0) : nextTail (m := m) st = st.2.1 := by
  simp only [nextTail, tailDecision, hzero, lt_self_iff_false, decide_false,
    OriginalPrefixOracleReplay.advance, Bool.false_eq_true, and_false, if_false]

theorem next_tail_when_activated {R : Type*} {m : ℕ}
    (st : State R) (hone : st.1 = 1) (ht : st.2.1 ≤ m) :
    nextTail (m := m) st = min (st.2.1 + 1) m := by
  simp only [nextTail, tailDecision, hone, Nat.zero_lt_one, decide_true,
    OriginalPrefixOracleReplay.advance, and_true]
  split_ifs with hlt
  · exact (min_eq_left (by omega)).symm
  · have he : st.2.1 = m := by omega
    omega

theorem mask_idempotent {E : Type*} [Zero E] {m : ℕ} (k : ℕ) (v : Fin m → E) :
    mask k (mask k v) = mask k v := by
  funext j
  by_cases hj : j.val < k <;> simp [mask, hj]

theorem incoming_germ_zero_of_inactive_decision (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer + 1))
    (side : Parameters A W outer nt) (st : State (AugResponse A B W outer nt))
    (n : ℕ) (hn : 0 < n) (z : Point A B W outer) (ha : 0 < c.a) (he : 0 < c.ell)
    (hdec : activation c C packet n side st z = false) :
    (fun w : Point A B W outer => incoming outer (suppressForPacket outer packet (gates c C side))
      (fun t => w (2,t)) packet) =ᶠ[𝓝 z] (fun _ => 0) := by
  revert hdec
  refine Fin.cases ?_ (fun j => ?_) packet
  · intro hdec
    simp [activation, Nat.ne_of_gt hn] at hdec
  · intro hdec
    have hout : 2 * (c.a * c.ell) ≤
        ‖z (2,j.castSucc) - c.a • center c (C j.castSucc) (side j.castSucc)‖ := by
      simpa only [activation, Nat.ne_of_gt hn, if_false, Fin.cases_succ, decide_eq_false_iff_not,
        not_lt] using hdec
    apply incoming_private_gate_germ_zero_before_activation outer
      (suppressForPacket outer j.succ (gates c C side)) j c.a c.ell
      (center c (C j.castSucc) (side j.castSucc)) z ha he _ hout
    have hj : j.castSucc ≠ j.succ := by intro h; have hv := congrArg Fin.val h; simp only [Fin.val_castSucc, Fin.val_succ] at hv; omega
    simp only [suppressForPacket, if_neg hj, gates]

theorem actual_endpoint_germs_under_prefix_state (c : Config nt)
    (C : A ≃ₗᵢ[ℝ] B) (st : State (AugResponse A B W outer nt))
    (kh : ℕ) (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (y : PhysicalSpace A B W)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hR : 0 < c.R)
    (hb : st.1 ≤ 1) (hbt : st.2.1 ≤ nt + 2) (hkh : kh ≤ 1) (hmono : st.1 ≤ kh)
    (hzero : st.1 = 0 → st.2.1 = 0)
    (hgood : ‖y‖ ≤ 2 * c.R →
      (st.1 = 0 → |inner ℝ (handle 0) (C.symm y.fst.snd)| ≤ c.delta / 8) ∧
      (∀ j, st.2.1 ≤ j.val → |inner ℝ (tail j) y.snd| ≤ c.delta / 8)) :
    let kt := nextTail (m := nt + 2) st
    (reducedZero c C (handle 0,tail) =ᶠ[𝓝 y]
      reducedZero c C (mask kh handle 0,mask kt tail)) ∧
    (kh ≠ 0 → reducedOne c C (handle 0,tail) =ᶠ[𝓝 y]
      reducedOne c C (mask kh handle 0,mask kt tail)) := by
  intro kt
  have reduce0 {h h' : A} {v v' : Fin (nt + 2) → W}
      (hh : H0 c C h v =ᶠ[𝓝 y] H0 c C h' v') :
      reducedZero c C (h,v) =ᶠ[𝓝 y] reducedZero c C (h',v') :=
    subtract_public_quadratic_preserves_germ _ _ c.mu y hh
  have reduce1 {h h' : A} {v v' : Fin (nt + 2) → W}
      (hh : H1 c C h v =ᶠ[𝓝 y] H1 c C h' v') :
      reducedOne c C (h,v) =ᶠ[𝓝 y] reducedOne c C (h',v') :=
    subtract_public_quadratic_preserves_germ _ _ c.mu y hh
  by_cases hout : 2 * c.R < ‖y‖
  · have hf := actual_paired_eventually_public_outer c.profile c.delta c.omega nt (physicalFrame C (handle 0) nt tail)
      (QPhysical c.q (c.scale*c.barlam) C) c.phi c.scale c.R c.gain c.A (c.seed*c.A) hR (mkPhysical (handle 0) 0 0) y hout
    have hm := actual_paired_eventually_public_outer c.profile c.delta c.omega nt (physicalFrame C (mask kh handle 0) nt (mask kt tail))
      (QPhysical c.q (c.scale*c.barlam) C) c.phi c.scale c.R c.gain c.A (c.seed*c.A) hR (mkPhysical (mask kh handle 0) 0 0) y hout
    exact ⟨reduce0 (hf.1.trans hm.1.symm), fun _ => reduce1 (hf.2.trans hm.2.symm)⟩
  have hg := hgood (le_of_not_gt hout)
  by_cases hk0 : kh = 0
  · have hs0 : st.1 = 0 := by omega
    have ht0 : kt = 0 := (next_tail_when_unactivated st hs0).trans (hzero hs0)
    have hf := actual_inactive_germ_no_selected_handle c.profile c.delta c.omega hd hdw nt C (handle 0) tail
      c.q (c.scale*c.barlam) c.scale c.R c.gain y (hg.1 hs0) (fun j => hg.2 j (by rw [hzero hs0]; omega))
    have hm := actual_inactive_germ_no_selected_handle c.profile c.delta c.omega hd hdw nt C (mask kh handle 0) (mask kt tail)
      c.q (c.scale*c.barlam) c.scale c.R c.gain y (by simp [mask, hk0]; positivity)
      (by intro j; simp [mask, ht0]; positivity)
    exact ⟨reduce0 (hf.trans hm.symm), fun h => (h hk0).elim⟩
  · have hk1 : kh = 1 := by omega
    have hh : mask kh handle 0 = handle 0 := by simp [mask,hk1]
    have hp : st.1 = 0 ∨ st.1 = 1 := by omega
    have hgerm : (H0 c C (handle 0) tail =ᶠ[𝓝 y] H0 c C (handle 0) (mask kt tail)) ∧
        (H1 c C (handle 0) tail =ᶠ[𝓝 y] H1 c C (handle 0) (mask kt tail)) := by
      rcases hp with hp | hp
      · have ht0 : kt = 0 := (next_tail_when_unactivated st hp).trans (hzero hp)
        have hf := actual_activation_germs_grant_handle_without_tail c.profile c.delta c.omega hd hdw nt C (handle 0) tail
          c.phi c.q (c.scale*c.barlam) c.scale c.R c.gain c.A (c.seed*c.A) y (hg.1 hp)
          (fun j => hg.2 j (by rw [hzero hp]; omega))
        have hmask0 : mask kt tail = 0 := by funext j; simp [mask, ht0]
        simpa only [hmask0, FangqingCanonicalLateGateFamily.H0, FangqingCanonicalLateGateFamily.H1, actualInactive, actualActive] using! hf
      · have hkt : kt = min (st.2.1+1) (nt+2) := next_tail_when_activated st hp hbt
        have hf := actual_physical_paired_germs_after_one_boundary c.profile c.delta c.omega hd hdw nt st.2.1 C (handle 0) tail
          c.phi c.q (c.scale*c.barlam) c.scale c.R c.gain c.A (c.seed*c.A) y hg.2
        simpa only [hkt, FangqingCanonicalLateGateFamily.H0, FangqingCanonicalLateGateFamily.H1, actualInactive, actualActive] using! hf
    rw [hh]
    exact ⟨reduce0 hgerm.1, fun _ => reduce1 hgerm.2⟩


theorem actual_zero_slot_equals_virtual_masked_record (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (seed : Seed) (side : Parameters A W outer nt) (st : State (AugResponse A B W outer nt))
    (handle : Fin 1 → A) (tail : Fin (nt + 2) → W) (z : Point A B W outer) (hb : st.1 ≤ 1) :
    let kh := nextHandle (activation c C packet) 0 side st z
    let kt := nextTail (m := nt+2) st
    realReply c C m0 m1 packet 0 seed side st kh kt handle tail z =
      virtualReply c C m0 m1 packet 0 seed side st kh kt (mask kh handle) (mask kt tail) z := by
  intro kh kt
  have hi : initialHandle packet side handle tail = initialHandle packet side (mask kh handle) (mask kt tail) := by
    by_cases hp : packet = 0
    · subst packet
      have hk : kh = 1 := by
        simp only [kh, nextHandle, activation, if_true, decide_true, OriginalPrefixOracleReplay.advance, and_true]
        split_ifs <;> omega
      simp [initialHandle, frameOverride, mask, hk]
    · simp only [initialHandle, frameOverride, Function.update_of_ne (Ne.symm hp)]
  simp only [realReply, virtualReply, kernelReply, if_true, publicRecord, hi,
    mask_idempotent]

theorem actual_paid_reply_equals_virtual_prefix_reply (c : Config nt)
    (C : Fin (outer + 1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer + 1) → ℝ) (packet : Fin (outer + 1))
    (n : ℕ) (hn : 0 < n) (seed : Seed) (side : Parameters A W outer nt)
    (st : State (AugResponse A B W outer nt)) (handle : Fin 1 → A) (tail : Fin (nt+2) → W)
    (z : Point A B W outer) (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hR : 0 < c.R)
    (ha : 0 < c.a) (he : 0 < c.ell) (hb : st.1 ≤ 1) (hbt : st.2.1 ≤ nt+2)
    (hzero : st.1 = 0 → st.2.1 = 0)
    (hNoHit : ownRelayHit c C packet handle tail z = false)
    (hgood : ‖z (1,packet)‖ ≤ 2*c.R →
      (st.1 = 0 → |inner ℝ (handle 0) ((C packet).symm (z (1,packet)).fst.snd)| ≤ c.delta/8) ∧
      (∀ j, st.2.1 ≤ j.val → |inner ℝ (tail j) (z (1,packet)).snd| ≤ c.delta/8)) :
    let kh := nextHandle (activation c C packet) n side st z
    let kt := nextTail (m := nt+2) st
    realReply c C m0 m1 packet n seed side st kh kt handle tail z =
      virtualReply c C m0 m1 packet n seed side st kh kt (mask kh handle) (mask kt tail) z := by
  intro kh kt
  have hmono : st.1 ≤ kh := (OriginalPrefixOracleReplay.advance_bounds 1 st.1 (activation c C packet n side st z)).1
  have hkh : kh ≤ 1 := by
    dsimp [kh,nextHandle,OriginalPrefixOracleReplay.advance]
    split_ifs <;> omega
  have hg := actual_endpoint_germs_under_prefix_state c (C packet) st kh handle tail (z (1,packet))
    hd hdw hR hb hbt hkh hmono hzero hgood
  have hout : 2 * (c.a*c.ell) ≤ ‖z (2,packet) - c.a • center c (C packet) (handle 0,tail)‖ := by
    simpa only [ownRelayHit, decide_eq_false_iff_not, not_lt] using hNoHit
  have h1 : (reducedOne c (C packet) (handle 0,tail) =ᶠ[𝓝 (z (1,packet))]
      reducedOne c (C packet) (mask kh handle 0,mask kt tail)) ∨
      ((fun w : Point A B W outer => incoming outer (suppressForPacket outer packet (gates c C side))
        (fun t => w (2,t)) packet) =ᶠ[𝓝 z] (fun _ => 0)) := by
    by_cases hk0 : kh = 0
    · right
      have hpre : st.1 = 0 := by omega
      have hdec : activation c C packet n side st z = false := by
        by_contra h
        have ht : activation c C packet n side st z = true := by simpa using h
        have hx : kh = 1 := by simp [kh,nextHandle,OriginalPrefixOracleReplay.advance,hpre,ht]
        omega
      exact incoming_germ_zero_of_inactive_decision c C packet side st n hn z ha he hdec
    · exact Or.inl (hg.2 hk0)
  have hreply := literal_full_relay_reply_from_packet_germs c C m0 m1 packet side (handle 0,tail)
    (mask kh handle 0,mask kt tail) z ha he hout hg.1 h1
  simpa only [realReply,virtualReply,kernelReply,Nat.ne_of_gt hn,if_false,mask_idempotent] using
    congrArg (fun ans => (ans,side,mask kh handle,mask kt tail)) hreply


theorem unactivated_run_has_zero_tail
    {H T Q R Seed Side : Type*} [Zero H] [Zero T] [Zero R] {m : ℕ}
    (query : Query Seed R Q) (dec : Activation Side R Q) (r : Reply Seed Side H T R Q m)
    (N : ℕ) (seed : Seed) (side : Side) (handle : Fin 1 → H) (tail : Fin m → T)
    (hzero : (run query dec r N seed side handle tail).1 = 0) :
    (run query dec r N seed side handle tail).2.1 = 0 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hb := count_step_bounds query dec r N seed side handle tail
      have hp : (run query dec r N seed side handle tail).1 = 0 := by omega
      have ht := ih hp
      change OriginalPrefixOracleReplay.advance m _ (tailDecision _) = 0
      simp only [tailDecision, hp, lt_self_iff_false, decide_false,
        OriginalPrefixOracleReplay.advance, Bool.false_eq_true, and_false, if_false, ht]

theorem actual_full_relay_stopped_replay (c : Config nt)
    (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (m0 m1 : Fin (outer+1) → ℝ) (packet : Fin (outer+1))
    (query : Query Seed (AugResponse A B W outer nt) (Point A B W outer))
    (out : Seed → History (AugResponse A B W outer nt) → Point A B W outer)
    (N : ℕ) (seed : Seed) (side : Parameters A W outer nt) (handle : Fin 1 → A) (tail : Fin (nt+2) → W)
    (hd : 0 < c.delta) (hdw : c.delta ≤ c.omega) (hR : 0 < c.R) (ha : 0 < c.a) (he : 0 < c.ell)
    (hgood : ∀ n < N,
      let st := run query (activation c C packet) (virtualReply c C m0 m1 packet) n seed side handle tail
      let z := query n seed st.2.2
      ‖z (1,packet)‖ ≤ 2*c.R →
        (st.1 = 0 → |inner ℝ (handle 0) ((C packet).symm (z (1,packet)).fst.snd)| ≤ c.delta/8) ∧
        (∀ j, st.2.1 ≤ j.val → |inner ℝ (tail j) (z (1,packet)).snd| ≤ c.delta/8)) :
    let vhit := fun n => ownRelayHit c C packet handle tail
      (query n seed (run query (activation c C packet) (virtualReply c C m0 m1 packet) n seed side handle tail).2.2)
    let stop := OriginalPrefixOracleReplay.firstHitUntil N vhit
    (∀ n ≤ stop, fullRun query (activation c C packet) (realReply c C m0 m1 packet) n seed side handle tail =
      run query (activation c C packet) (virtualReply c C m0 m1 packet) n seed side handle tail) ∧
    OriginalPrefixOracleReplay.firstHitUntil N (fun n => ownRelayHit c C packet handle tail
      (query n seed (fullRun query (activation c C packet) (realReply c C m0 m1 packet) n seed side handle tail).2.2)) = stop ∧
    (stop = N → out seed (fullRun query (activation c C packet) (realReply c C m0 m1 packet) N seed side handle tail).2.2 =
      out seed (run query (activation c C packet) (virtualReply c C m0 m1 packet) N seed side handle tail).2.2) := by
  apply FangqingStoppedTwoGroupReplay.literal_replay_stopped_at_virtual_first_hit
  intro n hn
  dsimp only
  intro hhit
  have hcounts := counts_bounded query (activation c C packet) (virtualReply c C m0 m1 packet) n seed side handle tail
  by_cases hn0 : n = 0
  · subst n
    exact actual_zero_slot_equals_virtual_masked_record c C m0 m1 packet seed side _ handle tail _ hcounts.1
  · exact actual_paid_reply_equals_virtual_prefix_reply c C m0 m1 packet n (Nat.pos_of_ne_zero hn0)
      seed side _ handle tail _ hd hdw hR ha he hcounts.1 hcounts.2
      (unactivated_run_has_zero_tail query (activation c C packet) (virtualReply c C m0 m1 packet) n seed side handle tail)
      hhit (hgood n hn)

end
end FangqingActualPaddedRelayLocalReplay
end

section
-- Source component: ActualRelayCandidates.lean

open MeasureTheory

namespace FangqingActualRelayCandidates

open FangqingAmplifier FangqingCanonicalLateGateFamily FangqingCanonicalRelayParameterFamily
  FangqingActualPaddedRelayReplies FangqingCanonicalSuppressedRelay FangqingRelayBlockGeometry
  FangqingPreHitGateGeometry OriginalPacketOrientationNormalization OriginalPacketDistanceGapBounds

noncomputable section
set_option maxHeartbeats 3000000

variable {A B W : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace A] [BorelSpace A] [Nontrivial A]
  [MeasurableSpace W] [BorelSpace W] [Nontrivial W]
  {outer nt : ℕ}

def mappedPacketPoint (c : Config nt) (packet : Fin (outer+1)) (j : Fin 3)
    (z : Point A B W outer) : PhysicalSpace A B W :=
  if j = 0 then z (1,packet) else if j = 1 then (-c.beta/c.lam) • z (0,packet)
    else (-c.beta/(c.a*c.lam)) • z (2,packet)

def handleComponent (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer+1)) (j : Fin 3)
    (z : Point A B W outer) : A := if j = 0 then (C packet).symm (z (1,packet)).fst.snd else 0

def tailComponent (c : Config nt) (packet : Fin (outer+1)) (j : Fin 3)
    (z : Point A B W outer) : W := (mappedPacketPoint c packet j z).snd

theorem mappedPacketPoint_continuous (c : Config nt) (packet : Fin (outer+1)) (j : Fin 3) :
    Continuous (mappedPacketPoint (A:=A) (B:=B) (W:=W) c packet j) := by
  unfold mappedPacketPoint
  split_ifs
  · exact (FangqingRelayBlockGeometry.coord outer 1 packet).continuous
  · exact (FangqingRelayBlockGeometry.coord (E := PhysicalSpace A B W) outer 0 packet).continuous.const_smul (-c.beta/c.lam)
  · simpa only using! (FangqingRelayBlockGeometry.coord (E := PhysicalSpace A B W) outer 2 packet).continuous.const_smul (-c.beta/(c.a*c.lam))

theorem handleComponent_continuous (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer+1)) (j : Fin 3) :
    Continuous (handleComponent (W:=W) C packet j) := by
  unfold handleComponent
  split_ifs
  · have hc : Continuous (fun y : PhysicalSpace A B W => (C packet).symm y.fst.snd) := by fun_prop
    exact hc.comp (FangqingRelayBlockGeometry.coord outer 1 packet).continuous
  · exact continuous_const

theorem tailComponent_continuous (c : Config nt) (packet : Fin (outer+1)) (j : Fin 3) :
    Continuous (tailComponent (A:=A) (B:=B) (W:=W) c packet j) :=
  (by fun_prop : Continuous (fun y : PhysicalSpace A B W => y.snd)).comp
    (mappedPacketPoint_continuous c packet j)

theorem dual_components_bounded_by_packet_norm
    (C : A ≃ₗᵢ[ℝ] B) (y : PhysicalSpace A B W) :
    ‖C.symm y.fst.snd‖ ≤ ‖y‖ ∧ ‖y.snd‖ ≤ ‖y‖ := by
  constructor
  · rw [C.symm.norm_map]
    exact (WithLp.norm_snd_le A y.fst).trans (WithLp.norm_fst_le (WithLp 2 (A × B)) y)
  · exact WithLp.norm_snd_le (WithLp 2 (A × B)) y

theorem clipped_dual_projection_good (c : Config nt)
    (C : Fin (outer+1) → A ≃ₗᵢ[ℝ] B) (packet : Fin (outer+1))
    (handle : A) (tail : Fin (nt+2) → W) (z : Point A B W outer) (Rclip : ℝ)
    (hR : 2*c.R ≤ Rclip) (hy : ‖z (1,packet)‖ ≤ 2*c.R)
    (hhandle : |inner ℝ handle (OriginalPrefixOracleHaarBridge.zeroClip Rclip (handleComponent C packet 0 z))| ≤ c.delta/8)
    (k : ℕ) (htail : ∀ j, k ≤ j.val →
      |inner ℝ (tail j) (OriginalPrefixOracleHaarBridge.zeroClip Rclip (tailComponent c packet 0 z))| ≤ c.delta/8) :
    |inner ℝ handle ((C packet).symm (z (1,packet)).fst.snd)| ≤ c.delta/8 ∧
      ∀ j, k ≤ j.val → |inner ℝ (tail j) (z (1,packet)).snd| ≤ c.delta/8 := by
  have hb := dual_components_bounded_by_packet_norm (C packet) (z (1,packet))
  have hh : handleComponent C packet 0 z = (C packet).symm (z (1,packet)).fst.snd := by simp [handleComponent]
  have ht : tailComponent c packet 0 z = (z (1,packet)).snd := by simp [tailComponent,mappedPacketPoint]
  rw [hh,OriginalPrefixOracleHaarBridge.zeroClip_eq Rclip _ (hb.1.trans (hy.trans hR))] at hhandle
  refine ⟨hhandle,?_⟩
  intro j hj
  have h := htail j hj
  rwa [ht,OriginalPrefixOracleHaarBridge.zeroClip_eq Rclip _ (hb.2.trans (hy.trans hR))] at h


theorem early_distance_from_clipped_tail_projection
    (C : A ≃ₗᵢ[ℝ] B) (h : A) (hh : ‖h‖ = 1)
    (q k : ℕ) (tail : Fin (nt+2) → W) (hv : Orthonormal ℝ tail)
    (hq : 8 ≤ q) (hfit : q ≤ nt+2) (hk : k ≤ q/8)
    (delta omega Cmin Rclip : ℝ) (hd : 0 ≤ delta) (hdw : delta ≤ omega) (hw : 0 < omega)
    (Z w : PhysicalSpace A B W) (hZ : ‖Z‖ ≤ Cmin * distanceScale q omega)
    (hclip : (Cmin+3) * distanceScale q omega ≤ Rclip)
    (hbulk : ∀ j : Fin (nt+3), (j.val : ℝ) ≤ q →
      3 * (q : ℝ) * omega ≤ inner ℝ (physicalFrame C h nt tail j) Z)
    (hsmall : ∀ j, k ≤ j.val → |inner ℝ (tail j) (OriginalPrefixOracleHaarBridge.zeroClip Rclip w.snd)| ≤ delta/8) :
    2 * distanceScale q omega < ‖Z-w‖ := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hD : 0 < distanceScale q omega := by unfold distanceScale; positivity
  by_cases hout : Rclip < ‖w‖
  · have hnorm := norm_sub_norm_le w Z
    rw [norm_sub_rev] at hnorm
    nlinarith only [hclip,hZ,hout,hnorm,hD]
  have hwsnd : ‖w.snd‖ ≤ Rclip := (WithLp.norm_snd_le (WithLp 2 (A × B)) w).trans (le_of_not_gt hout)
  have hunclip := OriginalPrefixOracleHaarBridge.zeroClip_eq Rclip w.snd hwsnd
  let J := OriginalPacketBulkIndexing.unrevealedFirstTail nt q (k+1) hfit
  have hidx := OriginalPacketBulkIndexing.actual_unrevealed_index_properties nt q (k+1) hfit (by omega : k+1 ≤ q/2)
  have hcard := early_unrevealed_card nt q (k+1) hfit hq (by omega)
  have hs : ∀ j ∈ J, |inner ℝ (physicalFrame C h nt tail j) w| ≤ omega/4 := by
    intro j hj
    have hjk := (hidx.1 j hj).2
    refine Fin.cases ?_ (fun i hi => ?_) j hjk
    · intro hj0
      simp only [Fin.val_zero] at hj0
      omega
    · rw [OriginalActualPairedPacketExecution.physical_tail_inner]
      have hi' : k ≤ i.val := by simp only [Fin.val_succ] at hi; omega
      have hh := hsmall i hi'
      rw [hunclip] at hh
      linarith only [hh,hdw,hd]
  have hsep := early_distance_from_unrevealed_coefficients (physicalFrame C h nt tail)
    (OriginalPhysicalPacketMinimizer.physicalFrame_orthonormal C h hh nt tail hv) J Z w q omega
    (by exact_mod_cast (show 1 ≤ q by omega)) hw.le hcard
    (fun j hj => hbulk j (hidx.1 j hj).1) hs
  linarith only [hsep,hD]

theorem fenchel_distance_identity (beta lam : ℝ) (hb : 0 < beta) (hl : 0 < lam)
    (Z x : PhysicalSpace A B W) :
    ‖Z - (-beta/lam) • x‖ = (beta/lam) * ‖x - (-lam/beta) • Z‖ := by
  have hc : (beta/lam) * (-lam/beta) = -1 := by field_simp <;> ring
  have he : Z - (-beta/lam) • x = (beta/lam) • (x - (-lam/beta) • Z) := by
    rw [smul_sub,smul_smul,hc,neg_one_smul,sub_neg_eq_add]
    rw [neg_div,neg_smul,sub_neg_eq_add]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hb hl)]

theorem relay_distance_identity (beta lam a : ℝ) (hb : 0 < beta) (hl : 0 < lam) (ha : 0 < a)
    (Z s : PhysicalSpace A B W) :
    ‖Z - (-beta/(a*lam)) • s‖ = (beta/(a*lam)) * ‖s - a • ((-lam/beta) • Z)‖ := by
  have hc : (beta/(a*lam)) * a * (-lam/beta) = -1 := by field_simp <;> ring
  have he : Z - (-beta/(a*lam)) • s = (beta/(a*lam)) • (s - a • ((-lam/beta) • Z)) := by
    rw [smul_sub,smul_smul,smul_smul,hc,neg_one_smul,sub_neg_eq_add]
    rw [neg_div,neg_smul,sub_neg_eq_add]
    abel
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hb (mul_pos ha hl))]

end
end FangqingActualRelayCandidates
end
