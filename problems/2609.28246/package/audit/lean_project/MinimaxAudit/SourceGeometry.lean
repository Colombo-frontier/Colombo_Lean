import MinimaxAudit.HardPotential
import MinimaxAudit.SourceRecurrence
import MinimaxAudit.Chain
import MinimaxAudit.ChainExtra
import MinimaxAudit.StrongSaddle

/-! Actual scalar-hard-instance residual geometry, with the displayed chain
coordinates derived from its actual signed gradient. -/

namespace MinimaxAudit

section Source
variable {n dx dy : ℕ} {U : Fin (n + 1) → Primal dx} {V : Fin (n + 1) → Dual dy}
variable (hU : Orthonormal ℝ U) (hV : Orthonormal ℝ V)

noncomputable def sourceANat (z : SaddleSpace dx dy) (j : ℕ) : ℝ :=
  if hj : j < n + 1 then pairedA U V ⟨j, hj⟩ z else 0

noncomputable def sourceADelta (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if hk : k < n then
      pairedA U V (⟨k, hk⟩ : Fin n).succ (sourceTransport hU hV profile tau q c z) -
        q * pairedA U V (⟨k, hk⟩ : Fin n).castSucc z
    else 0

@[simp] theorem sourceANat_fin (z : SaddleSpace dx dy) (i : Fin (n + 1)) :
    sourceANat (U := U) (V := V) z i.val = pairedA U V i z := by
  simp [sourceANat, i.isLt]

/-- The numerical gated error is exactly an actual normalized signed-gradient
coordinate. This supplies the analytic bridge absent from the scalar chain lemma. -/
theorem source_gatedError_eq (profile : GateProfile) (tau q c : ℝ)
    (z : SaddleSpace dx dy) (i : Fin (n + 1)) :
    gatedError q c (sourceANat (U := U) (V := V) z)
      (sourceADelta hU hV profile tau q c z) i.val =
      pairedA U V i (z - sourceTransport hU hV profile tau q c z) := by
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    simp [gatedError, idealError, sourceADelta, sourceANat, map_sub,
      sourceTransport_a_seed hU hV]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hklt : k < n := by omega
    let j : Fin n := ⟨k, hklt⟩
    have hieq : i = j.succ := Fin.ext hk
    subst i
    simp [gatedError, idealError, sourceADelta, sourceANat, j, hklt,
      show k < n + 1 by omega, map_sub]

/-- Every actual gate perturbation obeys the scalar telescoping budget. -/
theorem sourceADelta_bound (profile : GateProfile) {tau q : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c : ℝ)
    (z : SaddleSpace dx dy) :
    ∀ j ∈ Finset.range (n + 1), |sourceADelta hU hV profile tau q c z j| ≤ tau := by
  intro j hj
  cases j with
  | zero => simpa [sourceADelta] using htau.le
  | succ k =>
    have hk : k < n := by simpa using hj
    simpa [sourceADelta, hk] using
      (sourceTransport_a_step_error hU hV profile htau hq0 c z ⟨k, hk⟩).trans
        (mul_le_of_le_one_left htau.le hq1)

/-- The actual normalized residual has the claimed chain-length obstruction. -/
theorem source_normalized_residual_lower (profile : GateProfile) {tau q : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (c rho : ℝ)
    (z : SaddleSpace dx dy) (hr : |pairedA U V (Fin.last n) z| ≤ rho) :
    (q ^ n * c - rho - (n + 1 : ℝ) * tau) / Real.sqrt (n + 1) ≤
      ‖z - sourceTransport hU hV profile tau q c z‖ := by
  have h := gated_chain_residual_lower q c rho tau hq0 hq1
    (sourceANat (U := U) (V := V) z) (sourceADelta hU hV profile tau q c z) n
    (by
      change |sourceANat (U := U) (V := V) z (Fin.last n).val| ≤ rho
      rw [sourceANat_fin]
      exact hr) (sourceADelta_bound hU hV profile htau hq0 hq1 c z)
  apply h.trans
  rw [Finset.sum_range]
  simp_rw [source_gatedError_eq hU hV profile tau q c z]
  apply Real.sqrt_le_iff.mpr
  refine ⟨norm_nonneg _, ?_⟩
  have hplus : Orthonormal ℝ (pairedPlus U V) :=
    (paired_frame_orthonormal hU hV).comp Sum.inl Sum.inl_injective
  have hb := hplus.sum_inner_products_le
    (z - sourceTransport hU hV profile tau q c z) (s := Finset.univ)
  simpa [pairedA, innerSL_apply_apply, Real.norm_eq_abs, sq_abs] using hb

/-- Actual full signed scalar gradient version of the gated residual bound. -/
theorem source_scalar_residual_lower (profile : GateProfile) {tau q lam : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hlam : 0 ≤ lam) (c rho : ℝ)
    (z : SaddleSpace dx dy) (hr : |pairedA U V (Fin.last n) z| ≤ rho) :
    lam * ((q ^ n * c - rho - (n + 1 : ℝ) * tau) / Real.sqrt (n + 1)) ≤
      ‖scalarSaddleOperator (minimaxHardPotential profile tau lam q c hU hV) z‖ := by
  change _ ≤ ‖euclideanSaddleSign dx dy (gradient (minimaxHardPotential profile tau lam q c hU hV) z)‖
  rw [minimaxHardPotential_saddle_operator profile htau.ne' lam q c hU hV z,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_left
    (source_normalized_residual_lower hU hV profile htau hq0 hq1 c rho z hr) hlam

/-- A single approximate shift increases the absolute coordinate by at most τ. -/
theorem approximate_shift_abs_bound {a b q tau : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (htau : 0 ≤ tau)
    (herror : |a - q * b| ≤ q * tau) : |a| ≤ |b| + tau := by
  have htri : |a| ≤ |a - q * b| + |q * b| := by
    have h := abs_add_le (a - q * b) (q * b)
    simpa using h
  rw [abs_mul, abs_of_nonneg hq0] at htri
  have h1 := mul_le_of_le_one_left (abs_nonneg b) hq1
  have h2 := mul_le_of_le_one_left htau hq1
  linarith

/-- The actual fixed-point a-coordinates obey the forward chain bound. -/
theorem source_fixed_a_bound (profile : GateProfile) {tau q c : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z)
    (i : Fin (n + 1)) : |pairedA U V i z| ≤ c + (i.val : ℝ) * tau := by
  induction i using Fin.induction with
  | zero =>
    have hseed := sourceTransport_a_seed hU hV profile tau q c z
    rw [hfix] at hseed
    simp [hseed, abs_of_nonneg hc]
  | succ i ih =>
    have herror := sourceTransport_a_step_error hU hV profile htau hq0 c z i
    rw [hfix] at herror
    have hstep := approximate_shift_abs_bound hq0 hq1 htau.le herror
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
    linarith

/-- The actual b-coordinates obey the reverse chain bound, including the
middle terminal H-gate step. -/
theorem source_fixed_b_bound (profile : GateProfile) {tau q c : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z)
    (i : Fin (n + 1)) :
    |pairedB U V i z| ≤ c + (2 * (n : ℝ) + 1 - (i.val : ℝ)) * tau := by
  refine Fin.reverseInduction ?_ (fun j ih => ?_) i
  · have ha := source_fixed_a_bound hU hV profile htau hq0 hq1 hc z hfix (Fin.last n)
    have herror := sourceTransport_b_terminal_error hU hV profile htau hq0 c z
    rw [hfix] at herror
    have hstep := approximate_shift_abs_bound hq0 hq1 htau.le herror
    simp only [Fin.val_last] at ha ⊢
    nlinarith
  · have herror := sourceTransport_b_step_error hU hV profile htau hq0 c z j
    rw [hfix] at herror
    have hstep := approximate_shift_abs_bound hq0 hq1 htau.le herror
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] at ih ⊢
    nlinarith

/-- Uniform coordinate bounds at the actual fixed point, with the manuscript
safe bound c+2(n+1)τ. -/
theorem source_fixed_coordinate_bounds (profile : GateProfile) {tau q c : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z)
    (i : Fin (n + 1)) :
    |pairedA U V i z| ≤ c + 2 * (n + 1 : ℝ) * tau ∧
      |pairedB U V i z| ≤ c + 2 * (n + 1 : ℝ) * tau := by
  have ha := source_fixed_a_bound hU hV profile htau hq0 hq1 hc z hfix i
  have hb := source_fixed_b_bound hU hV profile htau hq0 hq1 hc z hfix i
  have hi : (i.val : ℝ) ≤ n := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hzero : (0 : ℝ) ≤ i.val := by positivity
  constructor <;> nlinarith

/-- The actual ambient fixed point has no hidden inactive contribution to its
norm: its transport expression is an isometric synthesis. All active entries
are bounded by the preceding concrete a/b recurrences. -/
theorem source_fixed_norm_bound (profile : GateProfile) {tau q c : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hc : 0 ≤ c)
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z) :
    ‖z‖ ≤ Real.sqrt (2 * (n + 1 : ℝ)) * (c + 2 * (n + 1 : ℝ) * tau) := by
  let g := chainBlockGradient profile tau q c (Fin.last n)
    (frameAnalysis (blockPairedFrame_orthonormal hU hV) z)
  let M := c + 2 * (n + 1 : ℝ) * tau
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hg (j : Fin (n + 1) × Fin 2) : |g j| ≤ M := by
    obtain ⟨i, k⟩ := j
    have hk : k = 0 ∨ k = 1 := by omega
    rcases hk with rfl | rfl
    · have h := pairedB_signed_synthesis hU hV g i
      change pairedB U V i (sourceTransport hU hV profile tau q c z) = g (i, 0) at h
      rw [hfix] at h
      rw [← h]
      exact (source_fixed_coordinate_bounds hU hV profile htau hq0 hq1 hc z hfix i).2
    · have h := pairedA_signed_synthesis hU hV g (finRotate (n + 1) i)
      simp only [Equiv.symm_apply_apply] at h
      change pairedA U V (finRotate (n + 1) i) (sourceTransport hU hV profile tau q c z) = g (i, 1) at h
      rw [hfix] at h
      rw [← h]
      exact (source_fixed_coordinate_bounds hU hV profile htau hq0 hq1 hc z hfix (finRotate (n + 1) i)).1
  have hsq : ‖g‖ ^ 2 ≤ (2 * (n + 1 : ℝ)) * M ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin (n + 1) × Fin 2, M ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have h := hg j
        simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (2 * (n + 1 : ℝ)) * M ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
        ring
  have hnorm : ‖z‖ = ‖g‖ := by
    rw [← hfix]
    simp only [sourceTransport, LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
    rfl
  rw [hnorm]
  have hroot := Real.sq_sqrt (show 0 ≤ 2 * (n + 1 : ℝ) by positivity)
  have hnonneg := norm_nonneg g
  have hprodnonneg : 0 ≤ Real.sqrt (2 * (n + 1 : ℝ)) * M := by positivity
  nlinarith

/-- An actual zero of the signed scalar gradient is the concrete transport
fixed point, provided the amplitude is positive. -/
theorem source_zero_is_fixed (profile : GateProfile) {tau lam q c : ℝ}
    (htau : tau ≠ 0) (hlam : 0 < lam) (z : SaddleSpace dx dy)
    (hzero : scalarSaddleOperator (minimaxHardPotential profile tau lam q c hU hV) z = 0) :
    sourceTransport hU hV profile tau q c z = z := by
  change euclideanSaddleSign dx dy (gradient (minimaxHardPotential profile tau lam q c hU hV) z) = 0 at hzero
  rw [minimaxHardPotential_saddle_operator profile htau lam q c hU hV z] at hzero
  have hsub : z - sourceTransport hU hV profile tau q c z = 0 :=
    (smul_eq_zero.mp hzero).resolve_left (ne_of_gt hlam)
  exact (sub_eq_zero.mp hsub).symm

/-- The manuscript parameters place the actual fixed point inside radius R/8. -/
theorem source_fixed_inner_radius (profile : GateProfile) {tau q c R : ℝ}
    (htau : 0 < tau) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hR : 0 < R)
    (hc : c = geometryKappa * R / Real.sqrt (n + 1))
    (ht : tau = geometryEta * c / (n + 1 : ℝ))
    (z : SaddleSpace dx dy) (hfix : sourceTransport hU hV profile tau q c z = z) :
    ‖z‖ ≤ R / 8 := by
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hs : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.mpr hN
  have hc0 : 0 ≤ c := by rw [hc]; unfold geometryKappa; positivity
  have hM : 0 ≤ c + 2 * (n + 1 : ℝ) * tau := by positivity
  have hroot : Real.sqrt (2 * (n + 1 : ℝ)) ≤ 2 * Real.sqrt (n + 1 : ℝ) := by
    have h1 := Real.sq_sqrt (show 0 ≤ 2 * (n + 1 : ℝ) by positivity)
    have h2 := Real.sq_sqrt hN.le
    nlinarith [Real.sqrt_nonneg (2 * (n + 1 : ℝ)), Real.sqrt_nonneg (n + 1 : ℝ)]
  have hMcal : c + 2 * (n + 1 : ℝ) * tau = c * (1 + 2 * geometryEta) := by
    rw [ht]
    field_simp [ne_of_gt hN]
  have hcroot : Real.sqrt (n + 1 : ℝ) * c = geometryKappa * R := by
    rw [hc]
    field_simp [ne_of_gt hs]
  calc
    ‖z‖ ≤ Real.sqrt (2 * (n + 1 : ℝ)) * (c + 2 * (n + 1 : ℝ) * tau) :=
      source_fixed_norm_bound hU hV profile htau hq0 hq1 hc0 z hfix
    _ ≤ (2 * Real.sqrt (n + 1 : ℝ)) * (c + 2 * (n + 1 : ℝ) * tau) :=
      mul_le_mul_of_nonneg_right hroot hM
    _ = 2 * (Real.sqrt (n + 1 : ℝ) * c) * (1 + 2 * geometryEta) := by rw [hMcal]; ring
    _ = 2 * geometryKappa * R * (1 + 2 * geometryEta) := by rw [hcroot]; ring
    _ ≤ R / 8 := by norm_num [geometryKappa, geometryEta]; linarith

/-- Actual saddle zero, not an assumed auxiliary vector, lies in the inner ball. -/
theorem source_zero_inner_radius (profile : GateProfile) {tau lam q c R : ℝ}
    (htau : 0 < tau) (hlam : 0 < lam) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hR : 0 < R)
    (hc : c = geometryKappa * R / Real.sqrt (n + 1))
    (ht : tau = geometryEta * c / (n + 1 : ℝ))
    (z : SaddleSpace dx dy)
    (hzero : scalarSaddleOperator (minimaxHardPotential profile tau lam q c hU hV) z = 0) :
    ‖z‖ ≤ R / 8 :=
  source_fixed_inner_radius hU hV profile htau hq0 hq1 hR hc ht z
    (source_zero_is_fixed hU hV profile htau.ne' hlam z hzero)

/-- The concrete balanced chain gives the manuscript's half-seed residual scale. -/
theorem source_balanced_scalar_residual (profile : GateProfile) {tau lam c : ℝ}
    (htau : 0 < tau) (hlam : 0 ≤ lam) (hc : 0 ≤ c)
    (ht : tau = geometryEta * c / (n + 1 : ℝ))
    (z : SaddleSpace dx dy) (hr : |pairedA U V (Fin.last n) z| ≤ tau) :
    lam * c / (2 * Real.sqrt (n + 1)) ≤
      ‖scalarSaddleOperator (minimaxHardPotential profile tau lam (balancedQ n) c hU hV) z‖ := by
  have h := source_scalar_residual_lower hU hV profile htau
    (balancedQ_nonneg n) (balancedQ_le_one n) hlam c tau z hr
  have hN : (0 : ℝ) < n + 1 := by positivity
  have hnt : (n + 1 : ℝ) * tau = geometryEta * c := by
    rw [ht]
    field_simp [ne_of_gt hN]
  have htle : tau ≤ geometryEta * c := by
    rw [ht]
    apply div_le_self (by unfold geometryEta; positivity)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hq := mul_le_mul_of_nonneg_right (balancedQ_power_lower n) hc
  have hmargin := explicit_gated_residual_margin c hc
  have hnum : c / 2 ≤ balancedQ n ^ n * c - tau - (n + 1 : ℝ) * tau := by
    rw [hnt]
    linarith
  have hdiv := div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg (n + 1 : ℝ))
  have hmul := mul_le_mul_of_nonneg_left hdiv hlam
  have heq : lam * (c / 2 / Real.sqrt (n + 1 : ℝ)) = lam * c / (2 * Real.sqrt (n + 1 : ℝ)) := by ring
  rw [heq] at hmul
  exact hmul.trans h

end Source

/-- The actual Euclidean product projections are contractions. -/
theorem source_block_norms_le {dx dy : ℕ} (z : SaddleSpace dx dy) :
    ‖primalBlock z‖ ≤ ‖z‖ ∧ ‖dualBlock z‖ ≤ ‖z‖ := by
  have h := join_blocks_inner (primalBlock z) (primalBlock z) (dualBlock z) (dualBlock z)
  rw [join_blocks z] at h
  simp only [real_inner_self_eq_norm_sq] at h
  constructor <;> nlinarith [norm_nonneg z, norm_nonneg (primalBlock z), norm_nonneg (dualBlock z),
    sq_nonneg ‖primalBlock z‖, sq_nonneg ‖dualBlock z‖]

@[simp] theorem source_primal_sub {dx dy : ℕ} (z w : SaddleSpace dx dy) :
    primalBlock (z - w) = primalBlock z - primalBlock w := by ext i; rfl
@[simp] theorem source_dual_sub {dx dy : ℕ} (z w : SaddleSpace dx dy) :
    dualBlock (z - w) = dualBlock z - dualBlock w := by ext i; rfl


end MinimaxAudit
