import MinimaxAudit.Model
import MinimaxAudit.Geometry

/-!
# Full scalar saddle-gap / true tangent-residual comparison

This module supplies the actual Euclidean block embeddings, identifies the
partial gradients of a scalar potential, and proves the source `lem:criteria`
comparison for every `AdmissibleScalar` instance. The tangent residual is the
actual `Metric.infDist` from `Geometry.lean`; no attainment is assumed.
-/
namespace MinimaxAudit

/-- Euclidean product coordinates split their actual inner product. -/
theorem join_blocks_inner {dx dy : ℕ} (x u : Primal dx) (y v : Dual dy) :
    inner ℝ (joinBlocks x y) (joinBlocks u v) = inner ℝ x u + inner ℝ y v := by
  simp only [PiLp.inner_apply, Fintype.sum_sum_type]
  rfl

theorem join_blocks_add {dx dy : ℕ} (x u : Primal dx) (y v : Dual dy) :
    joinBlocks (x + u) (y + v) = joinBlocks x y + joinBlocks u v := by
  ext i
  cases i <;> rfl

theorem join_blocks_sub {dx dy : ℕ} (x u : Primal dx) (y v : Dual dy) :
    joinBlocks (x - u) (y - v) = joinBlocks x y - joinBlocks u v := by
  ext i
  cases i <;> rfl

/-- An actual isometric primal embedding into the Euclidean product. -/
noncomputable def primalEmbedding (dx dy : ℕ) : Primal dx →ₗᵢ[ℝ] SaddleSpace dx dy where
  toFun x := joinBlocks x 0
  map_add' x u := by simpa using join_blocks_add x u (0 : Dual dy) 0
  map_smul' r x := by ext i; cases i <;> simp [joinBlocks]
  norm_map' x := by
    change ‖joinBlocks x (0 : Dual dy)‖ = ‖x‖
    have h := join_blocks_inner x x (0 : Dual dy) 0
    simp only [real_inner_self_eq_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h
    nlinarith [norm_nonneg (joinBlocks x (0 : Dual dy)), norm_nonneg x]

/-- An actual isometric dual embedding into the Euclidean product. -/
noncomputable def dualEmbedding (dx dy : ℕ) : Dual dy →ₗᵢ[ℝ] SaddleSpace dx dy where
  toFun y := joinBlocks 0 y
  map_add' y v := by simpa using join_blocks_add (0 : Primal dx) 0 y v
  map_smul' r y := by ext i; cases i <;> simp [joinBlocks]
  norm_map' y := by
    change ‖joinBlocks (0 : Primal dx) y‖ = ‖y‖
    have h := join_blocks_inner (0 : Primal dx) 0 y y
    simp only [real_inner_self_eq_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at h
    nlinarith [norm_nonneg (joinBlocks (0 : Primal dx) y), norm_nonneg y]

@[simp] theorem primal_embedding_apply {dx dy : ℕ} (x : Primal dx) :
    primalEmbedding dx dy x = joinBlocks x 0 := rfl
@[simp] theorem dual_embedding_apply {dx dy : ℕ} (y : Dual dy) :
    dualEmbedding dx dy y = joinBlocks 0 y := rfl

theorem join_blocks_embedding_sum {dx dy : ℕ} (x : Primal dx) (y : Dual dy) :
    joinBlocks x y = primalEmbedding dx dy x + dualEmbedding dx dy y := by
  simpa using join_blocks_add x 0 (0 : Dual dy) y

/-- The manuscript's actual scalar saddle operator. -/
noncomputable def scalarSaddleOperator {dx dy : ℕ} (phi : SaddleSpace dx dy → ℝ)
    (z : SaddleSpace dx dy) : SaddleSpace dx dy :=
  euclideanSaddleSign dx dy (gradient phi z)

theorem saddle_sign_blocks {dx dy : ℕ} (g : SaddleSpace dx dy) :
    euclideanSaddleSign dx dy g = joinBlocks (primalBlock g) (-dualBlock g) := by
  ext i
  cases i with
  | inl i => rfl
  | inr i => rfl

/-- A full scalar gradient supplies the genuine gradient of each primal slice. -/
theorem has_gradient_primal_slice {dx dy : ℕ} {phi : SaddleSpace dx dy → ℝ}
    {x : Primal dx} {y : Dual dy} {g : SaddleSpace dx dy}
    (hg : HasGradientAt phi g (joinBlocks x y)) :
    HasGradientAt (fun u => phi (joinBlocks u y)) (primalBlock g) x := by
  have hjoin : HasFDerivAt (fun u : Primal dx => joinBlocks u y)
      (primalEmbedding dx dy).toContinuousLinearMap x := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, ← join_blocks_embedding_sum] using
      (((primalEmbedding dx dy).toContinuousLinearMap.hasFDerivAt (x := x)).add_const
        (dualEmbedding dx dy y))
  apply hasGradientAt_iff_hasFDerivAt.2
  have heq : InnerProductSpace.toDual ℝ (Primal dx) (primalBlock g) =
      (InnerProductSpace.toDual ℝ (SaddleSpace dx dy) g).comp
        (primalEmbedding dx dy).toContinuousLinearMap := by
    ext h
    change inner ℝ (primalBlock g) h = inner ℝ g (joinBlocks h 0)
    rw [← join_blocks g, join_blocks_inner]
    simp
  rw [heq]
  exact hg.hasFDerivAt.comp x hjoin

/-- A full scalar gradient supplies the genuine gradient of each dual slice. -/
theorem has_gradient_dual_slice {dx dy : ℕ} {phi : SaddleSpace dx dy → ℝ}
    {x : Primal dx} {y : Dual dy} {g : SaddleSpace dx dy}
    (hg : HasGradientAt phi g (joinBlocks x y)) :
    HasGradientAt (fun v => phi (joinBlocks x v)) (dualBlock g) y := by
  have hjoin : HasFDerivAt (fun v : Dual dy => joinBlocks x v)
      (dualEmbedding dx dy).toContinuousLinearMap y := by
    simpa only [LinearIsometry.coe_toContinuousLinearMap, ← join_blocks_embedding_sum, add_comm] using
      (((dualEmbedding dx dy).toContinuousLinearMap.hasFDerivAt (x := y)).add_const
        (primalEmbedding dx dy x))
  apply hasGradientAt_iff_hasFDerivAt.2
  have heq : InnerProductSpace.toDual ℝ (Dual dy) (dualBlock g) =
      (InnerProductSpace.toDual ℝ (SaddleSpace dx dy) g).comp
        (dualEmbedding dx dy).toContinuousLinearMap := by
    ext h
    change inner ℝ (dualBlock g) h = inner ℝ g (joinBlocks 0 h)
    rw [← join_blocks g, join_blocks_inner]
    simp
  rw [heq]
  exact hg.hasFDerivAt.comp y hjoin

/-- The full first-order inequality with the actual scalar saddle operator. -/
theorem scalar_saddle_first_order {dx dy : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    {x x' : Primal dx} {y y' : Dual dy}
    (hx : x ∈ X) (hx' : x' ∈ X) (hy : y ∈ Y) (hy' : y' ∈ Y)
    (hcx : ConvexOn ℝ X (fun u => phi (joinBlocks u y)))
    (hcy : ConcaveOn ℝ Y (fun v => phi (joinBlocks x v)))
    (hd : DifferentiableAt ℝ phi (joinBlocks x y)) :
    phi (joinBlocks x y') - phi (joinBlocks x' y) ≤
      inner ℝ (scalarSaddleOperator phi (joinBlocks x y))
        (joinBlocks x y - joinBlocks x' y') := by
  have hg := hd.hasGradientAt
  have h := saddle_first_order_from_convex_concave
    (phi := fun u v => phi (joinBlocks u v)) hx hx' hy hy' hcx hcy
    (has_gradient_primal_slice hg) (has_gradient_dual_slice hg)
  change _ ≤ inner ℝ (euclideanSaddleSign dx dy (gradient phi (joinBlocks x y))) _
  rw [saddle_sign_blocks, ← join_blocks_sub, join_blocks_inner]
  exact h

/-- Source `lem:criteria`, for arbitrary nonempty feasible block sets with
convex/concave slices and a differentiable potential at the output point. -/
theorem full_gap_le_diameter_tangent {dx dy : ℕ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    {x : Primal dx} {y : Dual dy} {D : ℝ}
    (hneX : X.Nonempty) (hneY : Y.Nonempty) (hx : x ∈ X) (hy : y ∈ Y) (hD : 0 < D)
    (hdiam : ∀ w ∈ productDomain X Y, ‖joinBlocks x y - w‖ ≤ D)
    (hcx : ConvexOn ℝ X (fun u => phi (joinBlocks u y)))
    (hcy : ConcaveOn ℝ Y (fun v => phi (joinBlocks x v)))
    (hd : DifferentiableAt ℝ phi (joinBlocks x y)) :
    auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y ≤
      D * auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) (joinBlocks x y) := by
  have hne : (saddleDifferences X Y (fun u v => phi (joinBlocks u v)) x y).Nonempty := by
    obtain ⟨u, hu⟩ := hneX
    obtain ⟨v, hv⟩ := hneY
    exact ⟨_, u, hu, v, hv, rfl⟩
  have hcert : ∀ n, IsNormalAt (productDomain X Y) (joinBlocks x y) n →
      auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y ≤
        D * ‖scalarSaddleOperator phi (joinBlocks x y) + n‖ := by
    intro n hn
    apply csSup_le hne
    rintro d ⟨u, hu, v, hv, rfl⟩
    exact comparison_le_normal_certificate (by simp [productDomain, hu, hv]) hn
      (hdiam (joinBlocks u v) (by simp [productDomain, hu, hv]))
      (scalar_saddle_first_order hx hu hy hv hcx hcy hd)
  have hdiv : auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) x y / D ≤
      auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) (joinBlocks x y) := by
    apply (Metric.le_infDist (normalCorrections_nonempty _ _ _)).2
    rintro r ⟨n, hn, rfl⟩
    rw [dist_zero_left]
    exact (div_le_iff₀ hD).2 (by simpa [mul_comm] using hcert n hn)
  have := (div_le_iff₀ hD).1 hdiv
  simpa [mul_comm] using this

/-- Complete admissible-instance specialization: no first-order comparison,
normal certificate, or residual bound is supplied as an assumed field. -/
theorem admissible_gap_le_diameter_tangent {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) :
    auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) (primalBlock z) (dualBlock z) ≤
      D * auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z := by
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    ⟨O, hO, hZO, hreg⟩, hcx, hcy, hLip, hsaddle⟩
  have hdiff : DifferentiableAt ℝ phi z :=
    (hreg.contDiffAt (hO.mem_nhds (hZO hz))).differentiableAt (by exact_mod_cast (by omega : p ≠ 0))
  have h := full_gap_le_diameter_tangent hneX hneY hz.1 hz.2 hD
    (fun w hw => by simpa using hdiam z hz w hw) (hcx _ hz.2) (hcy _ hz.1)
    (by simpa using hdiff)
  simpa using h


/-- The primal block map as an actual continuous linear projection. -/
noncomputable def primalProjection (dx dy : ℕ) : SaddleSpace dx dy →L[ℝ] Primal dx :=
  (primalEmbedding dx dy).toContinuousLinearMap.adjoint

/-- The dual block map as an actual continuous linear projection. -/
noncomputable def dualProjection (dx dy : ℕ) : SaddleSpace dx dy →L[ℝ] Dual dy :=
  (dualEmbedding dx dy).toContinuousLinearMap.adjoint

@[simp] theorem primal_projection_apply {dx dy : ℕ} (z : SaddleSpace dx dy) :
    primalProjection dx dy z = primalBlock z := by
  apply ext_inner_right ℝ
  intro u
  change inner ℝ ((primalEmbedding dx dy).toContinuousLinearMap.adjoint z) u = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ z (joinBlocks u 0) = _
  rw [← join_blocks z, join_blocks_inner]
  simp

@[simp] theorem dual_projection_apply {dx dy : ℕ} (z : SaddleSpace dx dy) :
    dualProjection dx dy z = dualBlock z := by
  apply ext_inner_right ℝ
  intro v
  change inner ℝ ((dualEmbedding dx dy).toContinuousLinearMap.adjoint z) v = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ z (joinBlocks 0 v) = _
  rw [← join_blocks z, join_blocks_inner]
  simp

/-- All derivative tensors of an objective independent of y are computed
from the primal scalar jet by fixed linear restriction of their inputs.
This neighborhood-local statement includes derivative order zero. -/
theorem convex_embedding_jet_formula {dx dy k p : ℕ}
    (f : Primal dx → ℝ) (U : Set (Primal dx)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ p f U) (hk : k ≤ p) (z : SaddleSpace dx dy)
    (hz : primalBlock z ∈ U) :
    iteratedFDeriv ℝ k (fun w : SaddleSpace dx dy => f (primalBlock w)) z =
      (iteratedFDeriv ℝ k f (primalBlock z)).compContinuousLinearMap
        (fun _ => primalProjection dx dy) := by
  have hpre : IsOpen ((primalProjection dx dy) ⁻¹' U) := hU.preimage (primalProjection dx dy).continuous
  have hz' : primalProjection dx dy z ∈ U := by simpa using hz
  have hjet := (primalProjection dx dy).iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn
    hpre.uniqueDiffOn hz' (i := k) (by exact_mod_cast hk)
  rw [iteratedFDerivWithin_of_isOpen k hpre hz', iteratedFDerivWithin_of_isOpen k hU hz'] at hjet
  simpa only [Function.comp_def, primal_projection_apply] using hjet

/-- Exact convex-embedding gap identity, with the minimum represented by
the infimum of the actual image set and justified by compact attainment. -/
theorem convex_embedding_gap_eq {P Q : Type*} [TopologicalSpace P]
    {X : Set P} {Y : Set Q} (f : P → ℝ)
    (hc : IsCompact X) (hneX : X.Nonempty) (hneY : Y.Nonempty)
    (hf : ContinuousOn f X) (x : P) (y : Q) :
    auditedSaddleGap X Y (fun u _ => f u) x y = f x - sInf (f '' X) := by
  obtain ⟨xmin, hxmin, hmin⟩ := hc.exists_isMinOn hneX hf
  have hinf : sInf (f '' X) = f xmin := by
    apply le_antisymm
    · apply csInf_le (hc.image_of_continuousOn hf).bddBelow
      exact ⟨xmin, hxmin, rfl⟩
    · apply le_csInf (hneX.image f)
      rintro _ ⟨u, hu, rfl⟩
      exact hmin hu
  have hne : (saddleDifferences X Y (fun u _ => f u) x y).Nonempty := by
    obtain ⟨v, hv⟩ := hneY
    exact ⟨_, xmin, hxmin, v, hv, rfl⟩
  have hb : BddAbove (saddleDifferences X Y (fun u _ => f u) x y) := by
    refine ⟨f x - f xmin, ?_⟩
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact sub_le_sub_left (hmin hu) (f x)
  rw [hinf]
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact sub_le_sub_left (hmin hu) (f x)
  · obtain ⟨v, hv⟩ := hneY
    exact comparison_le_saddleGap hb hxmin hv


/-- The full returned scalar jet, including the objective value, is a
fixed transform of exactly one primal scalar jet. -/
theorem convex_embedding_complete_jet {dx dy p : ℕ}
    (f : Primal dx → ℝ) (U : Set (Primal dx)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ p f U) (z : SaddleSpace dx dy) (hz : primalBlock z ∈ U) :
    exactScalarJet p (fun w : SaddleSpace dx dy => f (primalBlock w)) z =
      (fun k : Fin (p + 1) =>
        ((exactScalarJet p f (primalBlock z)) k).compContinuousLinearMap
          (fun _ => primalProjection dx dy)) := by
  funext k
  exact convex_embedding_jet_formula f U hU hf (by omega : k.1 ≤ p) z hz

/-- Any tensor evaluation involving a purely dual direction vanishes,
as asserted in the convex-embedding part of the source lemma. -/
theorem convex_embedding_derivative_vanishes {dx dy p k : ℕ}
    (f : Primal dx → ℝ) (U : Set (Primal dx)) (hU : IsOpen U)
    (hf : ContDiffOn ℝ p f U) (hk : k ≤ p) (z : SaddleSpace dx dy)
    (hz : primalBlock z ∈ U) (directions : Fin k → SaddleSpace dx dy)
    (i : Fin k) (hi : primalBlock (directions i) = 0) :
    iteratedFDeriv ℝ k (fun w : SaddleSpace dx dy => f (primalBlock w)) z directions = 0 := by
  rw [convex_embedding_jet_formula f U hU hf hk z hz]
  change (iteratedFDeriv ℝ k f (primalBlock z))
    (fun j => primalProjection dx dy (directions j)) = 0
  exact (iteratedFDeriv ℝ k f (primalBlock z)).toMultilinearMap.map_coord_zero i (by simpa using hi)


/-- The supremum-of-differences definition equals the max-minus-min
expression on compact sets; the extrema are actually attained. -/
theorem saddle_gap_eq_sup_sub_inf {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]
    {X : Set P} {Y : Set Q} (phi : P → Q → ℝ)
    (hcX : IsCompact X) (hcY : IsCompact Y) (hneX : X.Nonempty) (hneY : Y.Nonempty)
    (x : P) (y : Q) (hcontX : ContinuousOn (fun u => phi u y) X)
    (hcontY : ContinuousOn (fun v => phi x v) Y) :
    auditedSaddleGap X Y phi x y =
      sSup ((fun v => phi x v) '' Y) - sInf ((fun u => phi u y) '' X) := by
  obtain ⟨xmin, hxmin, hmin⟩ := hcX.exists_isMinOn hneX hcontX
  obtain ⟨ymax, hymax, hmax⟩ := hcY.exists_isMaxOn hneY hcontY
  have hinf : sInf ((fun u => phi u y) '' X) = phi xmin y := by
    apply le_antisymm
    · exact csInf_le (hcX.image_of_continuousOn hcontX).bddBelow ⟨xmin, hxmin, rfl⟩
    · apply le_csInf (hneX.image _)
      rintro _ ⟨u, hu, rfl⟩
      exact hmin hu
  have hsup : sSup ((fun v => phi x v) '' Y) = phi x ymax := by
    apply le_antisymm
    · apply csSup_le (hneY.image _)
      rintro _ ⟨v, hv, rfl⟩
      exact hmax hv
    · exact le_csSup (hcY.image_of_continuousOn hcontY).bddAbove ⟨ymax, hymax, rfl⟩
  have hne : (saddleDifferences X Y phi x y).Nonempty :=
    ⟨_, xmin, hxmin, ymax, hymax, rfl⟩
  have hb : BddAbove (saddleDifferences X Y phi x y) := by
    refine ⟨phi x ymax - phi xmin y, ?_⟩
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact sub_le_sub (hmax hv) (hmin hu)
  rw [hsup, hinf]
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨u, hu, v, hv, rfl⟩
    exact sub_le_sub (hmax hv) (hmin hu)
  · exact comparison_le_saddleGap hb hxmin hymax

/-- The primal affine slice is continuous in the real Euclidean metric. -/
theorem continuous_join_primal {dx dy : ℕ} (y : Dual dy) :
    Continuous (fun x : Primal dx => joinBlocks x y) := by
  simpa only [← join_blocks_embedding_sum] using
    (primalEmbedding dx dy).continuous.add_const (dualEmbedding dx dy y)

/-- The dual affine slice is continuous in the real Euclidean metric. -/
theorem continuous_join_dual {dx dy : ℕ} (x : Primal dx) :
    Continuous (fun y : Dual dy => joinBlocks x y) := by
  simpa only [add_comm, ← join_blocks_embedding_sum] using
    (dualEmbedding dx dy).continuous.add_const (primalEmbedding dx dy x)

/-- The source's displayed max/min gap for an actual admissible scalar
instance coincides with the supremum gap used in the geometric modules. -/
theorem admissible_gap_eq_sup_sub_inf {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) :
    auditedSaddleGap X Y (fun u v => phi (joinBlocks u v)) (primalBlock z) (dualBlock z) =
      sSup ((fun v => phi (joinBlocks (primalBlock z) v)) '' Y) -
      sInf ((fun u => phi (joinBlocks u (dualBlock z))) '' X) := by
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    ⟨O, hO, hZO, hreg⟩, hcx, hcy, hLip, hsaddle⟩
  apply saddle_gap_eq_sup_sub_inf _ hcX hcY hneX hneY
  · apply (hreg.continuousOn.mono hZO).comp (continuous_join_primal _).continuousOn
    intro u hu
    simp [productDomain, hu, hz.2]
  · apply (hreg.continuousOn.mono hZO).comp (continuous_join_dual _).continuousOn
    intro v hv
    simp [productDomain, hv, hz.1]

/-- Full source `lem:criteria` with its max/min expression and actual
normal-cone distance, specialized only to the actual admissible class. -/
theorem admissible_maxmin_gap_le_diameter_tangent {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) :
    sSup ((fun v => phi (joinBlocks (primalBlock z) v)) '' Y) -
      sInf ((fun u => phi (joinBlocks u (dualBlock z))) '' X) ≤
      D * auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z := by
  rw [← admissible_gap_eq_sup_sub_inf hadm hz]
  exact admissible_gap_le_diameter_tangent hadm hz


/-- Convex-concavity of an actual admissible scalar instance gives the
actual ambient Euclidean saddle operator's monotonicity. -/
theorem admissible_saddle_operator_monotone {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z w : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) (hw : w ∈ productDomain X Y) :
    0 ≤ inner ℝ (scalarSaddleOperator phi z - scalarSaddleOperator phi w) (z - w) := by
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    ⟨O, hO, hZO, hreg⟩, hcx, hcy, hLip, hsaddle⟩
  have hdz : DifferentiableAt ℝ phi z :=
    (hreg.contDiffAt (hO.mem_nhds (hZO hz))).differentiableAt (by exact_mod_cast (by omega : p ≠ 0))
  have hdw : DifferentiableAt ℝ phi w :=
    (hreg.contDiffAt (hO.mem_nhds (hZO hw))).differentiableAt (by exact_mod_cast (by omega : p ≠ 0))
  have hgz : HasGradientAt phi (gradient phi z) (joinBlocks (primalBlock z) (dualBlock z)) := by
    simpa using hdz.hasGradientAt
  have hgw : HasGradientAt phi (gradient phi w) (joinBlocks (primalBlock w) (dualBlock w)) := by
    simpa using hdw.hasGradientAt
  have hm := convex_concave_gradient_monotonicity
    (phi := fun u v => phi (joinBlocks u v)) hz.1 hw.1 hz.2 hw.2 hcx hcy
    (has_gradient_primal_slice hgz) (has_gradient_dual_slice hgz)
    (has_gradient_primal_slice hgw) (has_gradient_dual_slice hgw)
  have hdisp : z - w = joinBlocks (primalBlock z - primalBlock w) (dualBlock z - dualBlock w) := by
    rw [join_blocks_sub, join_blocks, join_blocks]
  change 0 ≤ inner ℝ
    (euclideanSaddleSign dx dy (gradient phi z) - euclideanSaddleSign dx dy (gradient phi w)) (z - w)
  rw [saddle_sign_blocks, saddle_sign_blocks, ← join_blocks_sub, hdisp, join_blocks_inner]
  exact hm


/-- Source-facing complete `lem:criteria`: the actual scalar max/min gap
is bounded by diameter times the true tangent residual; convex embedding
has the exact optimization gap and its full returned jet is a fixed
transform of one primal jet. No conclusion is supplied as an input field. -/
theorem criteria_source {p dx dy : ℕ} {L D : ℝ}
    {X : Set (Primal dx)} {Y : Set (Dual dy)} {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) :
    (sSup ((fun v => phi (joinBlocks (primalBlock z) v)) '' Y) -
        sInf ((fun u => phi (joinBlocks u (dualBlock z))) '' X) ≤
      D * auditedTangentResidual (productDomain X Y) (scalarSaddleOperator phi) z) ∧
    (∀ (f : Primal dx → ℝ) (U : Set (Primal dx)), IsOpen U → X ⊆ U →
      ContDiffOn ℝ p f U →
      auditedSaddleGap X Y (fun u _ => f u) (primalBlock z) (dualBlock z) =
        f (primalBlock z) - sInf (f '' X) ∧
      exactScalarJet p (fun w : SaddleSpace dx dy => f (primalBlock w)) z =
        (fun k : Fin (p + 1) =>
          ((exactScalarJet p f (primalBlock z)) k).compContinuousLinearMap
            (fun _ => primalProjection dx dy))) := by
  refine ⟨admissible_maxmin_gap_le_diameter_tangent hadm hz, ?_⟩
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    hreg, hcx, hcy, hLip, hsaddle⟩
  intro f U hU hXU hf
  exact ⟨convex_embedding_gap_eq f hcX hneX hneY (hf.continuousOn.mono hXU) _ _,
    convex_embedding_complete_jet f U hU hf z (hXU hz.1)⟩

end MinimaxAudit
