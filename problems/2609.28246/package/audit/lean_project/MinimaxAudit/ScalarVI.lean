import MinimaxAudit.CriterionFull
import VIReference.Pilot.AdmissibleOracle

/-! Concrete scalar instance to the inherited VI solver's admissible class. -/
open Set
namespace MinimaxAudit.ScalarVI
open VIReference.Pilot

noncomputable section
variable {p dx dy : ℕ} {L D : ℝ} {X : Set (Primal dx)} {Y : Set (Dual dy)}

/-- Euclidean join is continuous for the ordinary topological product. -/
theorem continuous_join_blocks :
    Continuous (fun z : Primal dx × Dual dy => joinBlocks z.1 z.2) := by
  have h := (((primalEmbedding dx dy).continuous.comp continuous_fst).add
    ((dualEmbedding dx dy).continuous.comp continuous_snd))
  convert! h using 1
  funext z
  exact join_blocks_embedding_sum z.1 z.2

theorem product_domain_eq_join_image :
    productDomain X Y = (fun z : Primal dx × Dual dy => joinBlocks z.1 z.2) '' (X ×ˢ Y) := by
  ext z
  constructor
  · intro hz
    exact ⟨(primalBlock z, dualBlock z), hz, join_blocks z⟩
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    simpa [productDomain] using And.intro hx hy

theorem product_domain_compact (hX : IsCompact X) (hY : IsCompact Y) :
    IsCompact (productDomain X Y) := by
  rw [product_domain_eq_join_image]
  exact (hX.prod hY).image continuous_join_blocks

theorem product_domain_convex (hX : Convex ℝ X) (hY : Convex ℝ Y) :
    Convex ℝ (productDomain X Y) := by
  have h := (hX.linear_preimage (primalProjection dx dy).toLinearMap).inter
    (hY.linear_preimage (dualProjection dx dy).toLinearMap)
  have heq : (primalProjection dx dy) ⁻¹' X ∩ (dualProjection dx dy) ⁻¹' Y = productDomain X Y := by
    ext z
    simp [productDomain]
  rw [← heq]
  exact h

/-- All computational fields are public data; proof fields do not contain
or reveal the unknown scalar objective. -/
def scalarVIData (p : ℕ) (L D : ℝ) (X : Set (Primal dx)) (Y : Set (Dual dy))
    (hp : 2 ≤ p) (hL : 0 < L) (hD : 0 < D) (hdim : 0 < dx + dy)
    (hneX : X.Nonempty) (hneY : Y.Nonempty) (hcX : IsCompact X) (hcY : IsCompact Y)
    (hvX : Convex ℝ X) (hvY : Convex ℝ Y)
    (hdiam : ∀ z ∈ productDomain X Y, ∀ w ∈ productDomain X Y, ‖z - w‖ ≤ D)
    (z0 : SaddleSpace dx dy) (hz0 : z0 ∈ productDomain X Y) : VIPublicData (SaddleSpace dx dy) where
  dimension_pos := by simpa [SaddleSpace] using hdim
  p := p
  p_ge_two := hp
  Lp := L
  Lp_pos := hL
  D := D
  D_pos := hD
  X := productDomain X Y
  X_nonempty := ⟨z0, hz0⟩
  X_compact := product_domain_compact hcX hcY
  X_convex := product_domain_convex hvX hvY
  x0 := z0
  x0_mem := hz0
  diameter_le z hz w hw := by simpa only [dist_eq_norm] using hdiam z hz w hw

/-- Scalar neighborhood regularity supplies actual order p−1 regularity
of the signed-gradient operator. -/
theorem scalar_operator_regularity {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) :
    ∃ O : Set (SaddleSpace dx dy), IsOpen O ∧ productDomain X Y ⊆ O ∧
      ContDiffOn ℝ (↑(p - 1 : ℕ)) (scalarSaddleOperator phi) O := by
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    ⟨O, hO, hZO, hreg⟩, hcx, hcy, hLip, hsaddle⟩
  have hder : ContDiffOn ℝ (↑(p - 1 : ℕ)) (fderiv ℝ phi) O :=
    hreg.fderiv_of_isOpen hO (by norm_cast; omega)
  have hgrad : ContDiffOn ℝ (↑(p - 1 : ℕ)) (gradient phi) O :=
    (InnerProductSpace.toDual ℝ (SaddleSpace dx dy)).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hder
  have hsign := (euclideanSaddleSign dx dy).toContinuousLinearEquiv.contDiff.comp_contDiffOn hgrad
  exact ⟨O, hO, hZO, by simpa only [scalarSaddleOperator, Function.comp_def] using! hsign⟩

/-- Source highest-order scalar smoothness transfers with no loss. -/
theorem scalar_operator_top_lipschitz {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) {z w : SaddleSpace dx dy}
    (hz : z ∈ productDomain X Y) (hw : w ∈ productDomain X Y) :
    ‖iteratedFDeriv ℝ (p - 1) (scalarSaddleOperator phi) z -
      iteratedFDeriv ℝ (p - 1) (scalarSaddleOperator phi) w‖ ≤ L * ‖z - w‖ := by
  cases p with
  | zero => have hp := hadm.1; omega
  | succ k =>
    have hLip := hadm.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    change ‖iteratedFDeriv ℝ k (scalarSaddleOperator phi) z -
      iteratedFDeriv ℝ k (scalarSaddleOperator phi) w‖ ≤ L * ‖z - w‖
    exact scalar_saddle_highest_derivative_lipschitz (euclideanSaddleSign dx dy) phi k
      (productDomain X Y) L hLip hz hw

/-- The source class's existing saddle witnesses satisfy the actual VI
first-order inequalities. No unconstrained zero is assumed. -/
theorem scalar_saddle_gives_vi_solution {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) :
    ∃ zStar ∈ productDomain X Y, ∀ z ∈ productDomain X Y,
      0 ≤ inner ℝ (scalarSaddleOperator phi zStar) (z - zStar) := by
  rcases hadm with ⟨hp, hL, hD, hneX, hneY, hcX, hcY, hvX, hvY, hdiam,
    ⟨O, hO, hZO, hreg⟩, hcx, hcy, hLip,
    ⟨xs, hxs, ys, hys, hsaddle⟩⟩
  have hzs : joinBlocks xs ys ∈ productDomain X Y := by simpa [productDomain] using And.intro hxs hys
  have hd : DifferentiableAt ℝ phi (joinBlocks xs ys) :=
    (hreg.contDiffAt (hO.mem_nhds (hZO hzs))).differentiableAt (by exact_mod_cast (by omega : p ≠ 0))
  have hg := hd.hasGradientAt
  have hxgrad := has_gradient_primal_slice hg
  have hygrad := has_gradient_dual_slice hg
  have hmin : IsMinOn (fun u => phi (joinBlocks u ys)) X xs := by
    intro u hu
    exact (hsaddle u hu ys hys).2
  have hmax : IsMaxOn (fun v => phi (joinBlocks xs v)) Y ys := by
    intro v hv
    exact (hsaddle xs hxs v hv).1
  refine ⟨joinBlocks xs ys, hzs, ?_⟩
  intro z hz
  have hpx := hmin.localize.hasFDerivWithinAt_nonneg hxgrad.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_openSegment_subset (hvX.openSegment_subset hxs hz.1))
  have hdy := hmax.localize.hasFDerivWithinAt_nonpos hygrad.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_openSegment_subset (hvY.openSegment_subset hys hz.2))
  simp only [InnerProductSpace.toDual_apply_apply] at hpx hdy
  have hdisp : z - joinBlocks xs ys = joinBlocks (primalBlock z - xs) (dualBlock z - ys) := by
    rw [join_blocks_sub, join_blocks]
  change 0 ≤ inner ℝ (euclideanSaddleSign dx dy (gradient phi (joinBlocks xs ys))) _
  rw [saddle_sign_blocks, hdisp, join_blocks_inner, inner_neg_left]
  linarith

/-- The actual scalar class embeds in the inherited VI class, using only
public-field identifications. The unknown objective is not part of data. -/
theorem scalar_operator_is_admissible
    (data : VIPublicData (SaddleSpace dx dy)) (hp : data.p = p) (hL : data.Lp = L)
    (hX : data.X = productDomain X Y) {phi : SaddleSpace dx dy → ℝ}
    (hadm : AdmissibleScalar p L D X Y phi) :
    IsAdmissibleOperator data (scalarSaddleOperator phi) := by
  subst p
  subst L
  constructor
  · obtain ⟨O, hO, hZO, hreg⟩ := scalar_operator_regularity hadm
    refine ⟨O, hO, by simpa only [hX] using hZO, ?_⟩
    convert hreg using 1 <;> norm_cast
  · intro z hz w hw
    exact admissible_saddle_operator_monotone hadm (by simpa only [hX] using hz)
      (by simpa only [hX] using hw)
  · intro z hz w hw
    exact scalar_operator_top_lipschitz hadm
      (by simpa only [hX] using hz) (by simpa only [hX] using hw)

/-- The source tangent residual and the VI solver's residual use literally
the same normal-correction set, despite their different encodings. -/
theorem tangent_residual_eq_source
    (data : VIPublicData (SaddleSpace dx dy)) (hX : data.X = productDomain X Y)
    (F : SaddleSpace dx dy → SaddleSpace dx dy) (z : SaddleSpace dx dy) :
    VIReference.Pilot.tangentResidual data F z = auditedTangentResidual (productDomain X Y) F z := by
  unfold VIReference.Pilot.tangentResidual auditedTangentResidual
  congr 1
  rw [hX]
  ext u
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

end
end MinimaxAudit.ScalarVI
