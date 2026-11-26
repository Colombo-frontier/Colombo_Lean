import NCConcave16991.AcceleratedBudgetParameters
import NCConcave16991.SVRGProgramFamily

/-!
# Public translated-ball domains for the accelerated oracle program

The carrier and its canonical Hilbert projection depend only on the known
primal center, public radius and dual domain. Joint measurability follows from
the proved product/translation projection formula; no unknown objective or
smoothness assumption occurs in this public domain family.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped InnerProductSpace

namespace NCConcave16991.AcceleratedProgram

abbrev Parameter (dx dy : ℕ) := PrimalSpace dx × DualSpace dy

variable (p : ProblemParameters) (Δ : ℝ) {dx dy : ℕ} (K : KnownDualDomain dy p.diameter)

def carrier (θ : Parameter dx dy) : Set (JointSpace dx dy) :=
  {z | z.fst ∈ closedBall θ.1 (Accelerated.publicRadius p Δ) ∧ z.snd ∈ K.carrier}

theorem carrier_nonempty (θ : Parameter dx dy) : (carrier p Δ K θ).Nonempty := by
  obtain ⟨y, hy⟩ := K.nonempty
  refine ⟨jointPoint θ.1 y, ?_⟩
  change θ.1 ∈ closedBall θ.1 (Accelerated.publicRadius p Δ) ∧ y ∈ K.carrier
  exact ⟨by simpa using (Accelerated.publicRadius_pos p Δ).le, hy⟩

theorem carrier_closed (θ : Parameter dx dy) : IsClosed (carrier p Δ K θ) :=
  (isClosed_closedBall.preimage (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous).inter
    (K.compact.isClosed.preimage (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous)

theorem carrier_convex (θ : Parameter dx dy) : Convex ℝ (carrier p Δ K θ) :=
  ((convex_closedBall θ.1 (Accelerated.publicRadius p Δ)).linear_preimage
    (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).toLinearMap).inter
    (K.convex.linear_preimage (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).toLinearMap)

def zeroBallProjection (x : PrimalSpace dx) : closedBall (0 : PrimalSpace dx) (Accelerated.publicRadius p Δ) :=
  VariationalInequality.projection (closedBall (0 : PrimalSpace dx) (Accelerated.publicRadius p Δ))
    ⟨0, by simpa using (Accelerated.publicRadius_pos p Δ).le⟩ isClosed_closedBall
    (convex_closedBall 0 (Accelerated.publicRadius p Δ)) x

def dualProjection (y : DualSpace dy) : K.carrier :=
  VariationalInequality.projection K.carrier K.nonempty K.compact.isClosed K.convex y

/-- The explicit known-geometry product/translation formula. -/
def projected (θ : Parameter dx dy) (z : JointSpace dx dy) : JointSpace dx dy :=
  jointPoint (θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx))
    (dualProjection p K z.snd)

theorem projected_mem (θ : Parameter dx dy) (z : JointSpace dx dy) :
    projected p Δ K θ z ∈ carrier p Δ K θ := by
  have hx := (zeroBallProjection p Δ (z.fst - θ.1)).property
  have hy := (dualProjection p K z.snd).property
  constructor
  · change ‖θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx) - θ.1‖ ≤ _
    simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using hx
  · exact hy

/-- The canonical projection agrees with the concrete product formula, by its
literal supporting-halfspace characterization. -/
theorem projection_formula (θ : Parameter dx dy) (z : JointSpace dx dy) :
    (VariationalInequality.projection (carrier p Δ K θ) (carrier_nonempty p Δ K θ)
      (carrier_closed p Δ K θ) (carrier_convex p Δ K θ) z : JointSpace dx dy) =
        projected p Δ K θ z := by
  have he : VariationalInequality.projection (carrier p Δ K θ) (carrier_nonempty p Δ K θ)
      (carrier_closed p Δ K θ) (carrier_convex p Δ K θ) z =
      ⟨projected p Δ K θ z, projected_mem p Δ K θ z⟩ := by
    apply (VariationalInequality.projection_eq_iff _ _ _ _ _ _).2
    intro w hw
    have hx := VariationalInequality.projection_inner
      (closedBall (0 : PrimalSpace dx) (Accelerated.publicRadius p Δ))
      ⟨0, by simpa using (Accelerated.publicRadius_pos p Δ).le⟩ isClosed_closedBall
      (convex_closedBall 0 (Accelerated.publicRadius p Δ))
      (z.fst - θ.1) (w.fst - θ.1)
      (by simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using hw.1)
    have hy := VariationalInequality.projection_inner K.carrier K.nonempty K.compact.isClosed K.convex
      z.snd w.snd hw.2
    change ⟪z.fst - (θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx)),
      w.fst - (θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx))⟫_ℝ +
      ⟪z.snd - (dualProjection p K z.snd : DualSpace dy),
        w.snd - (dualProjection p K z.snd : DualSpace dy)⟫_ℝ ≤ 0
    change ⟪(z.fst - θ.1) - (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx),
      (w.fst - θ.1) - (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx)⟫_ℝ ≤ 0 at hx
    have hx1 : (z.fst - θ.1) - (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx) =
        z.fst - (θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx)) := by abel
    have hx2 : (w.fst - θ.1) - (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx) =
        w.fst - (θ.1 + (zeroBallProjection p Δ (z.fst - θ.1) : PrimalSpace dx)) := by abel
    rw [hx1, hx2] at hx
    exact add_nonpos hx hy
  exact congrArg (fun w : carrier p Δ K θ ↦ (w : JointSpace dx dy)) he

theorem projected_continuous : Continuous (Function.uncurry (projected p Δ K (dx := dx))) := by
  let A := Parameter dx dy × JointSpace dx dy
  have hc : Continuous (fun a : A ↦ a.1.1) := continuous_fst.comp continuous_fst
  have hx : Continuous (fun a : A ↦ a.2.fst) :=
    (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd
  have hy : Continuous (fun a : A ↦ a.2.snd) :=
    (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd
  have hp0 : Continuous (fun x : PrimalSpace dx ↦ (zeroBallProjection p Δ x : PrimalSpace dx)) :=
    continuous_subtype_val.comp (VariationalInequality.projection_lipschitz
      (closedBall (0 : PrimalSpace dx) (Accelerated.publicRadius p Δ))
      ⟨0, by simpa using (Accelerated.publicRadius_pos p Δ).le⟩ isClosed_closedBall
      (convex_closedBall 0 (Accelerated.publicRadius p Δ))).continuous
  have hpY : Continuous (fun y : DualSpace dy ↦ (dualProjection p K y : DualSpace dy)) :=
    continuous_subtype_val.comp (VariationalInequality.projection_lipschitz
      K.carrier K.nonempty K.compact.isClosed K.convex).continuous
  exact (WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).comp
    ((hc.add (hp0.comp (hx.sub hc))).prodMk (hpY.comp hy))

def domainFamily : SVRGProgram.DomainFamily (dx := dx) K (Parameter dx dy) where
  carrier := carrier p Δ K
  nonempty := carrier_nonempty p Δ K
  closed := carrier_closed p Δ K
  convex := carrier_convex p Δ K
  feasible := fun _ _ hz ↦ hz.2
  projection_measurable := by
    have he : (fun a : Parameter dx dy × JointSpace dx dy ↦
        (VariationalInequality.projection (carrier p Δ K a.1) (carrier_nonempty p Δ K a.1)
          (carrier_closed p Δ K a.1) (carrier_convex p Δ K a.1) a.2 : JointSpace dx dy)) =
        Function.uncurry (projected p Δ K) :=
      funext (fun a ↦ projection_formula p Δ K a.1 a.2)
    rw [he]
    exact (projected_continuous p Δ K).measurable

def correction (τ : ℝ) (a : Parameter dx dy × JointSpace dx dy) : JointSpace dx dy :=
  saddleCorrection p.L τ a.1.2 a.1.1 a.2

theorem correction_continuous (τ : ℝ) : Continuous (correction p (dx := dx) (dy := dy) τ) := by
  let A := Parameter dx dy × JointSpace dx dy
  have hc : Continuous (fun a : A ↦ a.1.1) := continuous_fst.comp continuous_fst
  have hv : Continuous (fun a : A ↦ a.1.2) := continuous_snd.comp continuous_fst
  have hx : Continuous (fun a : A ↦ a.2.fst) :=
    (WithLp.fstL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd
  have hy : Continuous (fun a : A ↦ a.2.snd) :=
    (WithLp.sndL 2 ℝ (PrimalSpace dx) (DualSpace dy)).continuous.comp continuous_snd
  have hL : Continuous (fun _ : A ↦ (2 * p.L)) := continuous_const
  have hτ : Continuous (fun _ : A ↦ τ) := continuous_const
  exact (WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).comp
    ((hL.smul (hx.sub hc)).prodMk (hτ.smul (hy.sub hv)))

def anchor (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) (θ : Parameter dx dy) :
    SVRGProgram.Point (domainFamily p Δ K (dx := dx)) :=
  ⟨(θ, jointPoint θ.1 y0), by
    change θ.1 ∈ closedBall θ.1 (Accelerated.publicRadius p Δ) ∧ y0 ∈ K.carrier
    exact ⟨by simpa using (Accelerated.publicRadius_pos p Δ).le, hy0⟩⟩

theorem anchor_measurable (y0 : DualSpace dy) (hy0 : y0 ∈ K.carrier) :
    Measurable (anchor p Δ K (dx := dx) y0 hy0) := by
  apply Measurable.subtype_mk
  exact measurable_id.prodMk
    ((WithLp.prod_continuous_toLp 2 (PrimalSpace dx) (DualSpace dy)).measurable.comp
      (measurable_fst.prodMk measurable_const))

theorem carrier_eq_feasibleProduct (P : Problem p dx dy K) (hAS : P.averagedSmooth)
    (y0 : DualSpace dy) (θ : Parameter dx dy) :
    carrier p Δ K θ = Accelerated.feasibleProduct (Accelerated.ballSaddle P hAS Δ y0 θ.1) := rfl

end NCConcave16991.AcceleratedProgram
