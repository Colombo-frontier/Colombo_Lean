import MinimaxAudit.Gate
import MinimaxAudit.GateCurvature

/-!
# Actual second derivatives of the scalar integral gate

The four coordinate identities below differentiate the manuscript's concrete
integral gate. They connect the previously verified gate calculus with the
explicit Hessian matrix and its curvature bounds.
-/

namespace MinimaxAudit

theorem scalarGate_second_aa (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun x => deriv (fun u => scalarGate profile tau u b) x)
      ((profile.rho ((a + b) / tau) - profile.rho ((a - b) / tau)) / 2) a := by
  have hfun : (fun x => deriv (fun u => scalarGate profile tau u b) x) =
      fun x => (gate profile tau (x + b) - gate profile tau (x - b)) / 2 := by
    funext x
    exact (scalarGate_partial_a profile htau x b).deriv
  rw [hfun]
  have hp := (gate_hasDerivAt profile htau (a + b)).comp a
    ((hasDerivAt_id a).add_const b)
  have hm := (gate_hasDerivAt profile htau (a - b)).comp a
    ((hasDerivAt_id a).sub_const b)
  simpa using (hp.sub hm).div_const 2

theorem scalarGate_second_ab (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun y => deriv (fun u => scalarGate profile tau u y) a)
      ((profile.rho ((a + b) / tau) + profile.rho ((a - b) / tau)) / 2) b := by
  have hfun : (fun y => deriv (fun u => scalarGate profile tau u y) a) =
      fun y => (gate profile tau (a + y) - gate profile tau (a - y)) / 2 := by
    funext y
    exact (scalarGate_partial_a profile htau a y).deriv
  rw [hfun]
  have hp := (gate_hasDerivAt profile htau (a + b)).comp b
    ((hasDerivAt_id b).const_add a)
  have hm := (gate_hasDerivAt profile htau (a - b)).comp b
    ((hasDerivAt_id b).const_sub a)
  simpa only [mul_one, mul_neg_one, sub_neg_eq_add] using! (hp.sub hm).div_const 2

theorem scalarGate_second_ba (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun x => deriv (fun u => scalarGate profile tau x u) b)
      ((profile.rho ((a + b) / tau) + profile.rho ((a - b) / tau)) / 2) a := by
  have hfun : (fun x => deriv (fun u => scalarGate profile tau x u) b) =
      fun x => (gate profile tau (x + b) + gate profile tau (x - b)) / 2 := by
    funext x
    exact (scalarGate_partial_b profile htau x b).deriv
  rw [hfun]
  have hp := (gate_hasDerivAt profile htau (a + b)).comp a
    ((hasDerivAt_id a).add_const b)
  have hm := (gate_hasDerivAt profile htau (a - b)).comp a
    ((hasDerivAt_id a).sub_const b)
  simpa using (hp.add hm).div_const 2

theorem scalarGate_second_bb (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (a b : ℝ) :
    HasDerivAt (fun y => deriv (fun u => scalarGate profile tau a u) y)
      ((profile.rho ((a + b) / tau) - profile.rho ((a - b) / tau)) / 2) b := by
  have hfun : (fun y => deriv (fun u => scalarGate profile tau a u) y) =
      fun y => (gate profile tau (a + y) + gate profile tau (a - y)) / 2 := by
    funext y
    exact (scalarGate_partial_b profile htau a y).deriv
  rw [hfun]
  have hp := (gate_hasDerivAt profile htau (a + b)).comp b
    ((hasDerivAt_id b).const_add a)
  have hm := (gate_hasDerivAt profile htau (a - b)).comp b
    ((hasDerivAt_id b).const_sub a)
  simpa only [mul_one, mul_neg_one, sub_eq_add_neg] using! (hp.add hm).div_const 2

/-- The concrete Euclidean gradient, with its two first partial derivatives. -/
noncomputable def scalarGateGradient (profile : GateProfile) (tau : ℝ)
    (v : GatePlane) : GatePlane :=
  WithLp.toLp 2 ![
    (gate profile tau (v 0 + v 1) - gate profile tau (v 0 - v 1)) / 2,
    (gate profile tau (v 0 + v 1) + gate profile tau (v 0 - v 1)) / 2]

/-- The coordinate description is exactly the vector of concrete partials. -/
theorem scalarGateGradient_coordinates (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    scalarGateGradient profile tau v = WithLp.toLp 2 ![
      deriv (fun a => scalarGate profile tau a (v 1)) (v 0),
      deriv (fun b => scalarGate profile tau (v 0) b) (v 1)] := by
  rw [(scalarGate_partial_a profile htau (v 0) (v 1)).deriv,
    (scalarGate_partial_b profile htau (v 0) (v 1)).deriv]
  rfl

/-- The full Euclidean Fréchet derivative of the concrete gate gradient is
exactly the matrix verified in GateCurvature.lean. -/
theorem scalarGateGradient_hasFDerivAt (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    HasFDerivAt (scalarGateGradient profile tau)
      (gateHessianCLM (profile.rho ((v 0 + v 1) / tau))
        (profile.rho ((v 0 - v 1) / tau))) v := by
  let p0 : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 1
  let A := profile.rho ((v 0 + v 1) / tau)
  let B := profile.rho ((v 0 - v 1) / tau)
  have hp := (gate_hasDerivAt profile htau (v 0 + v 1)).comp_hasFDerivAt v
    ((p0.hasFDerivAt).add p1.hasFDerivAt)
  have hm := (gate_hasDerivAt profile htau (v 0 - v 1)).comp_hasFDerivAt v
    ((p0.hasFDerivAt).sub p1.hasFDerivAt)
  let d0 : GatePlane →L[ℝ] ℝ := (1 / 2 : ℝ) • (A • (p0 + p1) - B • (p0 - p1))
  let d1 : GatePlane →L[ℝ] ℝ := (1 / 2 : ℝ) • (A • (p0 + p1) + B • (p0 - p1))
  have h0 : HasFDerivAt
      (fun w : GatePlane => (1 / 2 : ℝ) *
        (gate profile tau (w 0 + w 1) - gate profile tau (w 0 - w 1))) d0 v := by
    simpa [d0, A, B, p0, p1, Function.comp_def] using (hp.sub hm).const_mul (1 / 2 : ℝ)
  have h1 : HasFDerivAt
      (fun w : GatePlane => (1 / 2 : ℝ) *
        (gate profile tau (w 0 + w 1) + gate profile tau (w 0 - w 1))) d1 v := by
    simpa [d1, A, B, p0, p1, Function.comp_def] using (hp.add hm).const_mul (1 / 2 : ℝ)
  have hpi : HasFDerivAt
      (fun w : GatePlane => ![
        (1 / 2 : ℝ) * (gate profile tau (w 0 + w 1) - gate profile tau (w 0 - w 1)),
        (1 / 2 : ℝ) * (gate profile tau (w 0 + w 1) + gate profile tau (w 0 - w 1))])
      (ContinuousLinearMap.pi ![d0, d1]) v := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact h0
    · exact h1
  let L : (Fin 2 → ℝ) →L[ℝ] GatePlane :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap
  have hresult := L.hasFDerivAt.comp v hpi
  convert! hresult using 1
  · ext w i
    fin_cases i <;> simp [scalarGateGradient, L] <;> ring
  · ext w i
    fin_cases i <;>
      simp [L, d0, d1, A, B, p0, p1, gateHessianCLM, gateHessianLinear,
        gateHessianAction, ContinuousLinearMap.comp_apply] <;> ring

/-- The displayed vector is the true Euclidean gradient of the concrete
scalar gate, identified through its full Fréchet derivative. -/
theorem scalarGate_hasFDerivAt_gradient (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    HasFDerivAt (fun w : GatePlane => scalarGate profile tau (w 0) (w 1))
      (innerSL ℝ (scalarGateGradient profile tau v)) v := by
  let p0 : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : GatePlane →L[ℝ] ℝ := EuclideanSpace.proj 1
  have hp := (doubleGate_hasDerivAt profile htau (v 0 + v 1)).comp_hasFDerivAt v
    ((p0.hasFDerivAt).add p1.hasFDerivAt)
  have hm := (doubleGate_hasDerivAt profile htau (v 0 - v 1)).comp_hasFDerivAt v
    ((p0.hasFDerivAt).sub p1.hasFDerivAt)
  have h := (hp.sub hm).const_mul (1 / 2 : ℝ)
  convert! h using 1
  · ext w
    simp [scalarGate, Function.comp_def, p0, p1]
    ring
  · ext w
    simp [innerSL_apply_apply, PiLp.inner_apply, Fin.sum_univ_two,
      scalarGateGradient, p0, p1]
    ring

/-- The actual gradient Jacobian has operator norm at most one. -/
theorem scalarGateGradient_fderiv_norm_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    ‖fderiv ℝ (scalarGateGradient profile tau) v‖ ≤ 1 := by
  rw [(scalarGateGradient_hasFDerivAt profile htau v).fderiv]
  exact gateHessian_opNorm_le (profile.range _).1 (profile.range _).2
    (profile.range _).1 (profile.range _).2

/-- The actual operator-valued second Fréchet derivative is the Riesz lift
of the explicit Euclidean Hessian action. -/
theorem scalarGate_hasFDerivAt_fderiv (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    HasFDerivAt
      (fderiv ℝ (fun w : GatePlane => scalarGate profile tau (w 0) (w 1)))
      ((innerSL ℝ).comp
        (gateHessianCLM (profile.rho ((v 0 + v 1) / tau))
          (profile.rho ((v 0 - v 1) / tau)))) v := by
  have hfun : fderiv ℝ (fun w : GatePlane => scalarGate profile tau (w 0) (w 1)) =
      fun w => innerSL ℝ (scalarGateGradient profile tau w) := by
    funext w
    exact (scalarGate_hasFDerivAt_gradient profile htau w).fderiv
  rw [hfun]
  exact (innerSL ℝ).hasFDerivAt.comp v
    (scalarGateGradient_hasFDerivAt profile htau v)

/-- Consequently the concrete scalar gate's second Fréchet derivative has
operator norm at most one in the Euclidean metric used by the manuscript. -/
theorem scalarGate_second_fderiv_norm_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v : GatePlane) :
    ‖fderiv ℝ (fderiv ℝ (fun w : GatePlane => scalarGate profile tau (w 0) (w 1))) v‖ ≤ 1 := by
  rw [(scalarGate_hasFDerivAt_fderiv profile htau v).fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_norm, one_mul]
  exact gateHessian_norm_le (profile.range _).1 (profile.range _).2
    (profile.range _).1 (profile.range _).2 w

/-- Integrating the actual Jacobian bound makes the concrete gradient globally
one-Lipschitz, as required by the gate-block contraction construction. -/
theorem scalarGateGradient_norm_sub_le (profile : GateProfile) {tau : ℝ}
    (htau : tau ≠ 0) (v w : GatePlane) :
    ‖scalarGateGradient profile tau w - scalarGateGradient profile tau v‖ ≤ ‖w - v‖ := by
  simpa only [one_mul] using
    (convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (x := v) (y := w) (C := (1 : ℝ))
      (fun u _ => (scalarGateGradient_hasFDerivAt profile htau u).differentiableAt)
      (fun u _ => scalarGateGradient_fderiv_norm_le profile htau u)
      (Set.mem_univ v) (Set.mem_univ w))

end MinimaxAudit
