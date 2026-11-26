import RationalSparseMain254
import ExplicitCurved254

noncomputable section
namespace Paper254

theorem clipped_numeric_explicit (D G eta R P delta : ℝ) (d T : ℕ)
    (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta) (hd : 0 < d) (hT : 0 < T)
    (hP : 0 ≤ P)
    (hsmall : P≤curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2))
    (hreg : ∀ tau : ℝ, D/T≤tau → tau≤D →
      R≤2048*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
        Real.sqrt (d+1 : ℝ)*logFactor T^2/(curvature D G eta*tau)*P+
          curvature D G eta*G^2*T*tau^2)+delta) :
    R≤6144*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
      explicitCurvedRate (curvature D G eta) G d T P)+delta := by
  let gamma := curvature D G eta
  let Lambda := logFactor T
  let X := Real.sqrt (d+1 : ℝ)*Lambda^2*P/(gamma^2*G^2*T)
  let root := X^(1/3 : ℝ)
  let tau := max (D/T) root
  have hgamma : 0<gamma := curvature_pos D G eta hD hG heta
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hT1 : (1 : ℝ)≤T := by exact_mod_cast hT
  have hL := logFactor_ge_one T hT
  have hden : 0<gamma^2*G^2*T := by positivity
  have hX0 : 0≤X := by dsimp [X]; positivity
  have hr : 0≤root := Real.rpow_nonneg hX0 _
  have hr3 : root^3=X := third_rpow_cube X hX0
  have hXD : X≤D^3 := by
    have hs := (le_div_iff₀ (show 0<Real.sqrt (d+1 : ℝ)*logFactor T^2 by positivity)).mp hsmall
    apply (div_le_iff₀ hden).mpr
    change P*(Real.sqrt (d+1 : ℝ)*Lambda^2)≤gamma^2*G^2*T*D^3 at hs
    nlinarith
  have hrD : root≤D := nonneg_le_of_cube_le _ _ hr hD.le (by rw [hr3]; exact hXD)
  have hlo : D/T≤tau := le_max_left _ _
  have hhi : tau≤D := max_le ((div_le_iff₀ hTr).mpr (by nlinarith)) hrD
  have hbal : gamma^2*G^2*T*root^3=Real.sqrt (d+1 : ℝ)*Lambda^2*P := by
    rw [hr3]
    dsimp [X]
    field_simp
  have hb : (Real.sqrt (d+1 : ℝ)*Lambda^2/gamma)*P=(gamma*G^2*T)*root^3 := by
    rw [div_mul_eq_mul_div]
    apply (div_eq_iff (ne_of_gt hgamma)).mpr
    convert hbal.symm using 1 <;> ring
  have hcost := clipped_balance_cost (Real.sqrt (d+1 : ℝ)*Lambda^2/gamma) (gamma*G^2*T) P
    (D/T) root (by positivity) (by positivity) hP (div_pos hD hTr) hr hb
  have hexact := balanced_term_exact gamma G root P d T hgamma hG hT hP hr hbal
  have hfloor := explicit_floor_bound D G gamma d T hD hG hgamma hd hT
    (curvature_times_radius D G eta hD hG)
  have hbound := hreg tau hlo hhi
  change R≤2048*((d+1 : ℝ)*Lambda^2/gamma+
    Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau)*P+gamma*G^2*T*tau^2)+delta at hbound
  change (Real.sqrt (d+1 : ℝ)*Lambda^2/gamma)*P/tau+gamma*G^2*T*tau^2≤
    3*(gamma*G^2*T)*root^2+2*(gamma*G^2*T)*(D/T)^2 at hcost
  have he : (Real.sqrt (d+1 : ℝ)*Lambda^2/gamma)*P/tau=
      Real.sqrt (d+1 : ℝ)*Lambda^2/(gamma*tau)*P := by ring
  rw [he] at hcost
  change gamma*G^2*T*(D/T)^2≤(d+1 : ℝ)*Lambda^2/gamma at hfloor
  change R≤6144*((d+1 : ℝ)*Lambda^2/gamma+explicitCurvedRate gamma G d T P)+delta
  nlinarith

/-- Dimension-sharp curved regret of the actual rational sparse learner,
including data-independent numerical precision selection. -/
theorem exists_rational_sparse_curved {d T : ℕ} (hd : 0 < d) (hT : 2 ≤ T)
    {D G eta : ℝ} (W : Domain d D) (hD : 0 < D) (hG : 0 < G) (heta : 0 < eta)
    (a b : ℕ) (hdim : (d : ℝ)≤(2 : ℝ)^a)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (hi : ℚ) (hhi : (hi : ℝ)=D^2) (hhib : (hi : ℝ)≤(2 : ℝ)^b)
    (lam : ℚ) (hlam : 2*(lam : ℝ)=curvature D G eta)
    (w0 : Fin d → ℚ) (hw0 : WithLp.toLp 2 (fun j => (w0 j : ℝ))∈W.carrier)
    (query : ℕ → RationalGradientQuery d)
    (hquery : ∀ t w, WithLp.toLp 2 (fun j => (w j : ℝ))∈W.carrier →
      ‖WithLp.toLp 2 (fun j => (query t w j : ℝ))‖≤G)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : RationalSparseConstruction d T (scaleCount T) D G eta W,
      C.oracle=oracle ∧ C.initial_mean=w0 ∧ C.query=query ∧ C.lam=lam ∧
      ∀ f : ℕ → Loss d, (∀ t < T, ExpConcaveOn eta W.carrier (f t)) →
        (∀ t < T, HasGradientWithinAt (f t) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
          W.carrier (C.playedPoint t).val) →
        ∀ u : ℕ → W.carrier,
          intervalCharge (C.movementLength u) 0 (T-1)≤
            curvature D G eta^2*G^2*T*D^3/(Real.sqrt (d+1 : ℝ)*logFactor T^2) →
          C.cumulativeRegret f u≤6144*((d+1 : ℝ)*logFactor T^2/curvature D G eta+
            explicitCurvedRate (curvature D G eta) G d T
              (intervalCharge (C.movementLength u) 0 (T-1)))+delta := by
  obtain ⟨C,hCo,hCw,hCq,hClam,hbound⟩ := exists_rational_sparse_clipped hd hT W hD hG heta
    a b hdim oracle hspec hi hhi hhib lam hlam w0 hw0 query hquery delta hdelta
  refine ⟨C,hCo,hCw,hCq,hClam,?_⟩
  intro f hf hder u hsmall
  exact clipped_numeric_explicit D G eta (C.cumulativeRegret f u)
    (intervalCharge (C.movementLength u) 0 (T-1)) delta d T hD hG heta hd (by omega)
    (intervalCharge_nonneg _ (fun _ => norm_nonneg _) _ _) hsmall (hbound f hf hder u)

end Paper254
#print axioms Paper254.exists_rational_sparse_curved
