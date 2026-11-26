import RationalOneStep254
import GaussianBirth254

noncomputable section
open scoped BigOperators
open Matrix
namespace Paper254

theorem rationalHistory_movement {d : ℕ} {D : ℝ} (W : Domain d D) (lo hi : ℝ)
    (hlo : 0<lo) (hhi : 0<hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (u v : Space d) :
    Real.sqrt ((S.gaussian hS.covariance_pos).potential lo v)≤
      Real.sqrt ((S.gaussian hS.covariance_pos).potential lo u)+‖v-u‖/(Real.sqrt 2*Real.sqrt lo) := by
  apply rounded_history_movement _ lo hlo
  have hb := precision_bounds_from_covariance _ hS.covariance_pos lo hi hlo hhi
    hS.covariance_lower hS.covariance_upper
  exact fun x=>(hb.1 x).2

theorem rationalHistoryInitial_gaussian {d : ℕ} (m : Fin d→ℚ) (H : ℚ) (D : ℝ)
    (hD : 0<D) (hHD : (H:ℝ)=D^2)
    (hC : (realMatrix (rationalHistoryInitial m H).covariance).PosDef) :
    (rationalHistoryInitial m H).gaussian hC=isotropicGaussian (fun j=>(m j:ℝ)) D hD := by
  have hc : realMatrix (rationalHistoryInitial m H).covariance=
      Matrix.diagonal (fun _ : Fin d=>D^2) := by
    rw [show realMatrix (rationalHistoryInitial m H).covariance=(H:ℝ) • (1:Precision d) from realMatrix_scalar H,hHD]
    ext i j
    simp [Matrix.one_apply,Matrix.diagonal_apply]
  cases h : (rationalHistoryInitial m H).gaussian hC
  simp only [RationalHistoryData.gaussian] at h
  cases h
  unfold isotropicGaussian
  congr 1
  rw [hc,Matrix.inv_diagonal]
  let z : (Fin d→ℝ)ˣ := ⟨fun _=>D^2,fun _=>1/D^2,
    by ext i; dsimp; field_simp,
    by ext i; dsimp; field_simp⟩
  have hz : Ring.inverse (fun _ : Fin d=>D^2)=(fun _=>1/D^2) := Ring.inverse_unit z
  rw [hz]

theorem rationalHistoryInitial_birth {d : ℕ} {D : ℝ} (W : Domain d D) (hD : 0<D)
    (m : Fin d→ℚ) (hm : WithLp.toLp 2 (fun j=>(m j:ℝ))∈W.carrier)
    (H : ℚ) (hHD : (H:ℝ)=D^2)
    (hC : (realMatrix (rationalHistoryInitial m H).covariance).PosDef)
    (q : ℝ) (hq : 0<q) (u : W.carrier) :
    ((rationalHistoryInitial m H).gaussian hC).potential q u.val≤birthBudget d D q := by
  rw [rationalHistoryInitial_gaussian m H D hD hHD hC]
  exact isotropicGaussian_birth_bound W hD ⟨WithLp.toLp 2 (fun j=>(m j:ℝ)),hm⟩ u q hq

end Paper254
#print axioms Paper254.rationalHistoryInitial_birth
#print axioms Paper254.rationalHistory_movement
