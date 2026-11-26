import RationalTiltRadius254

noncomputable section
open Matrix
namespace Paper254

def uniformHistoryRadius (d : ℕ) (D hi G lam : ℝ) := D+(5/4)*lam*(d:ℝ)^3*hi*G+1

def actualHistoryLocalError (d : ℕ) (D lo hi G lam : ℝ)
    (cfg : RationalHistoryParameters) (h : ℝ) :=
  numericalKLError d lo D (max 1 ((d:ℝ)^2/lo)) ((1/hi)^d)
    (historyPrecisionError d lo cfg h)
    (historyMeanError d lo hi (uniformHistoryRadius d D hi G lam) cfg h)

theorem rationalHistoryStep_one_step {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (hD : 0≤D) (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi G : ℝ) (hlo : 0<lo) (hhi : 0<hi) (hG : 0≤G)
    (hlohi : lo≤hi) (hguard : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (hlam : 0≤(lam:ℝ))
    (g w : Fin d→ℚ) (hg : ∀ i,|(g i:ℝ)|≤G)
    (hsmall : |2*(lam:ℝ)*((fun j=>(g j:ℝ)) ⬝ᵥ
      ((fun j=>(S.mean j:ℝ))-(fun j=>(w j:ℝ))))|≤1/4)
    (h : ℝ) (hh : 0≤h) (hl : |(cfg.lowerThreshold:ℝ)-lo|≤h)
    (hu : |(cfg.upperThreshold:ℝ)-hi|≤h) :
    let hs := rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard S hS lam g w
    let N := (rationalHistoryStep oracle cfg S lam g w).gaussian hs.covariance_pos
    ∀ u : W.carrier,(lam:ℝ)*(coordinateSurrogate (2*(lam:ℝ)) (fun j=>(g j:ℝ))
        (fun j=>(w j:ℝ)) (fun j=>(S.mean j:ℝ))-
      smoothedCoordinateSurrogate (2*(lam:ℝ)) lo (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ)) u.val)≤
      (S.gaussian hS.covariance_pos).potential lo u.val-N.potential lo u.val+
        actualHistoryLocalError d D lo hi G (lam:ℝ) cfg h := by
  let R := uniformHistoryRadius d D hi G (lam:ℝ)
  have hR : 0≤R := by dsimp [R,uniformHistoryRadius]; positivity
  have hc := rationalTiltMean_uniform_radius W lo hi G hhi.le hG S hS lam hlam g w hg hsmall
    cfg.storagePrecision
  have hk := rationalHistoryStep_local_KL hd W hD oracle hspec cfg lo hi hlo hhi hlohi hguard
    S hS lam hlam g w h R hh hR hl hu hc
  dsimp only at hk ⊢
  intro u
  have hs := (S.gaussian hS.covariance_pos).history_one_step W (lam:ℝ) lo hlam hlo
    (fun j=>(g j:ℝ)) (fun j=>(w j:ℝ)) u hsmall
  have he := (abs_le.mp (hk u)).1
  change _≤_+actualHistoryLocalError d D lo hi G (lam:ℝ) cfg h
  change -actualHistoryLocalError d D lo hi G (lam:ℝ) cfg h≤_ at he
  dsimp only [RationalHistoryData.gaussian] at hs he ⊢
  linarith only [hs,he]

end Paper254
#print axioms Paper254.rationalHistoryStep_one_step
