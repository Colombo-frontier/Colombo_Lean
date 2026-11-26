import UniformHistoryGuards254

namespace Paper254

structure RationalHistoryInvariant {d : ℕ} {D : ℝ} (W : Domain d D) (lo hi : ℝ)
    (S : RationalHistoryData d) : Prop where
  covariance_pos : (realMatrix S.covariance).PosDef
  covariance_lower : ∀ x : Space d,lo*‖x‖^2≤matrixQuadratic (realMatrix S.covariance) x
  covariance_upper : ∀ x : Space d,matrixQuadratic (realMatrix S.covariance) x≤hi*‖x‖^2
  feasible : WithLp.toLp 2 (fun j=>(S.mean j:ℝ))∈W.carrier

theorem rationalHistoryStep_preserves {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hguard : UniformHistoryGuards d cfg lo hi) (S : RationalHistoryData d)
    (hS : RationalHistoryInvariant W lo hi S) (lam : ℚ) (g w : Fin d→ℚ) :
    RationalHistoryInvariant W lo hi (rationalHistoryStep oracle cfg S lam g w) := by
  obtain ⟨U,c,hC,hc⟩ := rationalTiltCovariance_spectrum S hS.covariance_pos lo hi hlo hhi
    hS.covariance_lower hS.covariance_upper lam g
  have hs := rationalHistoryStep_feasible_of_guards hd W oracle hspec cfg S hS.covariance_pos
    lam g w U c hC hguard.dimension hguard.smoothing_pos hguard.smoothing_lower
    (fun j=>hguard.lower_spectral (c j) (hc j).1.le (hc j).2)
    (fun j=>hguard.upper_spectral (c j) (hc j).1.le (hc j).2)
    lo hi hlo hhi hguard.thresholds hguard.lower_margin hguard.upper_margin hguard.metric
  exact ⟨hs.1,fun x=>(hs.2.1 x).1,fun x=>(hs.2.1 x).2,hs.2.2⟩

/-- Inputs may depend on the actual current rounded state. -/
def rationalHistoryRun {d : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (initial : RationalHistoryData d) (lam : ℚ)
    (input : ℕ→RationalHistoryData d→(Fin d→ℚ)×(Fin d→ℚ)) : ℕ→RationalHistoryData d
  | 0 => initial
  | t+1 => let S := rationalHistoryRun oracle cfg initial lam input t
           let z := input t S
           rationalHistoryStep oracle cfg S lam z.1 z.2

theorem rationalHistoryRun_invariant {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (cfg : RationalHistoryParameters) (lo hi : ℝ) (hlo : 0<lo) (hhi : 0<hi)
    (hguard : UniformHistoryGuards d cfg lo hi) (initial : RationalHistoryData d)
    (hinit : RationalHistoryInvariant W lo hi initial) (lam : ℚ)
    (input : ℕ→RationalHistoryData d→(Fin d→ℚ)×(Fin d→ℚ)) :
    ∀ t,RationalHistoryInvariant W lo hi (rationalHistoryRun oracle cfg initial lam input t) := by
  intro t
  induction t with
  | zero => exact hinit
  | succ t ih =>
    exact rationalHistoryStep_preserves hd W oracle hspec cfg lo hi hlo hhi hguard _ ih lam _ _

theorem rationalHistoryRun_uniform {d : ℕ} (hd : 0<d) {D : ℝ} (W : Domain d D)
    (oracle : RationalProjectionProcedure d) (hspec : RationalProjectionSpec W oracle)
    (a b r p : ℕ) (hdim : (d:ℝ)≤(2:ℝ)^a) (lo hi : ℚ) (hlo : 0<(lo:ℝ))
    (hhi : (hi:ℝ)≤(2:ℝ)^b) (hgap : ((2:ℝ)^r)⁻¹≤(hi:ℝ)-(lo:ℝ))
    (initial : RationalHistoryData d) (hinit : RationalHistoryInvariant W (lo:ℝ) (hi:ℝ) initial)
    (lam : ℚ) (input : ℕ→RationalHistoryData d→(Fin d→ℚ)×(Fin d→ℚ)) :
    ∀ t,RationalHistoryInvariant W (lo:ℝ) (hi:ℝ)
      (rationalHistoryRun oracle (uniformHistoryParameters a b r p lo hi) initial lam input t) := by
  have hhi0 : 0<(hi:ℝ) := by linarith [show 0<((2:ℝ)^r)⁻¹ by positivity]
  exact rationalHistoryRun_invariant hd W oracle hspec _ _ _ hlo hhi0
    (uniformHistoryParameters_guards d a b r p hd hdim lo hi hlo hhi hgap) initial hinit lam input

theorem rationalHistoryRun_causal {d : ℕ} (oracle : RationalProjectionProcedure d)
    (cfg : RationalHistoryParameters) (initial : RationalHistoryData d) (lam : ℚ)
    (input other : ℕ→RationalHistoryData d→(Fin d→ℚ)×(Fin d→ℚ)) (n : ℕ)
    (h : ∀ t<n,∀ S,input t S=other t S) :
    rationalHistoryRun oracle cfg initial lam input n=rationalHistoryRun oracle cfg initial lam other n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun t ht=>h t (by omega))
    simp only [rationalHistoryRun,hn,h n (by omega)]

end Paper254
#print axioms Paper254.rationalHistoryRun_uniform
#print axioms Paper254.rationalHistoryRun_causal
