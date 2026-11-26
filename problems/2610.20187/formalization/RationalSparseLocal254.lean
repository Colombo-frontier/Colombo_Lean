import RationalSparseConstruction254

noncomputable section
namespace Paper254
namespace RationalSparseConstruction
variable {d T K : ℕ} {D G eta : ℝ} {W : Domain d D}
variable (C : RationalSparseConstruction d T K D G eta W)

def smoothedLoss (u : ℕ → W.carrier) (k : Fin (K+1)) (t : ℕ) : ℝ :=
  smoothedCoordinateSurrogate (2*(C.lam : ℝ)) (C.lo k : ℝ)
    (fun j => (C.gradient t j : ℝ)) (fun j => (C.prediction t j : ℝ)) (u t).val

def regretCharge (u : ℕ → W.carrier) (k : Fin (K+1)) (t : ℕ) : ℝ :=
  coordinateSurrogate (2*(C.lam : ℝ)) (fun j => (C.gradient t j : ℝ))
    (fun j => (C.prediction t j : ℝ)) (fun j => (C.prediction t j : ℝ))-C.smoothedLoss u k t

def historyCharge (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ) : ℝ :=
  coordinateSurrogate (2*(C.lam : ℝ)) (fun j => (C.gradient t j : ℝ))
    (fun j => (C.prediction t j : ℝ)) (fun j => ((C.run t).histories (C.expert i k)).mean j)-
      C.smoothedLoss u k t

def prePotential (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ) : ℝ :=
  (C.gaussian i t k).potential (C.lo k : ℝ) (u t).val

def postPotential (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ) : ℝ :=
  (C.gaussian i (t+1) k).potential (C.lo k : ℝ) (u t).val

def movementLength (_ : RationalSparseConstruction d T K D G eta W)
    (u : ℕ → W.carrier) (t : ℕ) : ℝ := ‖(u (t+1)).val-(u t).val‖

theorem local_step (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ)
    (hit : i ≤ t) (ht : t < T) (halive : HistoryActive (t+1) (i+1)) :
    (C.lam : ℝ)*C.historyCharge u k i t ≤ C.prePotential u k i t-C.postPotential u k i t+
      C.localError k := by
  have hg : ∀ j, |(C.gradient t j : ℝ)| ≤ G := by
    intro j
    simpa only [Real.norm_eq_abs] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ))) j).trans (C.gradient_bound t)
  have hsmall : |2*(C.lam : ℝ)*((fun j => (C.gradient t j : ℝ)) ⬝ᵥ
      ((fun j => (((C.run t).histories (C.expert i k)).mean j : ℝ))-(fun j => (C.prediction t j : ℝ))))| ≤ 1/4 := by
    rw [C.lam_eq]
    exact coordinate_curvature_bound W C.diameter_pos C.gradient_pos C.curvature_pos _
      (C.gradient_bound t) ⟨_,(C.history_invariant i t k).feasible⟩ ⟨_,C.prediction_feasible t⟩
  have hs := rationalHistoryStep_one_step C.dimension_pos W C.diameter_pos.le C.oracle C.oracle_spec
    (C.cfg k) (C.lo k : ℝ) (C.hi : ℝ) G (C.lo_pos k) C.hi_pos C.gradient_pos.le
    (C.lo_le_hi k) (C.guards k) _ (C.history_invariant i t k) C.lam C.lam_pos.le
    (C.gradient t) (C.prediction t) hg hsmall (C.margin k) (C.margin_nonneg k)
    (C.lower_error k) (C.upper_error k) (u t)
  have he := rationalSparseRun_live_update C.oracle C.allCfg C.master_precision C.lam
    (standardRationalSchedule T K) C.initial C.query t (C.expert i k)
    (C.expert_live i t k (by omega) ht.le halive)
  change (C.run (t+1)).histories (C.expert i k)=
    rationalHistoryStep C.oracle (C.allCfg (C.expert i k)) ((C.run t).histories (C.expert i k))
      C.lam (C.gradient t) (C.prediction t) at he
  rw [C.expert_cfg] at he
  unfold historyCharge smoothedLoss prePotential postPotential gaussian localError
  simp only [he]
  exact hs

theorem potential_movement (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ) :
    Real.sqrt (C.prePotential u k i (t+1)) ≤ Real.sqrt (C.postPotential u k i t)+
      C.movementLength u t/(Real.sqrt 2*Real.sqrt (C.lo k : ℝ)) :=
  rationalHistory_movement W (C.lo k : ℝ) (C.hi : ℝ) (C.lo_pos k) C.hi_pos _
    (C.history_invariant i (t+1) k) (u t).val (u (t+1)).val

theorem regretCharge_sub_historyCharge (u : ℕ → W.carrier) (k : Fin (K+1)) (i t : ℕ) :
    C.regretCharge u k t-C.historyCharge u k i t=
      rationalSparseDifference C.lam (C.run t) (C.gradient t) (C.expert i k) := by
  unfold regretCharge historyCharge rationalSparseDifference rationalSparseSurrogate
  rw [show coordinateSurrogate (2*(C.lam : ℝ)) (fun j => (C.gradient t j : ℝ))
      (fun j => (C.prediction t j : ℝ)) (fun j => (C.prediction t j : ℝ))=
      rankOneSurrogate (2*(C.lam : ℝ)) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
        (WithLp.toLp 2 (fun j => (C.prediction t j : ℝ)))
        (WithLp.toLp 2 (fun j => (C.prediction t j : ℝ))) from coordinate_surrogate_eq _ _ _ _]
  rw [show coordinateSurrogate (2*(C.lam : ℝ)) (fun j => (C.gradient t j : ℝ))
      (fun j => (C.prediction t j : ℝ)) (fun j => ((C.run t).histories (C.expert i k)).mean j)=
      rankOneSurrogate (2*(C.lam : ℝ)) (WithLp.toLp 2 (fun j => (C.gradient t j : ℝ)))
        (WithLp.toLp 2 (fun j => (C.prediction t j : ℝ)))
        (WithLp.toLp 2 (fun j => ((C.run t).histories (C.expert i k)).mean j)) from coordinate_surrogate_eq _ _ _ _]
  change (_-C.smoothedLoss u k t)-(_-C.smoothedLoss u k t)=_
  dsimp only [prediction]
  ring

end RationalSparseConstruction
end Paper254
#print axioms Paper254.RationalSparseConstruction.local_step
#print axioms Paper254.RationalSparseConstruction.potential_movement
