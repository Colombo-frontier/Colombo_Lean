import HeavyTail.OnlineMasterTuning

/-! The generic online master is dominated by the conservative stage
normalization, including its smaller comparator-net error. -/
noncomputable section
namespace HeavyTail

theorem generic_online_small_master_bound {C p M V s R ell n D₀ Llog : ℝ}
    (hC : 0 ≤ C) (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s)
    (hR : 0 < R) (hell : 1 ≤ ell) (hn : 0 < n)
    (hD : D₀ ≤ R ^ 2 / (2 * (onlineSmoothing R ell) ^ 2) +
      onlineQuadratic (onlineStep p M V s R ell n) M R n * R ^ 2 / 2)
    (hlog : Llog ≤ 2 * ell) :
    let η := onlineStep p M V s R ell n
    let a := onlineSmoothing R ell
    let β := onlineQuadratic η M R n
    let ε := onlineResidual η M R n
    (D₀ + n * (η ^ 2 * M ^ 2 / (2 * β) + ε) +
      2 * (n * (C * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))) + Llog)) / (η * n) +
      M * R / (8 * n) ≤ onlineMaster C p M V s R ell n := by
  let η := onlineStep p M V s R ell n
  let a := onlineSmoothing R ell
  let β := onlineQuadratic η M R n
  let ε := onlineResidual η M R n
  let ν := C * (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2))
  have hη : 0 < η := onlineStep_pos hM hV hs hR (lt_of_lt_of_le zero_lt_one hell) hn
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hnν := mul_nonneg hn.le hν
  have hnum : D₀ + n * (η ^ 2 * M ^ 2 / (2 * β) + ε) + 2 * (n * ν + Llog) ≤
      R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 +
        n * (η ^ 2 * M ^ 2 / (2 * β) + ε) + 8 * n * ν + 4 * ell := by
    change D₀ ≤ R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 at hD
    linarith only [hD, hlog, hnν]
  have hdiv := div_le_div_of_nonneg_right hnum (mul_pos hη hn).le
  have hnet : M * R / (8 * n) ≤ M * R / (2 * n) := by
    apply div_le_div_of_nonneg_left (mul_pos hM hR).le (by positivity)
    linarith
  dsimp only
  change _ ≤ (R ^ 2 / (2 * a ^ 2) + β * R ^ 2 / 2 +
    n * (η ^ 2 * M ^ 2 / (2 * β) + ε) + 8 * n * C *
      (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2)) + 4 * ell) / (η * n) + M * R / (2 * n)
  have he : 8 * n * ν = 8 * n * C *
      (η ^ p * (s * R) ^ p + η ^ 2 * a ^ 2 * (V + M ^ 2)) := by dsimp [ν]; ring
  rw [he] at hdiv
  exact add_le_add hdiv hnet

theorem tunedOnlineResidual_pos {p M V s R ell n : ℝ}
    (hM : 0 < M) (hV : 0 ≤ V) (hs : 0 < s) (hR : 0 < R)
    (hell : 0 < ell) (hn : 0 < n) :
    0 < onlineResidual (onlineStep p M V s R ell n) M R n := by
  have hη := onlineStep_pos (p := p) hM hV hs hR hell hn
  unfold onlineResidual
  positivity

end HeavyTail
