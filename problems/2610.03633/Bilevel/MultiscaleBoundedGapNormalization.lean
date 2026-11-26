import Bilevel.MultiscaleAmplitudeCertificate
import Bilevel.MultiscaleMeanCurvature
import Bilevel.SmallGapNormalization

/-! The actual macro-free family fits the prescribed primitive budgets in
the bounded-gap branch. Its hyperobjective has dimension-free curvature
O(L kappa^2). The statement retains the displayed scalar objectives and
does not assert an information or query lower bound. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean Filter
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem bounded_gap_normalized_family : ∃ A K η τ C : ℝ,
    1≤A ∧ 1≤K ∧ 0<η ∧ η≤1 ∧ 0<τ ∧ 1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (n : ℕ) (P : Parameters (E:=E) n) (μ L Δ : ℝ),
      0<μ → 0<L → 0≤Δ → Δ≤L → 2*A*μ≤L →
      P.μ=2*μ → P.L=L/A → P.η=η → P.c=1/64 →
      P.R=K*P.β*Real.sqrt (n+1:ℕ) → P.ν=P.η*P.L/24 → P.β*P.θ≤τ →
      (n+1:ℕ)*P.η*P.L*P.β^2≤Δ/A →
      ∃ Q : Model.Primitive (X:=E) (Y:=LowerSpace E) μ L L L (μ*P.θ),
      ∃ r : Q.Response,
        Q.f=P.data.upper ∧ Q.g=P.data.lower ∧ r.y=P.data.response ∧
        Q.hyperobjective r=P.realized ∧ r.y 0=0 ∧
        Nonempty (Q.GapCertificate r 0 Δ) ∧
        Tendsto (Q.hyperobjective r) (cocompact E) atTop ∧
        (∀ x z,‖gradient (Q.hyperobjective r) x-gradient (Q.hyperobjective r) z‖≤
          (C*L*(L/μ)^2)*‖x-z‖) ∧
        (∀ x,|WrappedChain.coordinates n P.R P.U ((P.L/P.μ) • x) (Fin.last n)|<P.β →
          (P.L/P.μ)*P.η*P.L*P.β/2≤‖gradient (Q.hyperobjective r) x‖) := by
  obtain ⟨K,η,τ,LfC,CfC,hK,hη,hη1,hτ,hLfC,hCfC,hfamily⟩ :=
    amplitude_mean_family_certificate
  obtain ⟨C,hC,hcurv⟩ := actual_realized_curvature
  let G : ℝ := (1+2*Real.exp 1)*ZeroChain.phiBound
  have hG : 0≤G := by
    dsimp [G]
    exact mul_nonneg (by positivity) ZeroChain.phiBound_nonneg
  let A : ℝ := 3+LfC+2*CfC+G
  have hA : 1≤A := by dsimp [A]; linarith
  have hAp : 0<A := by linarith
  have hA3 : 3≤A := by dsimp [A]; linarith
  have hAf : LfC≤A := by dsimp [A]; linarith
  have hAc : 2*CfC≤A := by dsimp [A]; linarith
  have hAG : G≤A := by dsimp [A]; linarith
  refine ⟨A,K,η,τ,C,hA,hK,hη,hη1,hτ,hC,?_⟩
  intro E _ _ _ _ n P μ L Δ hμ hL hΔ hΔL hcond hPμ hPL hPη hc hR hν hscale henergy
  have hPLp := P.L_pos
  have hPμp := P.μ_pos
  have hPβp := P.β_pos
  have hμL : P.μ≤P.L := by
    rw [hPμ,hPL]
    apply (le_div_iff₀ hAp).mpr
    nlinarith only [hcond]
  have hηp : 0<P.η := hPη.symm ▸ hη
  have hηb : P.η≤η := hPη.le
  obtain ⟨⟨R⟩,hend⟩ := hfamily E n P (Δ/A) hμL hηp hηb hc hR hν hscale
    (div_nonneg hΔ hAp.le) henergy
  have hLf : LfC*P.L≤L := by
    rw [hPL]
    have hh := mul_le_mul_of_nonneg_right hAf (div_pos hL hAp).le
    have he : A*(L/A)=L := by field_simp
    simpa only [he] using hh
  have hLg : 3*P.L≤L := by
    rw [hPL]
    have hh := mul_le_mul_of_nonneg_right hA3 (div_pos hL hAp).le
    have he : A*(L/A)=L := by field_simp
    simpa only [he] using hh
  have hsmallgap : Δ/A≤P.L := by
    rw [hPL]
    exact div_le_div_of_nonneg_right hΔL hAp.le
  have hroot : Real.sqrt (P.L*(Δ/A))≤P.L :=
    Real.sqrt_le_iff.mpr ⟨hPLp.le,by nlinarith [mul_le_mul_of_nonneg_left hsmallgap hPLp.le]⟩
  have hCf : CfC*(P.L+Real.sqrt (P.L*(Δ/A)))≤L := by
    calc
      _ ≤ 2*CfC*P.L := by nlinarith [mul_le_mul_of_nonneg_left hroot hCfC.le]
      _ ≤ A*P.L := mul_le_mul_of_nonneg_right hAc hPLp.le
      _ = L := by rw [hPL]; field_simp
  have hμeq : P.μ/2=μ := by rw [hPμ]; ring
  let Q := R.primitive.rebudget μ L L L (μ*P.θ) hμ hμeq.ge hLf hLg hCf
    (by rw [hμeq])
  let r : Q.Response := { y:=R.response.y, minimizes:=R.response.minimizes }
  have hobj : Q.hyperobjective r=P.realized := R.objective_eq
  have hgap : P.amplitude*((1+2*Real.exp 1)*ZeroChain.phiBound*(n+1:ℕ))≤Δ := by
    calc
      _ = G*((n+1:ℕ)*P.η*P.L*P.β^2) := by dsimp [G,Parameters.amplitude]; ring
      _ ≤ G*(Δ/A) := mul_le_mul_of_nonneg_left henergy hG
      _ ≤ A*(Δ/A) := mul_le_mul_of_nonneg_right hAG (div_nonneg hΔ hAp.le)
      _ = Δ := by field_simp
  have hRad : P.β*Real.sqrt (n+1:ℕ)≤P.R := by
    rw [hR]
    have hh := mul_le_mul_of_nonneg_right hK (show 0≤P.β*Real.sqrt (n+1:ℕ) by positivity)
    nlinarith only [hh]
  have hνL : P.ν≤P.L := by
    rw [hν]
    have hh := mul_le_mul_of_nonneg_right P.η_le_one hPLp.le
    nlinarith
  have hPLL : P.L≤L := by
    rw [hPL]
    exact (div_le_self hL.le hA)
  have hgain : P.L/P.μ≤L/μ := by
    have hd : μ≤P.μ := by rw [hPμ]; linarith
    exact (div_le_div_of_nonneg_left hPLp.le hμ hd).trans
      (div_le_div_of_nonneg_right hPLL hμ.le)
  refine ⟨Q,r,R.f_eq,R.g_eq,R.response_eq,hobj,R.initial_response,?_,R.coercive,?_,?_⟩
  · exact ⟨{ floor:=R.gap.floor,lower_bound:=R.gap.lower_bound,gap:=R.gap.gap.trans hgap }⟩
  · intro x z
    rw [hobj]
    apply (hcurv E n P hRad hνL x z).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hs := pow_le_pow_left₀ (div_pos hPLp hPμp).le hgain 2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPLL (by linarith : 0≤C)) hs
      (sq_nonneg _) (by positivity)
  · intro x hx
    rw [hobj]
    exact hend x hx

end Bilevel.MultiscaleMean
