import Bilevel.MultiscaleBoundedGapNormalization
import Bilevel.MultiscaleBoundedGapScale
import Bilevel.MultiscaleBoundedGapParameters

/-! A single actual macro-free primitive, response and gap certificate on
the full curvature-class accuracy window in the bounded-gap branch.
No execution, observer, or query lower bound is asserted here. -/
noncomputable section
namespace Bilevel.MultiscaleMean
open CompensatedMean Filter
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem bounded_gap_witness : ∃ A K η C c : ℝ,
    ∃ hA : 1≤A,∃ hK : 1≤K,∃ hη : 0<η,∃ hη1 : η≤1,
    1≤C ∧ 0<c ∧ c≤1 ∧
    ∀ (L Δ κ θ ε : ℝ) (hL : 0<L) (_hΔ : 0<Δ) (_hΔL : Δ≤L) (hκ : 2*A≤κ)
      (hθ : 1≤θ) (_hθκ : θ≤κ) (_hε : 0<ε),
      ε≤c*min L (κ*Real.sqrt (L*Δ)) →
      let β := innerWidth A η ε κ L
      let T := innerLength η L Δ β
      let n := T-1
      ∃ hβ : 0<β,β*θ≤1 ∧ 256≤T ∧ n+1=T ∧
      (η/(2048*A^4))*L*κ^2*Δ/ε^2≤(T:ℝ) ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
        [FiniteDimensional ℝ E] (U : ZeroChain.Space n →ₗᵢ[ℝ] E),
      let P := innerParameters n (2*(L/κ)) (L/A) η β θ K
        (by
          have hk : 0<κ := by linarith
          positivity)
        (by positivity) hη.le hη1 hβ hθ hK U
      ∃ Q : Model.Primitive (X:=E) (Y:=LowerSpace E) (L/κ) L L L ((L/κ)*θ),
      ∃ r : Q.Response,
        Q.f=P.data.upper ∧ Q.g=P.data.lower ∧ r.y=P.data.response ∧
        Q.hyperobjective r=P.realized ∧ r.y 0=0 ∧
        Nonempty (Q.GapCertificate r 0 Δ) ∧
        Tendsto (Q.hyperobjective r) (cocompact E) atTop ∧
        (∀ x z,‖gradient (Q.hyperobjective r) x-gradient (Q.hyperobjective r) z‖≤
          (C*L*κ^2)*‖x-z‖) ∧
        (∀ x,|WrappedChain.coordinates n P.R P.U ((κ/(2*A)) • x) (Fin.last n)|<β →
          8*ε≤‖gradient (Q.hyperobjective r) x‖) := by
  obtain ⟨A,K,η,τ,C,hA,hK,hη,hη1,hτ,hC,hfamily⟩ := bounded_gap_normalized_family
  obtain ⟨c,hc,hc1,hscale⟩ := inner_scale_certificate hA hη hη1 (show 0<min τ 1 by positivity)
  refine ⟨A,K,η,C,c,hA,hK,hη,hη1,hC,hc,hc1,?_⟩
  intro L Δ κ θ ε hL hΔ hΔL hκ hθ hθκ hε hacc
  dsimp only
  have hAp : 0<A := by linarith
  have hκp : 0<κ := by linarith
  let β := innerWidth A η ε κ L
  let T := innerLength η L Δ β
  let n := T-1
  obtain ⟨hβ,hβθ,hT,hn,henergy,hcount⟩ :=
    hscale L Δ κ θ ε hL hΔ hκp hθ hθκ hε hacc
  change 0<β at hβ
  refine ⟨hβ,hβθ.trans (min_le_right _ _),hT,hn,hcount,?_⟩
  intro E _ _ _ _ U
  let P := innerParameters n (2*(L/κ)) (L/A) η β θ K
    (by positivity) (by positivity) hη.le hη1 hβ hθ hK U
  have hμ : 0<L/κ := div_pos hL hκp
  have hcond : 2*A*(L/κ)≤L := by
    have hh := mul_le_mul_of_nonneg_right hκ hμ.le
    have he : κ*(L/κ)=L := by field_simp
    simpa only [he] using hh
  have henergy' : (n+1:ℕ)*P.η*P.L*P.β^2≤Δ/A := by
    have hh := div_le_div_of_nonneg_right henergy hAp.le
    change ((T:ℝ)*η*L*β^2)/A≤Δ/A at hh
    have hnt : n+1=T := hn
    rw [hnt]
    convert hh using 1
    dsimp [P,innerParameters]
    ring
  obtain ⟨Q,r,hf,hg,hr,hobj,hzero,hgap,hcoerc,hcurv,hblind⟩ :=
    hfamily E n P (L/κ) L Δ hμ hL hΔ.le hΔL hcond rfl rfl rfl rfl rfl rfl (hβθ.trans (min_le_left _ _)) henergy'
  refine ⟨Q,r,hf,hg,hr,hobj,hzero,hgap,hcoerc,?_,?_⟩
  · intro x z
    have he : L/(L/κ)=κ := by field_simp
    simpa only [he] using hcurv x z
  · intro x hx
    have hgain : P.L/P.μ=κ/(2*A) := by
      dsimp [P,innerParameters]
      field_simp
      ring
    have hm : (P.L/P.μ)*P.η*P.L*P.β/2=8*ε :=
      inner_margin_exact hAp hη hκp hL
    rw [←hm]
    apply hblind x
    simpa only [hgain] using hx

end Bilevel.MultiscaleMean
