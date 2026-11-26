import Bilevel.PolishedLiteralUpperMicro
import Bilevel.PolishedLiteralSelection

/-! First two physical jets of the actual micro payload at width b. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential RadialWrapper

def coreJetConstant (C Cg Ch Dr A Cr : ℝ) : ℝ :=
  (phi 0+C*Cr+12*A)+(Cg+4*A)+(Ch+Dr*A+4*(Cg+4*A))

theorem coreJetConstant_nonneg {C Cg Ch Dr A Cr : ℝ}
    (hC : 0≤C) (hCg : 0≤Cg) (hCh : 0≤Ch) (hDr : 0≤Dr) (hA : 0≤A) (hCr : 0≤Cr) :
    0≤coreJetConstant C Cg Ch Dr A Cr := by
  unfold coreJetConstant
  have hp := phi_nonneg 0
  positivity

theorem wrapped_core_jets : ∃ C Cg Ch Dr : ℝ,0≤C ∧ 0≤Cg ∧ 0≤Ch ∧ 0≤Dr ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n : ℕ) (L β A ν b R Cr : ℝ),0<L → 0<β → 0≤A → 0≤ν → ν≤L →
      β≤b → b≤R → R≤Cr*b → 0≤Cr → β*Real.sqrt ((n:ℝ)+1)≤b →
      ∀ (V : Space n →ₗᵢ[ℝ] E) (u : E) (k : ℕ),k≤2 →
        ‖iteratedFDeriv ℝ k (rawCore n L β A ν b ∘ WrappedChain.coordinates n R V) u‖≤
          coreJetConstant C Cg Ch Dr A Cr*L*b^2/b^k := by
  obtain ⟨C,hC,hval⟩ := wrapped_core_value
  obtain ⟨Cg,hCg,hg⟩ := chain_gradient_norm_uniform
  obtain ⟨Ch,Dr,hCh,hDr,hh⟩ := rawCore_second_uniform
  refine ⟨C,Cg,Ch,Dr,hC,hCg,hCh,hDr,?_⟩
  intro E _ _ _ n L β A ν b R Cr hL hβ hA hν hνL hβb hbR hRb hCr hwidth V u k hk
  have hb : 0<b := hβ.trans_le hβb
  have hR : 0<R := hb.trans_le hbR
  let B := coreJetConstant C Cg Ch Dr A Cr
  have hB0 : phi 0+C*Cr+12*A≤B := by
    dsimp [B,coreJetConstant]
    nlinarith [mul_nonneg hDr hA]
  have hB1 : Cg+4*A≤B := by
    dsimp [B,coreJetConstant]
    have hp := phi_nonneg 0
    nlinarith [mul_nonneg hC hCr,mul_nonneg hDr hA]
  have hB2 : Ch+Dr*A+4*(Cg+4*A)≤B := by
    dsimp [B,coreJetConstant]
    have hp := phi_nonneg 0
    nlinarith [mul_nonneg hC hCr]
  have hG (z : Space n) : ‖gradient (rawCore n L β A ν b) z‖≤(Cg+4*A)*L*b := by
    apply (rawCore_gradient_bound Cg hg n L β A ν b hL.le hβ hA hν hb z).trans
    have hc := mul_le_mul_of_nonneg_left hwidth (mul_nonneg hCg hL.le)
    have hn := mul_le_mul_of_nonneg_right hνL hb.le
    have hw := mul_le_mul_of_nonneg_left hβb hL.le
    have hr := mul_le_mul_of_nonneg_left (show 3*ν*b+L*β≤4*L*b by linarith) hA
    nlinarith only [hc,hr]
  have hcarried := carried_first_second (rawCore n L β A ν b) (rawCore_contDiff n 3 L β A ν b)
    ((Cg+4*A)*L*b) ((Ch+Dr*A)*L) R (by positivity) (by positivity) hR hG
    (hh n L β A ν b hL hβ hA hν hνL hβb) V u
  have hratio : ((Cg+4*A)*L*b)/R≤(Cg+4*A)*L := (div_le_iff₀ hR).mpr
    (mul_le_mul_of_nonneg_left hbR (by positivity))
  interval_cases k
  · rw [norm_iteratedFDeriv_zero,Real.norm_eq_abs,pow_zero,div_one]
    exact (hval E n L β A ν b R Cr hL hβ hA hν hνL hβb hR hRb hwidth V u).trans
      (by change _≤B*L*b^2;nlinarith only [mul_le_mul_of_nonneg_right hB0 (show 0≤L*b^2 by positivity)])
  · apply hcarried.1.trans
    have ht := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB1 hL.le) hb.le
    change (Cg+4*A)*L*b≤B*L*b^2/b^1
    convert ht using 1
    field_simp
    ring
  · apply hcarried.2.trans
    have ht := mul_le_mul_of_nonneg_right hB2 hL.le
    change (Ch+Dr*A)*L+4*((Cg+4*A)*L*b)/R≤B*L*b^2/b^2
    rw [show 4*((Cg+4*A)*L*b)/R=4*(((Cg+4*A)*L*b)/R) by ring]
    have hb' : B*L*b^2/b^2=B*L := by field_simp
    rw [hb']
    nlinarith only [hratio,ht]

end Bilevel.PolishedLiteral
