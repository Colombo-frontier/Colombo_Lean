import Bilevel.ChiUpperNoiseSource
import Bilevel.BernoulliOracle

/-! The actual macro and micro floors in the direct upper placement,
and their Bernoulli count arithmetic. No query lower bound is asserted. -/
noncomputable section
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiExtensionCalibration

def microLength (cn K : ℝ) : ℕ := Nat.floor (cn*K^2)

theorem micro_length_argument {cn η K : ℝ} (hcn : 0<cn) (hη : 0<η) (hK : 0<K)
    (hlen : 128≤cn/η^2) (hKth : 1/η≤K) : 128≤cn*K^2 := by
  have hres : 1/K≤η := by
    apply (div_le_iff₀ hK).mpr
    have hh := (div_le_iff₀ hη).mp hKth
    nlinarith only [hh]
  have hh := div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (div_pos zero_lt_one hK))
    (pow_le_pow_left₀ (by positivity : (0:ℝ)≤1/K) hres 2)
  apply (hlen.trans hh).trans_eq
  field_simp

theorem micro_length_exact {cn K : ℝ} (hlarge : 128≤cn*K^2) :
    sourceChainIndex cn 1 (1/K)+1=microLength cn K ∧
    128≤microLength cn K ∧ cn*K^2/2≤(microLength cn K:ℝ) := by
  have hnonneg : 0≤cn*K^2 := by linarith only [hlarge]
  have hn : 128≤microLength cn K := (Nat.le_floor_iff hnonneg).mpr (by exact_mod_cast hlarge)
  refine ⟨?_,hn,LowerAlgebra.natFloor_half_lower _ (by linarith only [hlarge])⟩
  have he : cn*1/(1/K)^2=cn*K^2 := by field_simp
  unfold sourceChainIndex
  rw [he]
  change microLength cn K-1+1=microLength cn K
  omega

theorem macro_micro_count_lower {η₀ L Δ Cgap Cb ε cn K : ℝ} {n : ℕ}
    (_hη₀ : 0<η₀) (_hL : 0<L) (_hΔ : 0<Δ) (_hCg : 0<Cgap) (_hCb : 0<Cb)
    (_hε : 0<ε) (_hcn : 0<cn) (hlarge : 128≤cn*K^2)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(n:ℝ)) :
    (cn*η₀/(8*Cgap*Cb^2))*L*K^2*Δ/ε^2≤((n+1)*microLength cn K:ℕ) := by
  have hm := (micro_length_exact hlarge).2.2
  have hn' : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤((n+1:ℕ):ℝ) := hn.trans (by norm_num)
  have hh := mul_le_mul hn' hm (show 0≤cn*K^2/2 by positivity) (Nat.cast_nonneg (n+1))
  rw [Nat.cast_mul]
  apply le_trans _ hh
  apply le_of_eq
  ring

theorem macro_micro_probability_lower {N : ℕ} {c C Cb L K Δ ε σ : ℝ}
    (hc : 0<c) (hC : 1≤C) (hCb : 1≤Cb) (hL : 0<L) (hK : 0<K) (hΔ : 0<Δ) (hε : 0<ε)
    (hcount : c*L*K^2*Δ/ε^2≤(N:ℝ)) :
    (c/(C^2*Cb^2))*(L*K^2*Δ/ε^2+L*K^4*σ^2*Δ/ε^4)≤
      (N:ℝ)*(BernoulliOracle.probability (C*Cb*ε/K) σ)⁻¹ := by
  have hCp : 0<C := by linarith only [hC]
  have hCbp : 0<Cb := by linarith only [hCb]
  have hB : 0<C*Cb*ε/K := by positivity
  rw [BernoulliOracle.inverse_probability hB]
  have hm := mul_le_mul_of_nonneg_right hcount
    (show 0≤1+σ^2/(C*Cb*ε/K)^2 by positivity)
  apply le_trans _ hm
  have hden : 1≤C^2*Cb^2 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC) (one_le_pow₀ hCb)
  have hd : c*L*K^2*Δ/(C^2*Cb^2*ε^2)≤c*L*K^2*Δ/ε^2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hε)
      (by have hh := mul_le_mul_of_nonneg_right hden (sq_nonneg ε); simpa only [one_mul] using hh)
  have he : (c/(C^2*Cb^2))*(L*K^2*Δ/ε^2+L*K^4*σ^2*Δ/ε^4)=
      c*L*K^2*Δ/(C^2*Cb^2*ε^2)+(c*L*K^2*Δ/ε^2)*(σ^2/(C*Cb*ε/K)^2) := by
    field_simp
    ring
  rw [he]
  exact (add_le_add_right hd _).trans_eq (by ring)

end Bilevel.ChiUpperNoise
