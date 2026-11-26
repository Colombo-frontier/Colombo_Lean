import Bilevel.ChiRecursiveSourceGeometry
import Bilevel.ChiRecursiveValue
import Bilevel.ChiBoundedChainUniformEta

/-! The uniform payload bound for the actual source scale and frame family,
discharging the local analytic and energy assumptions in the recursion. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiBoundedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem sourceGeometry_payload_bound (initial : Scale) (r η b : ℕ → ℝ)
    (A Kminus ζ cn CR : ℝ)
    (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] E)
    (hl : 0 < initial.curvature) (hh : 0 < initial.width) (hr : ∀ j,1≤r j)
    (hη : ∀ j,0<η j) {ηmax δ δ₀ : ℝ} (hηmax : 0<ηmax) (hηle : ∀ j,η j≤ηmax)
    (hA : 0≤A) (hK : 0<Kminus) (hζ : 0<ζ) (hcn : 0<cn)
    (hlen : 128≤cn/ηmax^2) (hδ : 0≤δ) (hδ₀ : 0≤δ₀) (hleaf : 2*δ₀≤δ)
    (hamp : sourceAmplitudeConstant A Kminus ζ cn ηmax≤δ₀)
    (hsmall : δ₀+(gaussianBound+δ)*ηmax^2≤δ)
    (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    |payloadValue (sourceGeometry initial r η b A Kminus ζ cn CR U) d j I u|≤
      δ*(parentScale initial r η j).energy := by
  let D := sourceGeometry initial r η b A Kminus ζ cn CR U
  have hpos := parentScale_positive initial r η hl hh hr hη
  have he : ∀ k,0≤(parentScale initial r η k).energy :=
    fun k => mul_nonneg (hpos k).1.le (sq_nonneg _)
  have hell : ∀ k P,0≤(D k P).ell := by
    intro k P
    exact mul_nonneg (by linarith [hr k]) (hpos k).1.le
  have hH : ∀ k P v,|(D k P).H v|≤δ₀*(parentScale initial r η k).energy := by
    intro k P v
    have hηsq : (η k)^2≤ηmax^2 := by have hb := hηle k;have hp := hη k;nlinarith
    have hlen' : 128≤cn/(η k)^2 := hlen.trans
      (div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hη k)) hηsq)
    have hn := (sourceChainIndex_length hcn (hr k) (hη k) hlen').2
    have hlocal := source_payload_amplitude A Kminus ζ cn (η k)
      (parentScale initial r η k).curvature (parentScale initial r η k).width (r k)
      (sourceChainIndex cn (r k) (η k)) hA hK hζ hcn (hη k) (hpos k).1 (hpos k).2 (hr k) hn
      ((D k P).coordinates v)
    have hamono := (source_constants_mono_eta (Cg:=0) (Cr:=0) (J:=0) (Cp:=0)
      (cn:=cn) hA hK.le hζ (hη k).le (hηle k)).2.2
    exact hlocal.trans (mul_le_mul_of_nonneg_right (hamono.trans hamp) (he k))
  have hR : ∀ k P,gaussianBound*((D k P).ell*(D k P).width^2)≤
      gaussianBound*(parentScale initial r η (k+1)).energy := fun _ _ => le_rfl
  have hscale : ∀ k,δ₀*(parentScale initial r η k).energy+
      (gaussianBound+δ)*(parentScale initial r η (k+1)).energy≤δ*(parentScale initial r η k).energy := by
    intro k
    have hc := mul_le_mul_of_nonneg_left
      (parentScale_energy_contract initial r η hl hh hr hη hηle k) (add_nonneg gaussianBound_nonneg hδ)
    have hs := mul_le_mul_of_nonneg_right hsmall (he k)
    nlinarith only [hc,hs]
  exact payloadValue_uniform_bound D (fun k => (parentScale initial r η k).energy)
    hδ hδ₀ hleaf he hell hH hR hscale d j I u

theorem geometric_margin_comparison {t η g : ℝ}
    (ht0 : 0≤t) (ht1 : t≤1) (hη0 : 0≤η) (hη1 : η≤1) (hg : 0≤g)
    {k J : ℕ} (hk : k≤J) :
    t^(J+1)*(η^J*g)/4≤t^(k+1)*(η^k*g)/4 := by
  have ht := pow_le_pow_of_le_one ht0 ht1 (Nat.add_le_add_right hk 1)
  have he := pow_le_pow_of_le_one hη0 hη1 hk
  have hh := mul_le_mul ht (mul_le_mul_of_nonneg_right he hg)
    (by positivity : 0≤η^J*g) (pow_nonneg ht0 _)
  linarith only [hh]

end Bilevel.ChiRecursive
