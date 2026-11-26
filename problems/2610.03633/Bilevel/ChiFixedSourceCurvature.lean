import Bilevel.ChiOuterDilationCurvature
import Bilevel.ChiCanonicalPublicData

/-! A dimension-free curvature certificate for the actual fixed-depth
source family, independent of the fine oracle parameter. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths

theorem source_fixed_public_curvature (A K ζ cn CR Km η t : ℝ)
    (hA : 0≤A) (hK : 1≤K) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km)
    (hη : 0<η) (hη1 : η≤1) (hlen : 128≤cn/η^2) (ht : 0<t) (ht1 : t≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L η₀ b κ Kg : ℝ),0<L → 0<η₀ → η₀≤1 → 0<b → 2≤κ → 0<Kg → 1/η≤Kg →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A K ζ cn CR V
      let rad := sourcePublicRadialWeight initial (sourceRatio 1) (resolution η Kg) weight ζ
      let R := sourcePublicNodeRadius initial (sourceRatio 1) (resolution η Kg) weight CR ζ
      ∀ (m : ℕ) (x z : Joint E (Blocks m F)),
      ‖gradient (jointOuter m M (initial.curvature/24) D rad R 1 (κ/6)) x-
        gradient (jointOuter m M (initial.curvature/24) D rad R 1 (κ/6)) z‖≤(C*L*κ^2)*‖x-z‖ := by
  obtain ⟨C,hC,hsecond⟩ := source_fixed_objective_second A K ζ cn CR Km hA hK hζ hζ1 hcn hcn1 hCR hCRcn hKm
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n L η₀ b κ Kg hL hη₀ hη₀1 hb hκ hKg hKgη U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let weight := fun j : ℕ => t^(j+1)
  let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight A K ζ cn CR V
  let rad := sourcePublicRadialWeight initial (sourceRatio 1) (resolution η Kg) weight ζ
  let R := sourcePublicNodeRadius initial (sourceRatio 1) (resolution η Kg) weight CR ζ
  have hres := base_resolution_positive hη hKg
  have hresle := base_resolution_le hKg hKgη hη
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (hresle j).trans hη1
  have hlen' (j : ℕ) : 128≤cn/(resolution η Kg j)^2 := hlen.trans
    (div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
      (pow_le_pow_left₀ (hres j).le (hresle j) 2))
  have hh := hsecond E F n initial (mul_pos hη₀ hL) hb
    (sourceRatio 1) (resolution η Kg) weight (sourceRatio_ge_one le_rfl) rfl
    (by simp [sourceRatio,curvature]) hres hres1 hlen'
    (fun j => pow_pos ht _) (fun j => pow_le_one₀ ht.le ht1) U V
  intro m
  have hbound (z : Joint E (Blocks m F)) :
      ‖iteratedFDeriv ℝ 2 (jointOuter m M (initial.curvature/24) D rad R 1 1) z‖≤C*L := by
    apply (hh m z).trans
    change C*(η₀*L)≤C*L
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hL.le hη₀1) (by linarith)
  exact jointOuter_kappa_curvature m M (initial.curvature/24) D rad R 1 hκ
    (mul_nonneg (by linarith only [hC]) hL.le) hbound

end Bilevel.ChiOuter

namespace Bilevel.ChiExtensionCalibration

theorem bounded_kappa_accuracy_window {c Θ κ L Δ ε : ℝ}
    (hc : 0≤c) (hΘ : 1≤Θ) (hκ : κ≤Θ) (hL : 0≤L)
    (hε : ε≤(c/Θ)*min L (κ*Real.sqrt (L*Δ))) :
    ε≤c*min L (Real.sqrt (L*Δ)) := by
  have hΘp : 0<Θ := by linarith
  have hmin : min L (κ*Real.sqrt (L*Δ))≤Θ*min L (Real.sqrt (L*Δ)) := by
    by_cases hh : L≤Real.sqrt (L*Δ)
    · rw [min_eq_left hh]
      exact (min_le_left _ _).trans (le_mul_of_one_le_left hL hΘ)
    · rw [min_eq_right (le_of_not_ge hh)]
      exact (min_le_right _ _).trans (mul_le_mul_of_nonneg_right hκ (Real.sqrt_nonneg _))
  calc ε≤(c/Θ)*min L (κ*Real.sqrt (L*Δ)) := hε
       _≤(c/Θ)*(Θ*min L (Real.sqrt (L*Δ))) := mul_le_mul_of_nonneg_left hmin (div_nonneg hc hΘp.le)
       _=c*min L (Real.sqrt (L*Δ)) := by field_simp;ring

end Bilevel.ChiExtensionCalibration
