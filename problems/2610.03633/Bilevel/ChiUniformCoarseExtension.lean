import Bilevel.ChiSourceCoarseExtension
import Bilevel.ChiScheduledNodeScales
import Bilevel.ChiUniformCurvatureSums

/-! Actual coarse-extension jets for independently chosen middle width.
The sharp sqrt(T) Hessian cost is retained until numerical calibration. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem independent_coarse_sums {cn η T P ℓ b K d : ℝ}
    (hcn : 0≤cn) (hη : 0≤η) (hη1 : η≤1) (hT : 1≤T) (hP : 0≤P)
    (hℓ : 0≤ℓ) (hb : 0≤b) (hK : 0<K) (hd : 0<d) (J : ℕ) :
    (∑ i : Fin J,4*P*(ℓ*curvature T (i.val+1))*
      (η^(i.val+1)*b/(K*curvature T (i.val+1)))*
      ((length cn η T i.val:ℝ)^(1/3:ℝ))^2/d)≤
        4*P*(ℓ*b/(K*d))*(J:ℝ)*(cn/η^2)^(2/3:ℝ)*Real.sqrt T ∧
    (∑ i : Fin J,8*P*(ℓ*curvature T (i.val+1))*
      (length cn η T i.val:ℝ)^(1/3:ℝ)/d)≤
        8*P*(ℓ/d)*(J:ℝ)*(cn/η^2)^(1/3:ℝ)*T := by
  constructor
  · have hs := mul_le_mul_of_nonneg_left (weighted_length_hessian_sum hcn hη hη1 hT J)
      (show 0≤4*P*(ℓ*b/(K*d)) by positivity)
    have he : (∑ i : Fin J,4*P*(ℓ*curvature T (i.val+1))*
        (η^(i.val+1)*b/(K*curvature T (i.val+1)))*
        ((length cn η T i.val:ℝ)^(1/3:ℝ))^2/d)=
        (4*P*(ℓ*b/(K*d)))*(∑ i : Fin J,η^(i.val+1)*((length cn η T i.val:ℝ)^(1/3:ℝ))^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have ha := (curvature_pos (by linarith : 0<T) (i.val+1)).ne'
      field_simp
      ring
    rw [he]
    convert hs using 1
    ring
  · have hi (i : Fin J) : 8*P*(ℓ*curvature T (i.val+1))*
        (length cn η T i.val:ℝ)^(1/3:ℝ)/d≤8*P*(ℓ/d)*(cn/η^2)^(1/3:ℝ)*T := by
      have hh := mul_le_mul_of_nonneg_left (weighted_length_bound (η:=η) hcn (by linarith : 0<T) i.val)
        (show 0≤8*P*(ℓ/d) by positivity)
      convert hh using 1 <;> ring
    have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    convert hs using 1
    ring

theorem independent_coarse_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0≤A) (hKm : 1≤Kminus) (hζ : 0<ζ) (hζ1 : ζ≤1)
    (hcn : 0<cn) (hcn1 : cn≤1) :
    ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (η Kg T CR Km : ℝ) (weight : ℕ → ℝ),0<η → η≤1 → 0<Kg → 1/η≤Kg →
      1≤T → 128≤cn/η^2 → (∀ j,0<weight j) → (∀ j,weight j≤1) →
      1≤CR → ζ*Real.sqrt cn≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ) (index : Fin J → Fin normals) (d : ℝ),0<d →
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 (sourceCoarseExtension blocks normals M D J index d) z‖≤
        4*SmallGapLiftSupport.C*C^(J+2)*(initial.curvature*initial.width/(Kg*d))*(J:ℝ)*
          (cn/η^2)^(2/3:ℝ)*Real.sqrt T ∧
      ‖iteratedFDeriv ℝ 3 (sourceCoarseExtension blocks normals M D J index d) z‖≤
        8*SmallGapLiftSupport.C*C^(J+2)*(initial.curvature/d)*(J:ℝ)*(cn/η^2)^(1/3:ℝ)*T := by
  obtain ⟨C,hC,hjet⟩ := source_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hb η Kg T CR Km weight hη hη1 hK hthreshold hT hlen
    hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hthreshold hη
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (hresle j).trans hη1
  have hreslen (j : ℕ) : 128≤cn/(resolution η Kg j)^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    nlinarith [hresle j,hres j]
  intro J blocks normals index d hd z
  have hj := hjet E F n initial hl hb (sourceRatio T) (resolution η Kg) weight
    CR Km hr hres hres1 hreslen hw hw1 hCR hCRcn hKm' U V J blocks normals index d hd z
  have hsc (i : Fin J) := source_high_node_scales initial T η Kg weight A Kminus ζ cn CR V
    hl hT hη hcn hlen i.val []
  have hN (i : Fin J) : ((D (i.val+1) []).n:ℝ)+1=(length cn η T i.val:ℝ) := by
    exact_mod_cast (hsc i).1
  have hell (i : Fin J) : (D (i.val+1) []).ell=initial.curvature*curvature T (i.val+1) := (hsc i).2.1
  have hwidth (i : Fin J) : (D (i.val+1) []).width=
      η^(i.val+1)*initial.width/(Kg*curvature T (i.val+1)) := (hsc i).2.2
  change _≤_ ∧ _≤_ ∧ _≤_ at hj
  have h2 := hj.2.1
  have h3 := hj.2.2
  change ‖iteratedFDeriv ℝ 2 _ z‖≤∑ i : Fin J,4*SmallGapLiftSupport.C*C^(J+2)*
    (D (i.val+1) []).ell*(D (i.val+1) []).width*((((D (i.val+1) []).n:ℝ)+1)^(1/3:ℝ))^2/d at h2
  change ‖iteratedFDeriv ℝ 3 _ z‖≤∑ i : Fin J,8*SmallGapLiftSupport.C*C^(J+2)*
    (D (i.val+1) []).ell*((((D (i.val+1) []).n:ℝ)+1)^(1/3:ℝ))/d at h3
  simp_rw [hN,hell,hwidth] at h2
  simp_rw [hN,hell] at h3
  have hs := independent_coarse_sums hcn.le hη.le hη1 hT
    (mul_nonneg SmallGapLiftSupport.C_pos.le (pow_nonneg (by linarith : 0≤C) (J+2)))
    hl.le hb.le hK hd J
  refine ⟨h2.trans ?_,h3.trans ?_⟩
  · simpa only [mul_assoc] using hs.1
  · simpa only [mul_assoc] using hs.2

end Bilevel.ChiExtensionCalibration
