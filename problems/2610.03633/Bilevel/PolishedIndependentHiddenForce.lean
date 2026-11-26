import Bilevel.ChiUniformCoarseExtension
import Bilevel.ChiHierarchyInactive
import Bilevel.ChiScheduledExtensionAssembly
import Bilevel.ChiExtensionLedgerAbsorption

/-!
Independent base width in the full hidden-gradient ledger of
`waI:lem:hidden`.  Geometry gain Kg is arbitrary and no response gain
appears.  Both globally fixed active/inactive potentials are included;
the unbounded public radial potential is excluded as in the source.

The result concerns the inherited SmallGapProfiles normal profile (C3).
It does not identify that profile with a prescribed C-infinity normal.
-/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension
  ChiCurvatureSchedule

theorem independent_fine_energy {L₀ b η Kg a d : ℝ}
    (hL : 0 ≤ L₀) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hK : 0 < Kg)
    (ha : 1 ≤ a) (hd : 0 < d) (J : ℕ) :
    (L₀*a)*(η^J*b/(Kg*a))^2/d ≤ (L₀/d)*(b/Kg)^2 := by
  have hap : 0 < a := by linarith
  have hp := pow_le_one₀ hη hη1 (n := J)
  have hp0 := pow_nonneg hη J
  have hs : (η^J)^2 ≤ a := by nlinarith
  have he : (L₀*a)*(η^J*b/(Kg*a))^2/d =
      ((L₀/d)*(b/Kg)^2)*((η^J)^2/a) := by
    field_simp
    ring
  rw [he]
  apply mul_le_of_le_one_right (by positivity)
  exact (div_le_one hap).mpr hs

theorem independent_coarse_energy {cn η T L₀ b Kg d : ℝ}
    (hcn : 0 ≤ cn) (hη : 0 < η) (hη1 : η ≤ 1) (hT : 1 ≤ T)
    (hL : 0 ≤ L₀) (hK : 0 < Kg) (hd : 0 < d) (j : ℕ) :
    (length cn η T j : ℝ)*(L₀*curvature T (j+1))*
        (η^(j+1)*b/(Kg*curvature T (j+1)))^2/d ≤
      cn*(L₀/d)*(b/Kg)^2 := by
  have hTp : 0 < T := by linarith
  have ha := curvature_pos hTp (j+1)
  have ha0 := curvature_pos hTp j
  have hn := length_upper (η := η) hcn hTp j
  have hm := mul_le_mul_of_nonneg_right hn
    (show 0 ≤ (L₀*curvature T (j+1))*(η^(j+1)*b/(Kg*curvature T (j+1)))^2 by positivity)
  have he : (cn*(curvature T (j+1)/curvature T j)/η^2)*
      ((L₀*curvature T (j+1))*(η^(j+1)*b/(Kg*curvature T (j+1)))^2) =
      cn*L₀*η^(2*j)*b^2/(Kg^2*curvature T j) := by
    rw [show η^(2*j) = (η^j)^2 by rw [Nat.mul_comm 2 j,pow_mul],pow_succ]
    field_simp
    ring
  rw [he] at hm
  have hp := pow_le_one₀ hη.le hη1 (n := 2*j)
  have he2 : cn*L₀*η^(2*j)*b^2/(Kg^2*curvature T j) ≤ cn*L₀*b^2/Kg^2 := by
    calc
      _ ≤ cn*L₀*b^2/(Kg^2*curvature T j) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have ht := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (mul_nonneg hcn hL)) (sq_nonneg b)
        simpa only [mul_one] using ht
      _ ≤ cn*L₀*b^2/Kg^2 := by
        apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hK)
        exact le_mul_of_one_le_right (sq_nonneg Kg) (curvature_bounds hT j).1
  have hs := div_le_div_of_nonneg_right (hm.trans he2) hd.le
  convert hs using 1 <;> ring

theorem depth_linear_coefficient_absorption {P Q C B : ℝ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hC : 1 ≤ C) (hB : 1 ≤ B) (J : ℕ) :
    P*C^(J+2)*(J : ℝ)+Q*B^(J+2) ≤
      (2*(max 1 (P+Q)*(C+B)^2))^(J+1) := by
  have hj : (J : ℝ)+1 ≤ (2 : ℝ)^(J+1) := by
    induction J with
    | zero => norm_num
    | succ J ih =>
      have hp : (1 : ℝ) ≤ 2^(J+1) := one_le_pow₀ (by norm_num)
      rw [pow_succ (2 : ℝ) (J+1)]
      push_cast
      nlinarith
  have hc0 : 0 ≤ C := by linarith
  have hb0 : 0 ≤ B := by linarith
  have hn : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
  have hh := three_coefficients_absorption hP hQ (show (0 : ℝ) ≤ 0 by norm_num) hC hB J
  simp only [add_zero] at hh
  have hmul := mul_le_mul_of_nonneg_right hh (show 0 ≤ (J : ℝ)+1 by positivity)
  have hpow := mul_le_mul_of_nonneg_left hj
    (show 0 ≤ (max 1 (P+Q)*(C+B)^2)^(J+1) by positivity)
  calc
    _ ≤ (P*C^(J+2)+Q*B^(J+2))*((J : ℝ)+1) := by
      nlinarith [mul_nonneg (mul_nonneg hQ (pow_nonneg hb0 (J+2))) hn,
        mul_nonneg hP (pow_nonneg hc0 (J+2))]
    _ ≤ _ := hmul
    _ ≤ _ := hpow
    _ = _ := by rw [mul_pow (2 : ℝ) (max 1 (P+Q)*(C+B)^2) (J+1)]; ring

theorem independent_hidden_force (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ Cg : ℝ,1 ≤ Cg ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (η Kg T CR Km : ℝ) (weight : ℕ → ℝ),0 < η → η ≤ 1 → 0 < Kg → 1/η ≤ Kg →
      1 ≤ T → 128 ≤ cn/η^2 → (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J →
      ∀ (index : Fin J → Fin normals) (fineIndex : Fin normals) (d c v : ℝ),0 < d →
      ∀ hc : 0 < c,c ≤ 1/128 → ∀ hv : 1 ≤ v,∀ hβ : 0 < (D J []).width,
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 (hidden index (coarseFamily blocks M D J) (coarseWidths D J)
        fineIndex (outerFineData blocks M D J c v hc hβ hv) (1/d)) z‖ ≤
          Cg^(J+1)*(initial.curvature/d)*(initial.width/Kg)^2 ∧
      ‖iteratedFDeriv ℝ 1 (hierarchyInactiveHidden blocks M D J c v hc hβ hv
        normals index fineIndex d) z‖ ≤
          Cg^(J+1)*(initial.curvature/d)*(initial.width/Kg)^2 := by
  obtain ⟨Cc,hCc,hcoarse⟩ := source_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨Ba,hBa,hactive⟩ := source_outer_coupling_jets
  obtain ⟨Bi,hBi,hinactive⟩ := source_outer_inactive_normal_jets
  let B := Ba+Bi
  have hB : 1 ≤ B := by dsimp [B]; linarith
  let P := 2*SmallGapLiftSupport.C*cn
  let Q := 8*SmallGapLiftSupport.C
  let Cg := 2*(max 1 (P+Q)*(Cc+B)^2)
  have hP : 0 ≤ P := by dsimp [P]; have := SmallGapLiftSupport.C_pos; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; have := SmallGapLiftSupport.C_pos; positivity
  have hCg : 1 ≤ Cg := by
    have hh := three_coefficients_constant_ge_one (P := P) (Q := Q) (R := 0) hCc hB
    dsimp only [Cg]
    simp only [add_zero] at hh
    linarith
  refine ⟨Cg,hCg,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hb η Kg T CR Km weight hη hη1 hK hthreshold hT hlen
    hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hthreshold hη
  have hres1 (j : ℕ) : resolution η Kg j ≤ 1 := (hresle j).trans hη1
  have hreslen (j : ℕ) : 128 ≤ cn/(resolution η Kg j)^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    nlinarith [hresle j,hres j]
  have hp := parentScale_positive initial (sourceRatio T) (resolution η Kg) hl hb hr hres
  intro J blocks normals hJ index fineIndex d c v hd hc hcs hv hβ z
  let S := (initial.curvature/d)*(initial.width/Kg)^2
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hW (i : Fin J) : 0 < coarseWidths D J i :=
    mul_pos (hp (i.val+2)).2 (Real.rpow_pos_of_pos (by positivity) _)
  have hco := (hcoarse E F n initial hl hb (sourceRatio T) (resolution η Kg) weight CR Km
    hr hres hres1 hreslen hw hw1 hCR hCRcn hKm' U V J blocks normals index d hd z).1
  have hsc (i : Fin J) := source_high_node_scales initial T η Kg weight A Kminus ζ cn CR V
    hl hT hη hcn hlen i.val []
  have hN (i : Fin J) : ((D (i.val+1) []).n : ℝ)+1 = (length cn η T i.val : ℝ) := by
    exact_mod_cast (hsc i).1
  have he (i : Fin J) : (D (i.val+1) []).ell=initial.curvature*curvature T (i.val+1) := (hsc i).2.1
  have hh (i : Fin J) : (D (i.val+1) []).width=
      η^(i.val+1)*initial.width/(Kg*curvature T (i.val+1)) := (hsc i).2.2
  have hci (i : Fin J) :
      2*SmallGapLiftSupport.C*Cc^(J+2)*(((D (i.val+1) []).n : ℝ)+1)*
        (D (i.val+1) []).ell*((D (i.val+1) []).width)^2/d ≤ P*Cc^(J+2)*S := by
    rw [hN,he,hh]
    have ht := mul_le_mul_of_nonneg_left
      (independent_coarse_energy (b := initial.width) hcn.le hη hη1 hT hl.le hK hd i.val)
      (show 0 ≤ 2*SmallGapLiftSupport.C*Cc^(J+2) by have := SmallGapLiftSupport.C_pos; positivity)
    convert ht using 1 <;> dsimp only [P,S] <;> ring
  have hcob : ‖iteratedFDeriv ℝ 1 (sourceCoarseExtension blocks normals M D J index d) z‖ ≤
      P*Cc^(J+2)*(J : ℝ)*S := by
    apply hco.trans
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hci i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hs
    convert hs using 1
    ring
  have hell : (D J []).ell=initial.curvature*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_high_node_curvature initial (by linarith) η Kg j
  have hwidth : (D J []).width=η^J*initial.width/(Kg*curvature T J) := by
    exact source_parent_width initial hT hl η Kg J
  have henergy : (D J []).ell*((D J []).width)^2/d ≤ S := by
    rw [hell,hwidth]
    exact independent_fine_energy hl.le hη.le hη1 hK (curvature_bounds hT J).1 hd J
  have hfa := (hactive E F n initial hl hb (sourceRatio T) (resolution η Kg) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKm hζ hζ1 hCR hKm' U V J blocks c v hc hcs hv
    (normalSlice normals fineIndex z)).1
  have hfa' := fineTerm_normalized_jet fineIndex (outerFineData blocks M D J c v hc hβ hv) hd z 1
    (by norm_num) hfa
  have hfi := (hinactive E F n initial hl hb (sourceRatio T) (resolution η Kg) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKm hζ hζ1 hCR hKm' U V J blocks c v hc hcs hv
    hβ normals fineIndex z).1
  have hfi' : ‖iteratedFDeriv ℝ 1
      (fun y => outerInactiveNormal blocks M D J c v hc hβ hv normals fineIndex y/d) z‖ ≤
      8*SmallGapLiftSupport.C*Bi^(J+2)*(D J []).ell*((D J []).width)^2/d := by
    rw [normalized_jet_norm (outerInactiveNormal_contDiff blocks M D J c v hc hβ hv normals fineIndex)
      hd 1 (by norm_num) z]
    exact div_le_div_of_nonneg_right hfi hd.le
  have hBa0 : 0 ≤ Ba := by linarith
  have hBi0 : 0 ≤ Bi := by linarith
  have hCp := SmallGapLiftSupport.C_pos
  have hE := (hp (J+1)).1.le
  have haf : ‖iteratedFDeriv ℝ 1
      (fun y => fineTerm normals fineIndex (outerFineData blocks M D J c v hc hβ hv) y/d) z‖ ≤
      Q*B^(J+2)*S := by
    apply hfa'.trans
    calc
      _ ≤ 8*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/d := by
        dsimp only [B]
        gcongr
        · norm_num
        · linarith
      _ ≤ Q*B^(J+2)*S := by
        have ht := mul_le_mul_of_nonneg_left henergy
          (show 0 ≤ 8*SmallGapLiftSupport.C*B^(J+2) by positivity)
        convert ht using 1
        dsimp only [Q]
        ring
  have hif : ‖iteratedFDeriv ℝ 1
      (fun y => outerInactiveNormal blocks M D J c v hc hβ hv normals fineIndex y/d) z‖ ≤
      Q*B^(J+2)*S := by
    apply hfi'.trans
    calc
      _ ≤ 8*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/d := by
        dsimp only [B]
        gcongr
        linarith
      _ ≤ Q*B^(J+2)*S := by
        have ht := mul_le_mul_of_nonneg_left henergy
          (show 0 ≤ 8*SmallGapLiftSupport.C*B^(J+2) by positivity)
        convert ht using 1
        dsimp only [Q]
        ring
  have hcoef := mul_le_mul_of_nonneg_right
    (depth_linear_coefficient_absorption hP hQ hCc hB J) hS
  have hfinal : P*Cc^(J+2)*(J : ℝ)*S+Q*B^(J+2)*S ≤
      Cg^(J+1)*(initial.curvature/d)*(initial.width/Kg)^2 := by
    convert hcoef using 1 <;> dsimp only [Cg,S] <;> ring
  constructor
  · exact (source_hidden_add_jet_bound blocks normals M D J index fineIndex
      (outerFineData blocks M D J c v hc hβ hv) d hW z 1 (by norm_num) _ _ hcob haf).trans hfinal
  · exact (hierarchyInactiveHidden_jet_bound blocks M D J c v hc hβ hv normals index
      fineIndex d (fun i => (hp (i.val+2)).2) z 1 (by norm_num) _ _ hcob hif).trans hfinal

theorem full_gradient_bound_of_first_jet
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {z : E} {B : ℝ} (h : ‖iteratedFDeriv ℝ 1 f z‖ ≤ B) :
    ‖gradient f z‖ ≤ B := by
  rw [← norm_fderiv_eq_norm_gradient]
  have he := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0) (f := f) (x := z)
  simpa only [norm_iteratedFDeriv_zero,Nat.zero_add] using he.trans_le h

theorem independent_hidden_gradient_force (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ Cg : ℝ,1 ≤ Cg ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (η Kg T CR Km : ℝ) (weight : ℕ → ℝ),0 < η → η ≤ 1 → 0 < Kg → 1/η ≤ Kg →
      1 ≤ T → 128 ≤ cn/η^2 → (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) →
      1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J →
      ∀ (index : Fin J → Fin normals) (fineIndex : Fin normals) (d c v : ℝ),0 < d →
      ∀ hc : 0 < c,c ≤ 1/128 → ∀ hv : 1 ≤ v,∀ hβ : 0 < (D J []).width,
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖gradient (hidden index (coarseFamily blocks M D J) (coarseWidths D J)
        fineIndex (outerFineData blocks M D J c v hc hβ hv) (1/d)) z‖ ≤
          Cg^(J+1)*(initial.curvature/d)*(initial.width/Kg)^2 ∧
      ‖gradient (hierarchyInactiveHidden blocks M D J c v hc hβ hv
        normals index fineIndex d) z‖ ≤
          Cg^(J+1)*(initial.curvature/d)*(initial.width/Kg)^2 := by
  obtain ⟨Cg,hCg,hbound⟩ := independent_hidden_force A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  refine ⟨Cg,hCg,?_⟩
  intro E F _ _ _ _ _ _ n initial hl hb η Kg T CR Km weight hη hη1 hK hthreshold hT hlen
    hw hw1 hCR hCRcn hKm' U V
  dsimp only
  intro J blocks normals hJ index fineIndex d c v hd hc hcs hv hβ z
  have h := hbound E F n initial hl hb η Kg T CR Km weight hη hη1 hK hthreshold hT hlen
    hw hw1 hCR hCRcn hKm' U V J blocks normals hJ index fineIndex d c v hd hc hcs hv hβ z
  exact ⟨full_gradient_bound_of_first_jet h.1,full_gradient_bound_of_first_jet h.2⟩

end Bilevel.ChiExtensionCalibration
