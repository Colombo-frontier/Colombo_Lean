import Bilevel.ChiOuterCalibration
import Bilevel.ChiOuterWrappedRegularity

/-! The same actual source constants also satisfy all carrier-ledger
hypotheses. The length cap is deduced from the already-proved amplitude
budget; the macro radius constant is exposed at its constructive value. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive
universe u

theorem gaussianBound_ge_one : (1:ℝ)≤gaussianBound := by
  have he : (1:ℝ)≤Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hp : (1:ℝ)≤2*Real.pi := by linarith [Real.two_le_pi]
  have hs := mul_le_mul (Real.one_le_sqrt.mpr he) (Real.one_le_sqrt.mpr hp)
    (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg (Real.exp 1))
  simpa only [one_mul,gaussianBound] using hs

theorem length_constant_le_one {C ζ cn η : ℝ} (hC : 0≤C) (hζ : 0<ζ) (hcn : 0≤cn) (hη : 0≤η)
    (hamp : sourceAmplitudeConstant 3 1 ζ cn η≤releaseTolerance C/4) : cn≤1 := by
  have hδ : releaseTolerance C≤1 := (div_le_one (by positivity : 0<16*(C+1))).mpr (by linarith)
  have hcnG := mul_le_mul_of_nonneg_right gaussianBound_ge_one hcn
  have h1 : 0≤3*(3:ℝ)*(3*ζ+η) := by positivity
  have h2 : 0≤2*(3:ℝ)*1*η^2/ζ := by positivity
  unfold sourceAmplitudeConstant at hamp
  nlinarith only [hδ,hcnG,h1,h2,hamp]

theorem radial_ledger_compatibility {ζ cn CR : ℝ} (_hζ : 0≤ζ) (hζ1 : ζ≤1)
    (hcn : cn≤1) (hCR : 1≤CR) : ζ*Real.sqrt cn≤CR := by
  have hs : Real.sqrt cn≤1 := Real.sqrt_le_one.mpr hcn
  exact (mul_le_mul hζ1 hs (Real.sqrt_nonneg _) zero_le_one).trans (by simpa using hCR)

theorem numerical_macro_endgame_ge_one : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (n : ℕ) (ℓ h : ℝ), 0 < ℓ → 0 < h →
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (U : Space n →ₗᵢ[ℝ] F) (u : F),
    let R := K*h*Real.sqrt ((n:ℝ)+1)
    WrappedChain.coordinates n R U u (Fin.last n) < h →
      (ℓ*h)/2 ≤ ‖gradient (macroValue n ℓ h (ℓ/24) R U) u‖ := by
  obtain ⟨C,hC,hb⟩ := chain_gradient_norm_uniform
  let K := 192*(C+1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K,by dsimp [K];linarith,?_⟩
  intro n ℓ h hℓ hh F _ _ _ U u
  dsimp only
  intro hlast
  let s := Real.sqrt ((n:ℝ)+1)
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hR : 0 < K*h*s := mul_pos (mul_pos hK hh) hs0
  apply macro_endgame_from_bound n ℓ h (ℓ/24) (K*h*s) (C*(ℓ*h)*s)
    hℓ.le hh (by positivity) hR (by positivity) (hb n ℓ h hℓ.le hh) _ _ _ U u hlast
  · dsimp [K]
    nlinarith [mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le,
      mul_nonneg hC (mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le)]
  · nlinarith [mul_pos hℓ hh]
  · have hscale := mul_le_mul_of_nonneg_left hs (mul_nonneg hℓ.le hh.le)
    dsimp [K]
    nlinarith [mul_nonneg hC (mul_nonneg (mul_nonneg hℓ.le hh.le) hs0.le)]


set_option maxHeartbeats 1000000 in
theorem source_outer_shared_barrier : ∃ Cs Cr t η ζ cn CR Km : ℝ,
    0≤Cs ∧ 0≤Cr ∧ t=descentThreshold (Cr+Cs) ∧
    sourceAmplitudeConstant 3 1 ζ cn η≤releaseTolerance (Cr+Cs)/4 ∧
    η^2≤releaseTolerance (Cr+Cs)/(2*(gaussianBound+releaseTolerance (Cr+Cs))) ∧
    0 < t ∧ t < 1 ∧ 0 < η ∧ η ≤ 1 ∧ 0 < ζ ∧ ζ ≤ 2/15 ∧ 0 < cn ∧
    cn ≤ 1 ∧ 128 ≤ cn/η^2 ∧ 1 ≤ CR ∧ ζ*Real.sqrt cn ≤ CR ∧ 1 ≤ Km ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (initial : Scale), 0 < initial.curvature → 0 < initial.width →
      ∀ (r : ℕ → ℝ), (∀ j, 1 ≤ r j) → ∀ (K : ℝ), 0 < K → 1/η ≤ K →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (resolution η K j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let b := fun j => t^(j+1)
      let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
      ∀ (J : ℕ) (x : E) (v : ℕ → F),
        M.coordinates x (Fin.last n) < initial.width →
        (t^(J+1)*(η^J*initial.force)/4 ≤
          ‖fderiv ℝ (fun y => outerObjective M (initial.curvature/24) D ρ R J y v) x‖) ∨
        ∃ k : ℕ,k ≤ J ∧ t^(J+1)*(η^J*initial.force)/4/K ≤
          ‖fderiv ℝ (fun y => outerObjective M (initial.curvature/24) D ρ R J x (Function.update v k y)) (v k)‖ := by
  obtain ⟨Cs,Cr,hCs,hCr,hderiv⟩ := constructed_node_derivative_envelopes.{u}
  obtain ⟨t,η,ζ,cn,CR,hteq,hamp,henergy,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hlen,hCR,hinner⟩ :=
    source_inner_barrier_with_envelopes Cs Cr hCs hCr hderiv
  obtain ⟨Km,hKm1,hmacro⟩ := numerical_macro_endgame_ge_one
  have hKm : 0<Km := by linarith
  have hcn1 := length_constant_le_one (add_nonneg hCr hCs) hζ hcn.le hη.le hamp
  have hCRsqrt := radial_ledger_compatibility hζ.le (show ζ≤1 by linarith) hcn1 hCR
  refine ⟨Cs,Cr,t,η,ζ,cn,CR,Km,hCs,hCr,hteq,hamp,henergy,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRsqrt,hKm1,?_⟩
  intro E F _ _ _ _ _ _ n initial hell hh r hr K hK hKth U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let b := fun j : ℕ => t^(j+1)
  let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR V
  let R := fun j => (D j []).radius
  let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
  let δ := releaseTolerance (Cr+Cs)
  have hC : 0 ≤ Cr+Cs := add_nonneg hCr hCs
  have hδ : 0 < δ := (descentThreshold_range hC).2.2
  have hg : 0 ≤ initial.force := mul_nonneg hell.le hh.le
  have hRmacro : 0 < M.radius := by
    change 0 < Km*initial.width*Real.sqrt ((n:ℝ)+1)
    exact mul_pos (mul_pos hKm hh) (Real.sqrt_pos.mpr (by positivity))
  have hsmall : δ/4+(gaussianBound+δ)*η^2 ≤ δ := by
    have hden : 0 < 2*(gaussianBound+δ) := by have hg0 := gaussianBound_nonneg; positivity
    have he := (le_div_iff₀ hden).mp henergy
    nlinarith only [he,hδ]
  intro J x v hlast
  let Q : Fin (M.n+1) → ℝ := fun i => (D 0 [i.val]).release (v 0)
  let W : Fin (M.n+1) → ℝ := fun i => payloadValue D J 0 [i.val] v
  have hbounds (i : Fin (M.n+1)) := wrapped_derivative_bounds_of_node M Cs Cr hCs hCr
    hell.le hh i x (hderiv E M hell.le hh hRmacro i x).1 (hderiv E M hell.le hh hRmacro i x).2
  have hW : ∀ i, |W i| ≤ δ*(M.ell*M.width^2) := by
    intro i
    exact sourceGeometry_payload_bound initial r (resolution η K) b 3 1 ζ cn CR V hell hh hr
      (base_resolution_positive hη hK) hη (base_resolution_le hK hKth hη)
      (by norm_num) (by norm_num) hζ hcn hlen hδ.le (by positivity) (by linarith) hamp hsmall J 0 [i.val] v
  have hm : (M.ell*M.width)/2 ≤
      ‖fderiv ℝ (macroValue M.n M.ell M.width (initial.curvature/24) M.radius M.frame) x‖ := by
    rw [norm_fderiv_eq_norm_gradient]
    exact hmacro n initial.curvature initial.width hell hh E U x hlast
  have he := attachment_stop_or_descend M (initial.curvature/24) Q W x hCs hCr hδ.le le_rfl
    hell.le hh hRmacro (fun i => (D 0 [i.val]).release_range (v 0))
    (fun i => (hbounds i).1) (fun i => (hbounds i).2) hW hm
  rcases he with hstop|⟨i,hi,hQi⟩
  · left
    have htp : t^(J+1) ≤ 1 := pow_le_one₀ ht.le ht1.le
    have hep : η^J ≤ 1 := pow_le_one₀ hη.le hη1
    have hp := mul_le_mul htp hep (pow_nonneg hη.le _) zero_le_one
    have hm' := mul_le_mul_of_nonneg_right hp hg
    have htarget : t^(J+1)*(η^J*initial.force)/4 ≤ (M.ell*M.width)/4 := by
      change t^(J+1)*(η^J*initial.force)/4 ≤ initial.force/4
      nlinarith only [hm']
    have heq : (fun y => outerObjective M (initial.curvature/24) D ρ R J y v) =
        fun y => attachment M (initial.curvature/24) Q W y+publicValue ρ R J 0 v := rfl
    rw [heq,fderiv_add_const]
    exact htarget.trans hstop
  · right
    have hit : t < wrappedSelector M i x := by rwa [← hteq] at hi
    have hi0 : wrappedSelector M i x ≠ 0 := ne_of_gt (ht.trans hit)
    have hψ := wrappedSelector_range M i x
    have hRp := wrappedResidual_nonpos M hell.le i x
    have hRpbound : |wrappedResidual M i x| ≤ gaussianBound*initial.energy := by
      have hb' := wrappedResidual_abs_bound M hell.le i x
      have he0 : 0 ≤ gaussianBound*(M.ell*M.width^2) := by have hG := gaussianBound_nonneg; positivity
      exact hb'.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hψ.2 he0)
    have hiB := hinner F initial hell hh r hr K hK hKth
      (fun j I => V j ([i.val]++I)) J v (wrappedSelector M i x) (wrappedResidual M i x)
      hit.le hψ.2 hRp hRpbound hQi
    change ∃ k : ℕ,k ≤ J ∧ t^(J+1)*(η^J*(initial.force/K))/4 ≤
      ‖fderiv ℝ (fun y => objective (rebase D [i.val]) ρ R J 0 []
        (wrappedSelector M i x) (wrappedResidual M i x) (Function.update v k y)) (v k)‖ at hiB
    simp only [objective_rebase,List.append_nil] at hiB
    obtain ⟨k,hk,hbound⟩ := hiB
    refine ⟨k,hk,?_⟩
    rw [outerObjective_inner_derivative M (initial.curvature/24) D ρ R J k x v i hi0]
    convert hbound using 1
    ring

end Bilevel.ChiOuter
