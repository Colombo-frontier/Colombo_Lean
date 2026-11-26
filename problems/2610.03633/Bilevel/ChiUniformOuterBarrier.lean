import Bilevel.ChiOuterSharedCalibration

/-! Source weighted block alternative retaining the full macro margin. The geometry gain is independent of the eventual response dilation. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive
universe u

set_option maxHeartbeats 1000000 in
theorem source_outer_independent_barrier : ∃ Cs Cr t η ζ cn CR Km : ℝ,
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
        (initial.force/4 ≤
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
    have heq : (fun y => outerObjective M (initial.curvature/24) D ρ R J y v) =
        fun y => attachment M (initial.curvature/24) Q W y+publicValue ρ R J 0 v := rfl
    rw [heq,fderiv_add_const]
    exact hstop
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

