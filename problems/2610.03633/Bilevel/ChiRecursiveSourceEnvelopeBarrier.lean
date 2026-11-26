import Bilevel.ChiRecursiveSourceValue
import Bilevel.ChiRecursiveSmallness
import Bilevel.ChiRecursiveBarrier

/-! Source-calibrated inner recursive barrier, including the special base
resolution 1/K. All local analytic and scalar budget premises are discharged.
Outer entry and finite-product full-gradient conversion are separate bridges. -/
noncomputable section
namespace Bilevel.ChiRecursive
universe u
open ChiBoundedChain

set_option maxHeartbeats 1000000 in
theorem source_inner_barrier_with_envelopes (Cs Cr : ℝ) (hCs : 0 ≤ Cs) (hCr : 0 ≤ Cr)
    (hderiv : ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F), 0 ≤ D.ell → 0 < D.width → 0 < D.radius → ∀ i u,
      ‖fderiv ℝ (D.selector i) u‖ ≤ (Cs/D.width)*Real.sqrt (D.selector i u) ∧
      ‖fderiv ℝ (D.residual i) u‖ ≤ Cr*(D.ell*D.width)*Real.sqrt (D.selector i u)) :
    ∃ t η ζ cn CR : ℝ,
    t = descentThreshold (Cr+Cs) ∧
    sourceAmplitudeConstant 3 1 ζ cn η ≤ releaseTolerance (Cr+Cs)/4 ∧
    η^2 ≤ releaseTolerance (Cr+Cs)/(2*(gaussianBound+releaseTolerance (Cr+Cs))) ∧
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ 128≤cn/η^2 ∧ 1≤CR ∧
    ∀ (F : Type u) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r : ℕ → ℝ),(∀ j,1≤r j) → ∀ (K : ℝ),0<K → 1/η≤K →
      ∀ (U : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (resolution η K j)) →ₗᵢ[ℝ] F),
      let b := fun j => t^(j+1)
      let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR U
      let R := fun j => (D j []).radius
      let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
      ∀ (J : ℕ) (u : ℕ → F) (w Rp : ℝ),t≤w → w≤1 → Rp≤0 → |Rp|≤gaussianBound*initial.energy →
        (D 0 []).release (u 0)<1 → ∃ k : ℕ,k≤J ∧
        t^(J+1)*(η^J*(initial.force/K))/4≤
          ‖fderiv ℝ (fun v => objective D ρ R J 0 [] w Rp (Function.update u k v)) (u k)‖ := by

  have hC : 0≤Cr+Cs := add_nonneg hCr hCs
  let t := descentThreshold (Cr+Cs)
  let δ := releaseTolerance (Cr+Cs)
  have ht : 0<t ∧ t<1 ∧ 0<δ := descentThreshold_range hC
  have hδpos : 0<δ := ht.2.2
  have hg0 := gaussianBound_nonneg
  have hd : 0<gaussianBound+δ := by linarith [ht.2.2]
  obtain ⟨ζ,cn,η,hζ,hζsmall,hcn,hη,hη1,hlen,henergy,hamp⟩ :=
    exists_source_small_parameters (A:=3) (K:=1) (δ:=δ/4) (q:=δ/(2*(gaussianBound+δ)))
      (by norm_num) (by norm_num) (by positivity) (by positivity)
  obtain ⟨CR,hCR1,hCRsqrt,hfamily⟩ := source_uniform_eta_margins 3 1 ζ cn η gaussianBound
    (by norm_num) (by norm_num) hζ hζsmall hcn hη hlen hg0
  have hCR : 0<CR := lt_of_lt_of_le (by norm_num) hCR1
  have hsmall : δ/4+(gaussianBound+δ)*η^2≤δ := by
    have he := (le_div_iff₀ (show 0<2*(gaussianBound+δ) by positivity)).mp henergy
    nlinarith only [he,ht.2.2]
  refine ⟨t,η,ζ,cn,CR,rfl,hamp,henergy,ht.1,ht.2.1,hη,hη1,hζ,hζsmall,hcn,hlen,hCR1,?_⟩
  intro F _ _ _ initial hl hh r hr K hK hKth U
  dsimp only
  let b := fun j : ℕ => t^(j+1)
  let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR U
  let R := fun j => (D j []).radius
  let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
  let cap := fun j => gaussianBound*(parentScale initial r (resolution η K) j).energy
  have hres : ∀ j,0<resolution η K j := base_resolution_positive hη hK
  have hresle : ∀ j,resolution η K j≤η := base_resolution_le hK hKth hη
  have hp := parentScale_positive initial r (resolution η K) hl hh hr hres
  have hb : ∀ j,0<b j := fun j => pow_pos ht.1 _
  have hbnext : ∀ j,b (j+1)=b j*descentThreshold (Cr+Cs) := by intro j;simp only [b,pow_succ];rfl
  have hell : ∀ j I,0≤(D j I).ell := by
    intro j I
    exact mul_nonneg (by linarith [hr j]) (hp j).1.le
  have hwidth : ∀ j I,0<(D j I).width := by
    intro j I
    exact div_pos (mul_pos (hres j) (hp j).2) (by linarith [hr j])
  have hradius : ∀ j,0<R j := by
    intro j
    have hr0 : 0<r j := by linarith [hr j]
    exact div_pos (mul_pos (mul_pos hCR (mul_pos (hp j).1 (hp j).2)) (Real.sqrt_pos.mpr hr0))
      (mul_pos (hb j) (mul_pos hζ (hp j).1))
  have hR : ∀ j I,R j=(D j I).radius := fun _ _ => rfl
  have hcap : ∀ j I,gaussianBound*((D j I).ell*(D j I).width^2)≤cap (j+1) := fun _ _ => le_rfl
  intro J u w Rp hw hw1 hRp hRpbound hrelease
  have hder : ∀ j I i,
      ‖fderiv ℝ ((D j I).selector i) (u j)‖≤(Cs/(D j I).width)*Real.sqrt ((D j I).selector i (u j)) ∧
      ‖fderiv ℝ ((D j I).residual i) (u j)‖≤Cr*((D j I).ell*(D j I).width)*Real.sqrt ((D j I).selector i (u j)) :=
    fun j I i => hderiv F (D j I) (hell j I) (hwidth j I) (by rw [← hR j I];exact hradius j) i (u j)
  have hW : ∀ d j I (i : Fin ((D j I).n+1)),
      |payloadValue D d (j+1) (child I i.val) u|≤δ*((D j I).ell*(D j I).width^2) := by
    intro d j I i
    exact sourceGeometry_payload_bound initial r (resolution η K) b 3 1 ζ cn CR U
      hl hh hr hres hη hresle (by norm_num) (by norm_num) hζ hcn hlen ht.2.2.le
      (by positivity) (by linarith [ht.2.2]) hamp hsmall d (j+1) (child I i.val) u
  have hlocal : ∀ j I w Rp,b j≤w → w≤1 → Rp≤0 → |Rp|≤cap j → (D j I).release (u j)<1 →
      (b j*((D j I).ell*(D j I).width)/2≤‖fderiv ℝ ((D j I).localBase (ρ j) w Rp) (u j)‖) ∧
      (|(D j I).coordinates (u j) (Fin.last (D j I).n)|<(D j I).width/2 →
        w*((D j I).ell*(D j I).width)/2≤‖fderiv ℝ ((D j I).localBase (ρ j) w Rp) (u j)‖) := by
    intro j I w' Rp' hw' hw1' hRp' hcap' hQ
    have hloc := hfamily (resolution η K j) (parentScale initial r (resolution η K) j).curvature
      (parentScale initial r (resolution η K) j).width (r j) (b j) w' Rp' (hres j) (hresle j)
      (hp j).1 (hp j).2 (hr j) (hb j) hw' hw1' hRp'
      (by simpa only [cap,Scale.energy,mul_assoc] using hcap') F (U j I) (u j)
    have hg : (D j I).ell*(D j I).width=
        resolution η K j*((parentScale initial r (resolution η K) j).curvature*
          (parentScale initial r (resolution η K) j).width) := by
      have hr0 : 0<r j := by linarith [hr j]
      dsimp only [D,sourceGeometry,sourceNode]
      field_simp
      ring
    refine ⟨?_,?_⟩
    · rw [norm_fderiv_eq_norm_gradient,hg]
      exact hloc.1 hQ
    · intro ha
      rw [norm_fderiv_eq_norm_gradient,hg]
      exact hloc.2 ha
  have htarget : ∀ k P,0≤k → k≤0+J →
      t^(J+1)*(η^J*(initial.force/K))/4≤b k*((D k P).ell*(D k P).width)/4 := by
    intro k P _ hk
    change _≤t^(k+1)*(parentScale initial r (resolution η K) (k+1)).force/4
    rw [source_force_formula initial r hr]
    exact geometric_margin_comparison ht.1.le ht.2.1.le hη.le hη1
      (div_nonneg (mul_nonneg hl.le hh.le) hK.le) (by omega)
  obtain ⟨k,_,hk,hbound⟩ := objective_block_barrier D ρ R b cap u hCs hCr ht.2.2.le le_rfl
    (fun j => (hb j).le) hbnext hell hwidth hradius hR hcap
    (fun j I i => (hder j I i).1) (fun j I i => (hder j I i).2) hW hlocal J 0 []
    (w:=w) (Rp:=Rp) (by simpa only [b,zero_add,pow_one] using hw) hw1 hRp hRpbound hrelease htarget
  exact ⟨k,by omega,hbound⟩

end Bilevel.ChiRecursive
