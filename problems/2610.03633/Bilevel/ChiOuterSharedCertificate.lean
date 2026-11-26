import Bilevel.ChiOuterSharedCalibration
import Bilevel.ChiOuterCoercive

/-! Deterministic source objective certificate with the shared carrier constants: the same fixed
numerical geometry constants give a depth-uniform full-gradient barrier,
coercivity, zero initial value, and the actual initial gap. This does not
assert a stochastic-oracle lower bound or a calibrated bilevel lift. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
universe u

set_option maxHeartbeats 1200000 in
theorem source_shared_objective_certificate : ∃ t η ζ cn CR Km Cgap : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧
    cn≤1 ∧ 128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (n : ℕ) (initial : Scale),0 < initial.curvature → 0 < initial.width →
      ∀ (r : ℕ → ℝ),(∀ j,1≤r j) → ∀ (K : ℝ),0<K → 1/η≤K →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (resolution η K j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let b := fun j => t^(j+1)
      let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
      ∀ J : ℕ,
      let f := jointOuter (J+1) M (initial.curvature/24) D ρ R J K
      Tendsto f (cocompact (Joint E (Blocks (J+1) F))) atTop ∧ f 0=0 ∧
      f 0-sInf (Set.range f)≤Cgap*((n:ℝ)+1)*initial.energy ∧
      ∀ z,M.coordinates z.fst (Fin.last n) < initial.width →
        t^(J+1)*(η^J*initial.force)/4≤‖gradient f z‖ := by
  obtain ⟨Cs,Cr,t,η,ζ,cn,CR,Km,hCs,hCr,hteq,hamp,henergy,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRsqrt,hKm1,hbarrier⟩ :=
    source_outer_shared_barrier.{u}
  have hKm : 0<Km := by linarith
  let δ := releaseTolerance (Cr+Cs)
  have hδ : 0<δ := (descentThreshold_range (add_nonneg hCr hCs)).2.2
  let Cgap := 1+gaussianBound+δ
  have hG := gaussianBound_nonneg
  have hCg : 1≤Cgap := by dsimp [Cgap];linarith
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRsqrt,hKm1,hCg,?_⟩
  intro E F _ _ _ _ _ _ _ _ n initial hell hh r hr K hK hKth U V
  dsimp only
  let M := sourceMacroNode n initial Km U
  let b := fun j : ℕ => t^(j+1)
  let D := sourceGeometry initial r (resolution η K) b 3 1 ζ cn CR V
  let R := fun j => (D j []).radius
  let ρ := fun j => b j*(ζ*(parentScale initial r (resolution η K) j).curvature)
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hKth hη
  have hp := parentScale_positive initial r (resolution η K) hell hh hr hres
  have hCR0 : 0<CR := by linarith
  have hb : ∀ j,0<b j := fun j => pow_pos ht _
  have hρ : ∀ j,0<ρ j := fun j => mul_pos (hb j) (mul_pos hζ (hp j).1)
  have hR : ∀ j,0<R j := by
    intro j
    exact div_pos (mul_pos (mul_pos hCR0 (mul_pos (hp j).1 (hp j).2))
      (Real.sqrt_pos.mpr (by linarith [hr j]))) (mul_pos (hb j) (mul_pos hζ (hp j).1))
  have hRM : 0<M.radius := mul_pos (mul_pos hKm hh) (Real.sqrt_pos.mpr (by positivity))
  have hν : 0 < initial.curvature/24 := by positivity
  have hsmall : δ/4+(gaussianBound+δ)*η^2≤δ := by
    have hden : 0<2*(gaussianBound+δ) := by positivity
    have he := (le_div_iff₀ hden).mp henergy
    nlinarith only [he,hδ]
  have he0 : 0 ≤ initial.energy := mul_nonneg hell.le (sq_nonneg _)
  intro J
  have hW : ∀ v i,|payloadValue D J 0 [i] v|≤δ*initial.energy := by
    intro v i
    exact sourceGeometry_payload_bound initial r (resolution η K) b 3 1 ζ cn CR V hell hh hr
      hres hη hresle (by norm_num) (by norm_num) hζ hcn hlen hδ.le (by positivity)
      (by linarith) hamp hsmall J 0 [i] v
  have hB : 0≤δ*initial.energy := mul_nonneg hδ.le he0
  refine ⟨jointOuter_coercive M _ D ρ R J K hK hell.le hν hRM hρ hR _ hB hW,
    jointOuter_zero _ M _ D ρ R J K,?_,?_⟩
  · have hg := jointOuter_gap_to_infimum M _ D ρ R J K hK hell.le hν hRM hρ hR _ hB hW
    apply hg.trans
    change ((n:ℝ)+1)*gaussianBound*initial.energy+δ*initial.energy≤Cgap*((n:ℝ)+1)*initial.energy
    have hn : (1:ℝ)≤(n:ℝ)+1 := by
      have hh : (0:ℝ)≤(n:ℝ) := Nat.cast_nonneg n
      linarith
    have hcoeff : ((n:ℝ)+1)*gaussianBound+δ≤Cgap*((n:ℝ)+1) := by
      dsimp only [Cgap]
      nlinarith only [hn,mul_nonneg hδ.le (Nat.cast_nonneg n)]
    have hh := mul_le_mul_of_nonneg_right hcoeff he0
    nlinarith only [hh]
  · intro z hlast
    exact jointOuter_gradient_of_blocks M _ D ρ R J K hK z.fst z.snd _
      (hbarrier E F n initial hell hh r hr K hK hKth U V J z.fst (padded (K • z.snd)) hlast)

end Bilevel.ChiOuter
