import Bilevel.ChiOuterCoerciveGeometry

/-! Coercivity and an attained initial-gap bound for the actual finite
outer-plus-recursive objective. Only the proved bounded payload interface
remains as an input here; the public penalties are actual radial bowls. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem jointOuter_linear_lower (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (hK : 0<K) (hℓ : 0≤M.ell) (hν : 0<ν) (hRM : 0<M.radius)
    (hρ : ∀ j,0<ρ j) (hR : ∀ j,0<R j) (B : ℝ) (hB : 0≤B)
    (hW : ∀ v i,|payloadValue D d 0 [i] v|≤B) :
    ∃ a c : ℝ,0<a ∧ ∀ z : Joint E (Blocks (d+1) F),
      a*‖z‖-c≤jointOuter (d+1) M ν D ρ R d K z := by
  obtain ⟨a₀,ha₀,haall⟩ := finite_positive_lower (fun j => ρ j*R j*K)
    (fun j => mul_pos (mul_pos (hρ j) (hR j)) hK) d
  let a := min (ν*M.radius) a₀
  let c := ((M.n:ℝ)+1)*gaussianBound*(M.ell*M.width^2)+B+ν*M.radius^2+
    ∑ i : Fin (d+1),ρ i.val*(R i.val)^2
  have ha : 0<a := lt_min (mul_pos hν hRM) ha₀
  have ham : a≤ν*M.radius := min_le_left _ _
  have hai : ∀ j,j≤d → a≤ρ j*R j*K := fun j hj => (min_le_right _ _).trans (haall j hj)
  refine ⟨a,c,ha,fun z => ?_⟩
  have hlow := outerObjective_lower M ν D ρ R d hℓ B hB z.fst (padded (K • z.snd))
    (fun i => hW _ i.val)
  have hpub := publicValue_linear_lower ρ R (fun j => (hρ j).le) hR d K a hK hai z.snd
  have hmacro := bowl_linear_lower ν M.radius hν.le hRM z.fst
  have hmacrocoef := mul_le_mul_of_nonneg_right ham (norm_nonneg z.fst)
  have hchain := chain_lower M.n M.ell M.width hℓ (WrappedChain.coordinates M.n M.radius M.frame z.fst)
  have hnorm := mul_le_mul_of_nonneg_left (joint_norm_le_block_sum (d+1) z) ha.le
  change chain M.n M.ell M.width (WrappedChain.coordinates M.n M.radius M.frame z.fst)+
    bowl ν M.radius z.fst+publicValue ρ R d 0 (padded (K • z.snd))-B≤_ at hlow
  change a*‖z‖-c≤outerObjective M ν D ρ R d z.fst (padded (K • z.snd))
  dsimp only [c]
  nlinarith only [hlow,hpub,hmacro,hmacrocoef,hchain,hnorm]

theorem jointOuter_coercive [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (hK : 0<K) (hℓ : 0≤M.ell) (hν : 0<ν) (hRM : 0<M.radius)
    (hρ : ∀ j,0<ρ j) (hR : ∀ j,0<R j) (B : ℝ) (hB : 0≤B)
    (hW : ∀ v i,|payloadValue D d 0 [i] v|≤B) :
    Tendsto (jointOuter (d+1) M ν D ρ R d K) (cocompact (Joint E (Blocks (d+1) F))) atTop := by
  obtain ⟨a,c,ha,hbound⟩ := jointOuter_linear_lower M ν D ρ R d K hK hℓ hν hRM hρ hR B hB hW
  apply tendsto_atTop.2
  intro b
  have hn := (tendsto_norm_cocompact_atTop (E:=Joint E (Blocks (d+1) F))).eventually_ge_atTop ((b+c)/a)
  filter_upwards [hn] with z hz
  have hh := (div_le_iff₀ ha).mp hz
  have hb := hbound z
  nlinarith only [hh,hb]

theorem jointOuter_minimum_attained [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (hK : 0<K) (hℓ : 0≤M.ell) (hν : 0<ν) (hRM : 0<M.radius)
    (hρ : ∀ j,0<ρ j) (hR : ∀ j,0<R j) (B : ℝ) (hB : 0≤B)
    (hW : ∀ v i,|payloadValue D d 0 [i] v|≤B) :
    ∃ z : Joint E (Blocks (d+1) F),∀ w,
      jointOuter (d+1) M ν D ρ R d K z≤jointOuter (d+1) M ν D ρ R d K w :=
  ((jointOuter_contDiff (d+1) M ν D ρ R d K 0).continuous).exists_forall_le
    (jointOuter_coercive M ν D ρ R d K hK hℓ hν hRM hρ hR B hB hW)

theorem jointOuter_gap_to_infimum [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ)
    (d : ℕ) (K : ℝ) (hK : 0<K) (hℓ : 0≤M.ell) (hν : 0<ν) (hRM : 0<M.radius)
    (hρ : ∀ j,0<ρ j) (hR : ∀ j,0<R j) (B : ℝ) (hB : 0≤B)
    (hW : ∀ v i,|payloadValue D d 0 [i] v|≤B) :
    jointOuter (d+1) M ν D ρ R d K 0-sInf (Set.range (jointOuter (d+1) M ν D ρ R d K))≤
      ((M.n:ℝ)+1)*gaussianBound*(M.ell*M.width^2)+B := by
  obtain ⟨z,hz⟩ := jointOuter_minimum_attained M ν D ρ R d K hK hℓ hν hRM hρ hR B hB hW
  have he : sInf (Set.range (jointOuter (d+1) M ν D ρ R d K))=jointOuter (d+1) M ν D ρ R d K z := by
    apply le_antisymm
    · exact csInf_le ⟨_,by rintro _ ⟨w,rfl⟩;exact hz w⟩ ⟨z,rfl⟩
    · apply le_csInf (Set.range_nonempty _)
      rintro _ ⟨w,rfl⟩
      exact hz w
  rw [he]
  exact jointOuter_pointwise_gap M ν D ρ R d K hℓ hν.le (fun j => (hρ j).le) B hB hW z

end Bilevel.ChiOuter
