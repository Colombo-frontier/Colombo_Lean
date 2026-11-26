import Bilevel.ChiOuterJoint
import Bilevel.ChiOuterGap

/-! Zero value and bounded negative part of the actual outer attachment.
The public radial penalties remain outside every selector. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper ZeroChainPotential
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem macro_zero_residual_sum (M : Node E) (ν : ℝ) :
    macroValue M.n M.ell M.width ν M.radius M.frame 0=∑ i : Fin (M.n+1),wrappedResidual M i 0 := by
  have hp : psi 0=0 := psi_zero (by norm_num)
  have hm : tailMask (0:Fin (M.n+1)) (0:Space M.n)=1 :=
    tailMask_one_of_small _ _ (by intros;simp)
  rw [macro_zero]
  simp only [wrappedResidual,Node.coordinates_zero,smul_zero]
  rw [Fin.sum_univ_succ]
  simp [residualTerm,selector,hp,hm]

omit [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem publicValue_zero (ρ R : ℕ → ℝ) (d j : ℕ) : publicValue (E:=F) ρ R d j (fun _ => 0)=0 := by
  induction d generalizing j with
  | zero => simp [publicValue,bowl]
  | succ d ih => simp [publicValue,ih,bowl]

omit [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem publicValue_nonneg (ρ R : ℕ → ℝ) (hρ : ∀ k,0≤ρ k) (d j : ℕ) (v : ℕ → F) :
    0≤publicValue ρ R d j v := by
  induction d generalizing j with
  | zero => exact bowl_nonnegative _ _ (hρ _) _
  | succ d ih => exact add_nonneg (bowl_nonnegative _ _ (hρ _) _) (ih (j+1))

theorem outerObjective_zero (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ) :
    outerObjective M ν D ρ R d 0 (fun _ => 0)=0 := by
  simp only [outerObjective,attachment,Node.release_zero,payloadValue_zero,publicValue_zero,
    zero_sub,neg_mul,one_mul,zero_mul,add_zero]
  rw [macro_zero_residual_sum,Finset.sum_neg_distrib,add_neg_cancel]

theorem jointOuter_zero (m : ℕ) (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ) :
    jointOuter m M ν D ρ R d K 0=0 := by
  change outerObjective M ν D ρ R d 0 (padded (K • (0:Blocks m F)))=0
  have hp : padded (0:Blocks m F)=fun _ => 0 := by funext j; exact map_zero _
  rw [smul_zero,hp,outerObjective_zero]

theorem attachment_lower (M : Node E) (ν : ℝ) (Q W : Fin (M.n+1) → ℝ)
    (hℓ : 0≤M.ell) (B : ℝ) (hB : 0≤B) (hQ : ∀ i,Q i≤1) (hW : ∀ i,-B≤W i) (x : E) :
    macroValue M.n M.ell M.width ν M.radius M.frame x-B≤attachment M ν Q W x := by
  have ht (i : Fin (M.n+1)) : -B*wrappedSelector M i x≤
      (Q i-1)*wrappedResidual M i x+W i*wrappedSelector M i x := by
    have hprod : 0≤(Q i-1)*wrappedResidual M i x :=
      mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hQ i)) (wrappedResidual_nonpos M hℓ i x)
    have hw := mul_le_mul_of_nonneg_right (hW i) (wrappedSelector_range M i x).1
    linarith
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ:Finset (Fin (M.n+1)))) => ht i)
  rw [← Finset.mul_sum] at hs
  have hb := mul_le_mul_of_nonpos_left (wrappedSelector_sum M x) (neg_nonpos.mpr hB)
  unfold attachment
  linarith

theorem outerObjective_lower (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ)
    (hℓ : 0≤M.ell) (B : ℝ) (hB : 0≤B) (x : E) (v : ℕ → F)
    (hW : ∀ i : Fin (M.n+1),|payloadValue D d 0 [i.val] v|≤B) :
    macroValue M.n M.ell M.width ν M.radius M.frame x+publicValue ρ R d 0 v-B≤
      outerObjective M ν D ρ R d x v := by
  have ht := attachment_lower M ν _ _ hℓ B hB
    (fun i => ((D 0 [i.val]).release_range (v 0)).2) (fun i => (abs_le.mp (hW i)).1) x
  unfold outerObjective
  linarith

theorem jointOuter_pointwise_gap (M : Node E) (ν : ℝ) (D : Geometry F) (ρ R : ℕ → ℝ) (d : ℕ) (K : ℝ)
    (hℓ : 0≤M.ell) (hν : 0≤ν) (hρ : ∀ k,0≤ρ k) (B : ℝ) (hB : 0≤B)
    (hW : ∀ v i,|payloadValue D d 0 [i] v|≤B) (z : Joint E (Blocks (d+1) F)) :
    jointOuter (d+1) M ν D ρ R d K 0-jointOuter (d+1) M ν D ρ R d K z≤
      ((M.n:ℝ)+1)*gaussianBound*(M.ell*M.width^2)+B := by
  rw [jointOuter_zero]
  have ht := outerObjective_lower M ν D ρ R d hℓ B hB z.fst (padded (K • z.snd))
    (fun i => hW _ i.val)
  have hp := publicValue_nonneg ρ R hρ d 0 (padded (K • z.snd))
  have hb := bowl_nonnegative ν M.radius hν z.fst
  have hc := chain_lower M.n M.ell M.width hℓ (WrappedChain.coordinates M.n M.radius M.frame z.fst)
  change -((M.n:ℝ)+1)*gaussianBound*(M.ell*M.width^2)≤
    chain M.n M.ell M.width (WrappedChain.coordinates M.n M.radius M.frame z.fst) at hc
  change 0-(outerObjective M ν D ρ R d z.fst (padded (K • z.snd)))≤_
  change chain M.n M.ell M.width (WrappedChain.coordinates M.n M.radius M.frame z.fst)+
    bowl ν M.radius z.fst+publicValue ρ R d 0 (padded (K • z.snd))-B≤_ at ht
  linarith

end Bilevel.ChiOuter
