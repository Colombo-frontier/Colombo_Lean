import Bilevel.ChiOuterValue

/-! Finite-product geometry for the coercivity proof of the actual recursive
objective. Every lower block is controlled by its own unselected radial
penalty; no geometric value is multiplied by a selector. -/
noncomputable section
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry RadialWrapper
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace F] in
theorem publicValue_sum (ρ R : ℕ → ℝ) (d j : ℕ) (v : ℕ → F) :
    publicValue ρ R d j v=∑ i : Fin (d+1),bowl (ρ (j+i.val)) (R (j+i.val)) (v (j+i.val)) := by
  induction d generalizing j with
  | zero => simp [publicValue]
  | succ d ih =>
    rw [publicValue,Fin.sum_univ_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have he : j+1+i.val=j+(i.val+1) := by omega
    rw [he]

omit [CompleteSpace F] in
theorem blocks_norm_le_sum (m : ℕ) (x : Blocks m F) : ‖x‖≤∑ i : Fin m,‖x i‖ := by
  have he : (∑ i : Fin m,insertion m i (x i))=x := by
    apply PiLp.ext
    intro j
    change (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin m => F) j) (∑ i : Fin m,insertion m i (x i))=x j
    rw [map_sum]
    simp [PiLp.proj_apply,insertion_apply]
  rw [← he] at ⊢
  have hn := norm_sum_le (Finset.univ) (fun i : Fin m => insertion m i (x i))
  simpa only [he,LinearIsometry.norm_map] using hn

omit [CompleteSpace F] in
theorem joint_norm_le_block_sum (m : ℕ) (z : Joint E (Blocks m F)) :
    ‖z‖≤‖z.fst‖+∑ i : Fin m,‖z.snd i‖ := by
  have hp : ‖z‖≤‖z.fst‖+‖z.snd‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [PrimitiveGeometry.norm_sq]
    nlinarith [mul_nonneg (norm_nonneg z.fst) (norm_nonneg z.snd)]
  exact hp.trans (add_le_add_left (blocks_norm_le_sum m z.snd) _)

theorem finite_positive_lower (f : ℕ → ℝ) (hf : ∀ j,0<f j) (d : ℕ) :
    ∃ a : ℝ,0<a ∧ ∀ j,j≤d → a≤f j := by
  induction d with
  | zero =>
    refine ⟨f 0,hf 0,fun j hj => ?_⟩
    have he : j=0 := by omega
    rw [he]
  | succ d ih =>
    obtain ⟨a,ha,hbound⟩ := ih
    refine ⟨min a (f (d+1)),lt_min ha (hf (d+1)),fun j hj => ?_⟩
    by_cases h : j≤d
    · exact (min_le_left _ _).trans (hbound j h)
    · have he : j=d+1 := by omega
      simpa only [he] using min_le_right a (f (d+1))

omit [CompleteSpace F] in
theorem publicValue_linear_lower (ρ R : ℕ → ℝ) (hρ : ∀ j,0≤ρ j) (hR : ∀ j,0<R j)
    (d : ℕ) (K a : ℝ) (hK : 0<K) (ha : ∀ j,j≤d → a≤ρ j*R j*K) (v : Blocks (d+1) F) :
    a*(∑ i : Fin (d+1),‖v i‖)-(∑ i : Fin (d+1),ρ i.val*(R i.val)^2)≤
      publicValue ρ R d 0 (padded (K • v)) := by
  have ht (i : Fin (d+1)) : a*‖v i‖-ρ i.val*(R i.val)^2≤
      bowl (ρ i.val) (R i.val) (padded (K • v) i.val) := by
    have hb := bowl_linear_lower (ρ i.val) (R i.val) (hρ _) (hR _) (padded (K • v) i.val)
    have hp : padded (K • v) i.val=K • v i := by
      simp [padded,block,i.isLt,PiLp.smul_apply]
    rw [hp,norm_smul,Real.norm_eq_abs,abs_of_pos hK] at hb
    rw [hp]
    have hc := mul_le_mul_of_nonneg_right (ha i.val (by omega)) (norm_nonneg (v i))
    nlinarith only [hb,hc]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ:Finset (Fin (d+1)))) => ht i)
  rw [publicValue_sum]
  simpa only [Finset.sum_sub_distrib,← Finset.mul_sum,Nat.zero_add] using hs

end Bilevel.ChiOuter
