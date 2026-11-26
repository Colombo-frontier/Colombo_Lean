import Bilevel.ChiFineFlattening

/-! Dimension-free derivative bounds for the actual centered frontier and
its incoming-coordinate flattening. Constants are obtained from the fixed
smooth profiles and actual selector jets. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiFine
open ChiBoundedChain ZeroChainPotential ZeroChainFlatteningBounds ZeroChainFlatteningMap

theorem centered_uniform_jet_bound : ∃ M : ℝ,1≤M ∧
    ∀ (n k : ℕ),k≤3 → ∀ z : Space n,‖iteratedFDeriv ℝ k (centeredResidual n) z‖≤M := by
  obtain ⟨B,hB,hsel⟩ := selector_uniform_jet_bound
  obtain ⟨K,hK,hprof⟩ := chain_profile_bound
  let S := 1+∑ j,B j
  have hS : 1≤S := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hB j))
  have hbS (j : Fin 4) : B j≤S := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hB l) (Finset.mem_univ j)
    dsimp [S]
    linarith
  let f : ℝ → ℝ := fun t => -(phi t-phi 0)
  have hf : ContDiff ℝ 3 f := ((phi_contDiff 3).sub contDiff_const).neg
  have hfb (k : ℕ) (hk : k≤3) (t : ℝ) : |iteratedDeriv k f t|≤2*K := by
    by_cases hz : k=0
    · subst k
      simp only [iteratedDeriv_zero,f,abs_neg]
      have hh := abs_sub (phi t) (phi 0)
      have ha := (hprof 0 t).2
      have hb := (hprof 0 0).2
      simp only [Fin.val_zero,iteratedDeriv_zero] at ha hb
      linarith
    · have he : f=fun t => phi 0-phi t := by funext t;dsimp [f];ring
      rw [he,iteratedDeriv_const_sub (by omega)]
      change |iteratedDeriv k (fun u => -phi u) t|≤2*K
      rw [iteratedDeriv_neg,abs_neg]
      exact ((hprof ⟨k,by omega⟩ t).2).trans (by linarith)
  let D : Fin 4 → ℝ := fun k =>
    ∑ j ∈ Finset.range (k.val+1),(k.val.choose j:ℝ)*S*(2*K)
  have hD (j : Fin 4) : 0≤D j := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith)
  let M := 1+∑ j,D j
  have hM : 1≤M := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hD j))
  have hdM (j : Fin 4) : D j≤M := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hD l) (Finset.mem_univ j)
    dsimp [M]
    linarith
  refine ⟨M,hM,fun n k hk z => ?_⟩
  rw [centered_eq_selected]
  have hh := selected_jet_bound n hf (fun _ => S) (fun _ => 2*K) (fun _ => by linarith)
    (fun i w j hj => (hsel ⟨j,by omega⟩ n i w).trans (hbS _)) hfb z k hk
  exact hh.trans (hdM ⟨k,by omega⟩)

theorem flattened_positive_jet_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (n : ℕ) (δ : ℝ),0<δ → δ≤1/16 → ∀ (j : Fin 3) (z : Space n),
      ‖iteratedFDeriv ℝ (j.val+1) (flattened n δ) z‖≤C/δ^j.val := by
  obtain ⟨M,hM,hm⟩ := centered_uniform_jet_bound
  obtain ⟨K,hK,hcore⟩ := coreMap_common_jet_bound
  let d : Fin 3 → ℝ := fun j => ((j.val+1).factorial:ℝ)*M*K^(j.val+1)
  have hd (j : Fin 3) : 0≤d j := by dsimp [d];positivity
  let C := 1+∑ j,d j
  have hC : 1≤C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hd j))
  have hdC (j : Fin 3) : d j≤C := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hd l) (Finset.mem_univ j)
    dsimp [C]
    linarith
  refine ⟨C,hC,fun n δ hδ hs j z => ?_⟩
  have ho (k : ℕ) (hk0 : 1≤k) (hk : k≤3) (w : Space n) :
      ‖iteratedFDeriv ℝ k (centeredResidual n) w‖≤M*δ/δ^k := by
    apply (hm n k hk w).trans
    have hp : δ^k≤δ := by
      simpa only [pow_one] using pow_le_pow_of_le_one hδ.le (by linarith : δ≤1) hk0
    exact (le_div_iff₀ (pow_pos hδ k)).mpr (mul_le_mul_of_nonneg_left hp (by linarith))
  have hh := flatten_positive_jet_bound (centeredResidual_contDiff n 3) K M δ hK
    (by linarith) hδ (hcore n) ho z (j.val+1) (by omega) (by omega)
  have he : (fun w => centeredResidual n (flattenMap n δ w))=flattened n δ :=
    funext (fun w => (flattened_eq_latent_composition hδ hs n w).symm)
  rw [he] at hh
  have ha : ((j.val+1).factorial:ℝ)*M*K^(j.val+1)*δ/δ^(j.val+1)=d j/δ^j.val := by
    dsimp [d]
    rw [pow_succ]
    field_simp
    ring
  rw [ha] at hh
  exact hh.trans (div_le_div_of_nonneg_right (hdC j) (pow_nonneg hδ.le _))

end Bilevel.ChiFine
