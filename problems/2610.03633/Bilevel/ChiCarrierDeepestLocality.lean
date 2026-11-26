import Bilevel.ChiCarrierCoarseLocality
import Bilevel.ChiBoundedChainJets

/-! The deepest revealed carrier uses the centered frontier. Its exact
subtraction cancels the prospective next coordinate even with both terminal
receivers, and this support survives every ancestor selector. -/
noncomputable section
namespace Bilevel.ChiBoundedChain

theorem centeredPayload_gradient_support (n r : ℕ) (ℓ h A ν g hp T : ℝ) (hh : 0<h)
    (z : Space n) (hz : ∀ k : Fin (n+1),r ≤ k.val → |z k|≤h/4)
    (k : Fin (n+1)) (hk : r ≤ k.val) :
    gradient (fun y => payload n ℓ h A ν g hp T y-ChiFine.frontier n ℓ h y) z k=0 := by
  have hlast : |z (Fin.last n)|≤h/4 := hz (Fin.last n) (by have := k.isLt;simp;omega)
  have hpay := payload_gradient_eq_chain n ℓ h A ν g hp T hh z hlast
  have he : (fun y => chain n ℓ h y-ChiFine.frontier n ℓ h y)=Acentered n ℓ h := by
    funext y
    change chain n ℓ h y-Rcentered n ℓ h y=Acentered n ℓ h y
    linarith [scaled_centered_exact_split n ℓ h y]
  rw [ChiFine.gradient_sub_C3 (payload_contDiff n ℓ h A ν g hp T 3) (ChiFine.frontier_contDiff n ℓ h),hpay,
    ← ChiFine.gradient_sub_C3 (Jets.chain_contDiff n 3 ℓ h) (ChiFine.frontier_contDiff n ℓ h),he]
  exact Acentered_gradient_support n r ℓ h hh z hz k hk

end Bilevel.ChiBoundedChain

namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def deepestCarrier (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) : Blocks m E → ℝ :=
  fun x => jointCarrier m D d j I d x-selectedFineFrontier m D d j I x

theorem deepestCarrier_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (deepestCarrier m D d j I) :=
  (jointCarrier_contDiff m D d j I d 3).sub (selectedFineFrontier_contDiff m D d j I)

theorem deepestCarrier_eq_selected (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ) :
    deepestCarrier m D d j I=selectFamily m D
      (fun k P x => jointCarrier m D 0 k P 0 x-jointFineFrontier m k (D k P) x) d j I := by
  have hcarrier := jointCarrier_selectFamily m D 0 d j I
  simp only [zero_add] at hcarrier
  funext x
  rw [deepestCarrier,hcarrier]
  exact (selectFamily_sub m D (fun k P => jointCarrier m D 0 k P 0)
    (fun k P => jointFineFrontier m k (D k P)) d j I x).symm

theorem jointDeepest_gradient_mem {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (j : Fin m) (D : Geometry E) (I : List ℕ) (r : ℕ)
    (hb : BlindNode W x j (D j.val I) r) :
    gradient (fun y => jointCarrier m D 0 j.val I 0 y-jointFineFrontier m j.val (D j.val I) y) x∈knownSpace W := by
  let N := D j.val I
  let f : Space N.n → ℝ := fun z => payload N.n N.ell N.width N.receiver N.nu N.force N.parentWidth N.tailRadius z-
    ChiFine.frontier N.n N.ell N.width z
  have hf : ContDiff ℝ 3 f := (payload_contDiff _ _ _ _ _ _ _ _ 3).sub (ChiFine.frontier_contDiff _ _ _)
  have hfc := hf.comp (N.coordinates_contDiff 3)
  have hm : gradient (f ∘ N.coordinates) (x j)∈W j :=
    WrappedPrefixLocality.carried_gradient_mem N.n r N.radius hb.radius_pos N.frame f
      (hf.differentiable (by norm_num)) (x j) (W j) hb.query_mem hb.columns_mem
      (fun k hk => centeredPayload_gradient_support _ r _ _ _ _ _ _ _ hb.width_pos _ hb.blind k hk)
  have hs := block_composition_gradient_mem W x j (hfc.sub contDiff_const)
    (gradient_sub_const_mem (W j) hfc (x j) (N.H 0) hm)
  convert hs using 1
  congr 1
  funext y
  dsimp only [jointCarrier,selectedCarrier,padded,jointFineFrontier,Function.comp_apply,f,N,Node.H]
  ring

theorem deepestCarrier_gradient_mem {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (htree : TreeBlind D j d hm W x r) : gradient (deepestCarrier m D d j I) x∈knownSpace W := by
  rw [deepestCarrier_eq_selected]
  apply selectFamily_gradient_mem_of_blind D _
    (fun k P => (jointCarrier_contDiff m D 0 k P 0 3).sub (jointFineFrontier_contDiff m k (D k P)))
    d j I hm W x r (fun k P hk hkt => htree k P hk (by omega))
  intro P
  exact jointDeepest_gradient_mem W x ⟨j+d,hm⟩ D P (r (j+d) P) (htree (j+d) P (by omega) le_rfl)

end Bilevel.ChiCarrier
