import Bilevel.ChiSourceSharedSpace
import Bilevel.ChiCanonicalFrameFamily

/-! Finite same-run energy bounds imply all-list canonical projection
bounds. Prefix columns are in the fresh shared space, and a successful
counter advance only enlarges that space. -/
noncomputable section
namespace Bilevel.ChiHierarchyExecution
open ChiHierarchyIndex EuclideanGaussian ProjectionGeometry

theorem sharedKnown_column_mem (counts : ℕ → ℕ) (J D q : ℕ) (U : FiniteColumns counts J (Space D))
    (V : Submodule ℝ (Space D)) (i : FrameIndex counts J) (k : Fin (chainSize i+1))
    (hk : k.val<retained counts J q i) : U i k∈sharedKnown counts J D q U V :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨i,k,hk,rfl⟩)

theorem sharedKnown_mono (counts : ℕ → ℕ) (J D q q' : ℕ) (U : FiniteColumns counts J (Space D))
    (V : Submodule ℝ (Space D)) (hq : ∀ i, retained counts J q i≤retained counts J q' i) :
    sharedKnown counts J D q U V≤sharedKnown counts J D q' U V := by
  apply sup_le le_sup_left
  apply Submodule.span_le.mpr
  rintro _ ⟨i,k,hk,rfl⟩
  exact sharedKnown_column_mem counts J D q' U V i k (hk.trans_le (hq i))

theorem sharedKnown_success_mono (counts : ℕ → ℕ) (J D q : ℕ) (U : FiniteColumns counts J (Space D))
    (V : Submodule ℝ (Space D)) : sharedKnown counts J D q U V≤sharedKnown counts J D (q+1) U V :=
  sharedKnown_mono counts J D q (q+1) U V (fun i => (retained_success_bounds counts J q i).1)

theorem frame_projection_norm_bound {D T : ℕ} (W : Submodule ℝ (Space D)) (r : ℕ)
    (U : Fin T → Space D) (cap : ℝ) (hcap : 0≤cap)
    (hE : GenieProtocol.BoundedEnergy W (prefixSet r) U cap) (k : Fin T) (hk : r≤k.val) :
    ‖W.orthogonalProjection (U k)‖≤Real.sqrt cap := by
  have he := hE k (by change ¬k.val<r;omega)
  change ‖W.orthogonalProjection (U k)‖^2≤cap at he
  nlinarith [Real.sq_sqrt hcap,Real.sqrt_nonneg cap,norm_nonneg (W.orthogonalProjection (U k))]

end Bilevel.ChiHierarchyExecution

namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution EuclideanGaussian ChiBoundedChain

theorem canonical_shared_column_mem {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j,counts (j+1)+1≤D) (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (a : Orientations counts J D) (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space D))
    (j : ℕ) (hj : j≤J) (I : List ℕ) (k : Fin (counts (j+1)+1))
    (hk : k.val<canonicalCounter counts J q j I) :
    canonicalFamily hD a j I (basis k)∈sharedKnown counts J D q (columns hAll a) V := by
  let i : ChiHierarchyIndex.Node counts J := canonicalNode counts J ⟨j,by omega⟩ I
  have hr : canonicalCounter counts J q j I=retained counts J q (Sum.inr i) := dif_pos hj
  rw [hr] at hk
  rw [canonicalFamily_covered hD hAll a j hj I]
  change frame hAll a (Sum.inr i) (basis k)∈_
  rw [frame_basis]
  exact sharedKnown_column_mem counts J D q (columns hAll a) V (Sum.inr i) k hk

theorem canonical_projection_norm {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ j,counts (j+1)+1≤D) (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤D)
    (a : Orientations counts J D) (q : ℕ) (W : Submodule ℝ (EuclideanGaussian.Space D))
    (cap : ℝ) (hcap : 0≤cap)
    (hE : ∀ i : FrameIndex counts J,
      GenieProtocol.BoundedEnergy W (prefixSet (retained counts J q i)) (columns hAll a i) cap)
    (j : ℕ) (hj : j≤J) (I : List ℕ) (k : Fin (counts (j+1)+1))
    (hk : canonicalCounter counts J q j I≤k.val) :
    ‖W.orthogonalProjection (canonicalFamily hD a j I (basis k))‖≤Real.sqrt cap := by
  exact finite_column_property_all_lists hD hAll a q
    (fun _ _ v => ‖W.orthogonalProjection v‖≤Real.sqrt cap)
    (fun i k hi => frame_projection_norm_bound W _ _ cap hcap (hE (Sum.inr i)) k hi) j hj I k hk

end Bilevel.ChiHierarchyHaar
