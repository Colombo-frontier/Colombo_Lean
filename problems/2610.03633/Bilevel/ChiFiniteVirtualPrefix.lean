import Bilevel.ChiFiniteVirtualState
import Bilevel.ChiCanonicalStore

/-! Exact finite-store data of the same sampled Haar hierarchy. Size casts
are explicit and disappear in the source specialization with definitional
branching counts. No auxiliary or undisclosed column enters the store. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiPrefixEvaluation ChiRecursive ChiBoundedChain

theorem finiteVirtualState_macro_prefix {counts : ℕ → ℕ} {J dim : ℕ}
    (M : ChiRecursive.Node (EuclideanGaussian.Space dim)) (D : Geometry (EuclideanGaussian.Space dim))
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤dim)
    (a : Orientations counts J dim) (q : ℕ) (i : Fin (M.n+1)) :
    (finiteVirtualState counts J M D hM hD (actual counts J q (columns hAll a))).2.1 i=
      paddedPrefix (counts 0) (ChiTreeProgress.counter counts (J+1) q 0 [])
        (fun k => frame hAll a (Sum.inl ()) (basis k)) (Fin.cast (congrArg (fun k => k+1) hM) i) :=
  congrFun (actual_macro_prefix hAll a q) (Fin.cast (congrArg (fun k => k+1) hM) i)

theorem finiteVirtualState_inner_prefix {counts : ℕ → ℕ} {J dim : ℕ}
    (M : ChiRecursive.Node (EuclideanGaussian.Space dim)) (D : Geometry (EuclideanGaussian.Space dim))
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (hdim : ∀ j,counts (j+1)+1≤dim)
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤dim)
    (a : Orientations counts J dim) (q j : ℕ) (I : List ℕ) (i : Fin ((D j I).n+1)) :
    (finiteVirtualState counts J M D hM hD (actual counts J q (columns hAll a))).2.2 j I i=
      paddedPrefix (counts (j+1)) (canonicalCounter counts J q j I)
        (fun k => canonicalFamily hdim a j I (basis k)) (Fin.cast (congrArg (fun k => k+1) (hD j I)) i) :=
  congrFun (actual_extended_prefix hdim hAll a q j I) (Fin.cast (congrArg (fun k => k+1) (hD j I)) i)

theorem finiteVirtualState_haar_valid {counts : ℕ → ℕ} {J dim : ℕ}
    (M : ChiRecursive.Node (EuclideanGaussian.Space dim)) (D : Geometry (EuclideanGaussian.Space dim))
    (hM : M.n=counts 0) (hD : ∀ j I,(D j I).n=counts (j+1))
    (hAll : ∀ i : FrameIndex counts J,chainSize i+1≤dim)
    (a : Orientations counts J dim) (q : ℕ) :
    ValidState M D (fun q => ChiTreeProgress.counter counts (J+1) q 0 []) (canonicalCounter counts J)
      (finiteVirtualState counts J M D hM hD (actual counts J q (columns hAll a))) :=
  finiteVirtualState_actual_valid counts J M D hM hD (columns hAll a) (columns_orthonormal hAll a) q

end Bilevel.ChiHierarchyHaar
