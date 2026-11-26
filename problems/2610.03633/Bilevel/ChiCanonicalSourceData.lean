import Bilevel.ChiFiniteVirtualPrefix
import Bilevel.ChiCanonicalProjection
import Bilevel.ChiCanonicalMacroFuture
import Bilevel.ChiSourceInverseGeometry

/-! The actual source geometry sampled from the finite Haar hierarchy,
and its exact finite disclosed store. Numeric parameters are unchanged;
frames and retained counts use the same canonical legal path. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)

def sourceCanonicalMacro (initial : Scale) (Km : ℝ) : ChiRecursive.Node (EuclideanGaussian.Space dim) :=
  sourceMacroNode macroN initial Km (frame hAll a (Sum.inl ()))

def sourceCanonicalGeometry (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ) :
    Geometry (EuclideanGaussian.Space dim) :=
  sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR (canonicalFamily hdim a)

def sourceCanonicalState (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ) (q : ℕ) :
    VirtualState (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR) :=
  finiteVirtualState (sourceCounts macroN cn ratios resolutions) J _ _ rfl (fun _ _ => rfl)
    (actual (sourceCounts macroN cn ratios resolutions) J q (columns hAll a))

theorem sourceCanonicalState_macro_prefix (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR Km : ℝ) (q : ℕ) (k : Fin (macroN+1))
    (hk : k.val<counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []) :
    (sourceCanonicalState macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km q).2.1 k=
      (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km).frame (basis k) := by
  have h := finiteVirtualState_macro_prefix
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km)
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR)
    rfl (fun _ _ => rfl) hAll a q k
  simpa only [sourceCanonicalState,paddedPrefix,Fin.cast_refl,id_eq,if_pos hk,sourceCanonicalMacro,
    sourceMacroNode] using h

theorem sourceCanonicalState_inner_prefix (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR Km : ℝ) (q j : ℕ) (I : List ℕ)
    (k : Fin (sourceChainIndex cn (ratios j) (resolutions j)+1))
    (hk : k.val<canonicalCounter (sourceCounts macroN cn ratios resolutions) J q j I) :
    (sourceCanonicalState macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km q).2.2 j I k=
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).frame
        (basis k) := by
  have h := finiteVirtualState_inner_prefix
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km)
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR)
    rfl (fun _ _ => rfl) hdim hAll a q j I k
  simpa only [sourceCanonicalState,paddedPrefix,Fin.cast_refl,id_eq,if_pos hk,sourceCanonicalGeometry,
    sourceGeometry,ChiRecursive.sourceNode] using h

theorem sourceCanonicalState_valid (initial : Scale) (weight : ℕ → ℝ)
    (A Kminus ζ CR Km : ℝ) (q : ℕ) :
    ValidState (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km)
      (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR)
      (fun t => counter (sourceCounts macroN cn ratios resolutions) (J+1) t 0 [])
      (canonicalCounter (sourceCounts macroN cn ratios resolutions) J)
      (sourceCanonicalState macroN J dim cn ratios resolutions hdim hAll a initial weight A Kminus ζ CR Km q) :=
  finiteVirtualState_haar_valid _ _ rfl (fun _ _ => rfl) hAll a q

end Bilevel.ChiHierarchyHaar
