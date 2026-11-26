import Bilevel.ChiCanonicalSourceData

/-! Explicit numeric and frame projections of the canonical source records.
These identities avoid unfolding entire dependent Haar frame records when
transporting the local analytic inequalities between list indices. -/
noncomputable section
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

theorem sourceCanonicalMacro_width :
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km).width=initial.width := rfl

theorem sourceCanonicalMacro_radius :
    (sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km).radius=
      Km*initial.width*Real.sqrt ((macroN:ℝ)+1) := rfl

theorem sourceCanonicalGeometry_width (j : ℕ) (I : List ℕ) :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).width=
      resolutions j*(parentScale initial ratios resolutions j).width/ratios j := rfl

theorem sourceCanonicalGeometry_radius (j : ℕ) (I : List ℕ) :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).radius=
      sourceLocalRadius CR (parentScale initial ratios resolutions j).curvature
        (parentScale initial ratios resolutions j).width (ratios j) (weight j) ζ := rfl

theorem sourceCanonicalGeometry_frame (j : ℕ) (I : List ℕ) :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).frame=
      canonicalFamily hdim a j I := rfl

end Bilevel.ChiHierarchyHaar
