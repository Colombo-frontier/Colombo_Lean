import Bilevel.ChiOriginalSourceDefinitions

/-! The public source scales do not depend on a Haar orientation. Named
identities keep dependent certificates from repeatedly unfolding records. -/
noncomputable section
set_option autoImplicit false
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR : ℝ)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim) (j : ℕ) (I : List ℕ)

theorem sourceCanonical_ell_eq_template :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).ell=
      (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR j I).ell := rfl

theorem sourceCanonical_width_eq_template :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).width=
      (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR j I).width := rfl

theorem sourceCanonical_radius_eq_template :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).radius=
      (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR j I).radius := rfl

theorem sourceCanonical_nu_eq_template :
    (sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).nu=
      (sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR j I).nu := rfl

theorem sourceCanonical_width_positive
    (h : 0<(sourceTemplateGeometry macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR j I).width) :
    0<(sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR j I).width :=
  (sourceCanonical_width_eq_template macroN J dim cn ratios resolutions hdim initial weight A Kminus ζ CR a j I).symm ▸ h

end Bilevel.ChiHierarchyHaar
