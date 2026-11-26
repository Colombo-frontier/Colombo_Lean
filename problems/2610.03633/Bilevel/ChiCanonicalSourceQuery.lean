import Bilevel.ChiCanonicalSourceProjection
import Bilevel.ChiSourceQueryVectors

/-! Concrete same-query locality inputs: actual canonical source counters,
finite Haar energy, fresh query inclusion and old/new disclosed spaces.
The only projection premise is the finite observer energy event. -/
noncomputable section
set_option maxHeartbeats 1200000
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex ChiHierarchyExecution ChiTreeProgress ChiBoundedChain ChiRecursive
  ChiOuter ChiCarrier ChiPrefixEvaluation ChiExtensionCalibration PrimitiveGeometry

variable (macroN J dim : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ)
  (hdim : ∀ j,sourceChainIndex cn (ratios j) (resolutions j)+1≤dim)
  (hAll : ∀ i : FrameIndex (sourceCounts macroN cn ratios resolutions) J,chainSize i+1≤dim)
  (a : Orientations (sourceCounts macroN cn ratios resolutions) J dim)
  (initial : Scale) (weight : ℕ → ℝ) (A Kminus ζ CR Km : ℝ)

local notation "Cts" => sourceCounts macroN cn ratios resolutions
local notation "M" => sourceCanonicalMacro macroN J dim cn ratios resolutions hAll a initial Km
local notation "G" => sourceCanonicalGeometry macroN J dim cn ratios resolutions hdim a initial weight A Kminus ζ CR

theorem sourceCanonical_bookkeeping (q : ℕ) :
    counter Cts (J+1) q 0 []≤counter Cts (J+1) (q+1) 0 [] ∧
    (∀ j I,canonicalCounter Cts J q j I≤canonicalCounter Cts J (q+1) j I) ∧
    (∀ i : Fin ((M).n+1),counter Cts (J+1) q 0 []≤ i.val →
      canonicalCounter Cts J q 0 [i.val]≤(G 0 [i.val]).n) ∧
    (∀ t,t<J → ∀ I,∀ i : Fin ((G t I).n+1),canonicalCounter Cts J q t I≤ i.val →
      canonicalCounter Cts J q (t+1) (child I i.val)≤(G (t+1) (child I i.val)).n) ∧
    (∀ i : Fin ((M).n+1),i.val≤counter Cts (J+1) q 0 [] →
      FrontierAdvance G (canonicalCounter Cts J q) (canonicalCounter Cts J (q+1)) J 0 [i.val]) := by
  refine ⟨(counter_success_bounds Cts (J+1) q 0 []).1,?_,?_,?_,?_⟩
  · exact fun j I => (canonicalCounter_success_bounds Cts J q j I).1
  · exact fun i hi => canonicalCounter_macro_future Cts J q i hi
  · exact fun t ht I i hi => canonicalCounter_future Cts J q t ht I i hi
  · exact fun i hi => canonical_frontierAdvance G Cts (fun _ _ => rfl) J q i hi

theorem sourceCanonical_tree_from_energy
    (hl : 0< initial.curvature) (hw : 0< initial.width)
    (hr : ∀ j,1≤ratios j) (hη : ∀ j,0<resolutions j) (hη1 : ∀ j,resolutions j≤1)
    (hweight : ∀ j,0<weight j) (hζ : 0<ζ) (hCR : 0<CR) (hKm : 0<Km)
    (q : ℕ) (V : Submodule ℝ (EuclideanGaussian.Space dim)) (cap τ : ℝ) (hcap : 0≤cap)
    (hE : ∀ i : FrameIndex Cts J,GenieProtocol.BoundedEnergy
      (sharedKnown Cts J dim q (columns hAll a) V)
      (prefixSet (retained Cts J q i)) (columns hAll a i) cap)
    (hmBudget : (M).radius*Real.sqrt cap≤(M).width/8)
    (hBudget : ∀ j,j≤J → (G j []).radius*Real.sqrt cap≤(G j []).width/8)
    (hfBudget : (G J []).radius*Real.sqrt cap≤τ/16) :
    let W := sharedKnown Cts J dim q (columns hAll a) V
    let Wnew := sharedKnown Cts J dim (q+1) (columns hAll a) V
    TreeProjection G 0 J (by omega) (fun _ : Fin (J+1) => W) (canonicalCounter Cts J q) ∧
    (∀ k : Fin ((M).n+1),counter Cts (J+1) q 0 []≤k.val →
      (M).radius*‖W.orthogonalProjection ((M).frame (basis k))‖≤(M).width/8) ∧
    (∀ j I,j≤J → ∀ k : Fin ((G j I).n+1),canonicalCounter Cts J q j I≤k.val →
      (G j I).radius*‖W.orthogonalProjection ((G j I).frame (basis k))‖≤(G j I).width/8) ∧
    (∀ I,∀ k : Fin ((G J I).n+1),canonicalCounter Cts J q J I≤k.val →
      (G J I).radius*‖W.orthogonalProjection ((G J I).frame (basis k))‖≤τ/16) ∧
    W≤Wnew ∧
    (∀ I,∀ k : Fin ((G J I).n+1),k.val<canonicalCounter Cts J (q+1) J I →
      (G J I).frame (basis k)∈Wnew) := by
  dsimp only
  have hg := sourceCanonical_geometry macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km hl hw hr hη hη1 hweight hζ hCR hKm
  have hp := sourceCanonical_projection_margins macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km q (sharedKnown Cts J dim q (columns hAll a) V) cap τ hcap hE
    hg.2.1.le (fun j _ => (hg.2.2.1 j []).2.1.le) hmBudget hBudget hfBudget
  have hk := sourceCanonical_known_columns macroN J dim cn ratios resolutions hdim hAll a initial weight
    A Kminus ζ CR Km q V
  refine ⟨?_,hp.1,hp.2.1,hp.2.2,sharedKnown_success_mono Cts J dim q (columns hAll a) V,?_⟩
  · apply treeProjection_of_half_margin G J (by omega)
      (fun _ : Fin (J+1) => sharedKnown Cts J dim q (columns hAll a) V) (canonicalCounter Cts J q)
    · exact fun j I _ => (hg.2.2.1 j I).1
    · exact fun j I _ => (hg.2.2.1 j I).2.1
    · exact fun j I hj k hkr => hk.2 j I hj k hkr
    · exact fun j I hj k hkr => hp.2.1 j I hj k hkr
  · exact fun I k hkr => (sourceCanonical_known_columns macroN J dim cn ratios resolutions hdim hAll a initial
      weight A Kminus ζ CR Km (q+1) V).2 J I le_rfl k hkr

theorem sourceCanonical_query_inclusion (q s : ℕ)
    (V : Submodule ℝ (EuclideanGaussian.Space dim))
    (p : PartialLegendre.FullNormalVariables (EuclideanGaussian.Space dim)
      (Blocks (J+1) (EuclideanGaussian.Space dim)) (ChiExtension.Normals s))
    (hp : ∀ k,originalVectors p k∈V) :
    let W := sharedKnown Cts J dim q (columns hAll a) V
    p.fst.fst∈W ∧ p.snd∈normalKnown (fun _ : Fin (J+1) => W) s := by
  dsimp only
  have hb : ∀ k,originalVectors p k∈sharedKnown Cts J dim q (columns hAll a) V :=
    fun k => Submodule.mem_sup_left (hp k)
  exact ⟨originalVectors_macro_mem p _ hb,originalVectors_lower_mem p _ hb⟩

end Bilevel.ChiHierarchyHaar
