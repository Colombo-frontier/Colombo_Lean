import GradientHessian.CensoredHierarchy
import GradientHessian.HierarchyJointCalculus

/-! The sole undisclosed matrix contribution to the entire censored scalar
is one numerical leaf base, multiplied by an explicit known selector weight. -/

noncomputable section
namespace GradientHessian.CensoredOracle
universe u
open HigherHierarchy CensoredHierarchy InnerCoordinates

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def numericalMap : (t : ℕ) → Space Y E H m t →L[ℝ] Y
  | 0 => (numerical Y E (m+1) (Inner.absoluteDepth+2)).comp CensoredFirstHeight.lower
  | t+1 => (numericalMap t).comp (lower (Space Y E H m t) (H t))

theorem frontier_add {F : Type*} (k : Fin b) (Q : F → ℝ) (S : ℝ)
    (child port self incoming parent : Fin b → F → ℝ) (active extra : F → ℝ) (Z : F) :
    FrontierOracleScalar.scalar k Q S child port self incoming parent (fun x => active x+extra x) Z=
      FrontierOracleScalar.scalar k Q S child port self incoming parent active Z+
        CensoredLeaf.prefixWeight (fun i => parent i Z) k*extra Z := by
  unfold FrontierOracleScalar.scalar
  ring

def known (K : ℝ) : (t : ℕ) → Plan m t → Data Y E H m t → Space Y E H m t → ℝ
  | 0,p,d => FrontierOracleScalar.scalar p.1
      (Leaf.publicQuadratic (m+1) ∘ CensoredFirstHeight.lower) (FirstHeight.spacing m)
      (fun i => FirstHeight.children d i ∘ CensoredFirstHeight.lower)
      (fun i => FirstHeight.childPorts d i ∘ CensoredFirstHeight.lower) (CensoredFirstHeight.maskedSelf d p.2.1)
      (fun i Z => Inner.input (d.outerDirections i) (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) i Z))
      (fun i Z => Inner.ports d.outerDirections Z i)
      (CensoredLeaf.knownTerm p.2.2 (d.b p.1,d.a p.1,d.innerDirections p.1) ∘ CensoredFirstHeight.lower)
  | t+1,p,d => FrontierOracleScalar.scalar p.1
      (baseline K t ∘ lower (Space Y E H m t) (H t)) (spacing m K t)
      (fun i => HigherHierarchy.scalar K t (d.children i) ∘ lower (Space Y E H m t) (H t))
      (fun i => outgoing K t (d.children i) ∘ lower (Space Y E H m t) (H t)) (CensoredHierarchy.maskedSelf K t d p.2.1)
      (fun i Z => nodeIncoming (radius m K t) (width m t) (centers K d) Z i)
      (fun i Z => nodePorts (width m t) (centers K d) Z i)
      (known K t p.2.2 (d.children p.1) ∘ lower (Space Y E H m t) (H t))

def weight (K : ℝ) : (t : ℕ) → Plan m t → Data Y E H m t → Space Y E H m t → ℝ
  | 0,p,d,Z => CensoredLeaf.prefixWeight (Inner.ports d.outerDirections Z) p.1
  | t+1,p,d,Z => CensoredLeaf.prefixWeight (nodePorts (width m t) (centers K d) Z) p.1 *
      weight K t p.2.2 (d.children p.1) (lower (Space Y E H m t) (H t) Z)

def selectedMatrix (t : ℕ) (p : Plan m t) (d : Data Y E H m t) : Y →L[ℝ] Y :=
  (leafData t d (selectedLeaf m t p)).A

theorem scalar_decomposition (K : ℝ) : ∀ t (p : Plan m t) (d : Data Y E H m t) (Z : Space Y E H m t),
    CensoredHierarchy.scalar K t p d Z = known K t p d Z+weight K t p d Z*
      LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1)) (selectedMatrix t p d)
        (numericalMap t Z)
  | 0,p,d,Z => by
      have he : CensoredFirstHeight.active d p.1 p.2.2 = fun x =>
          CensoredLeaf.knownTerm p.2.2 (d.b p.1,d.a p.1,d.innerDirections p.1) (CensoredFirstHeight.lower x)+
          LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1)) (d.A p.1)
            (numerical Y E (m+1) (Inner.absoluteDepth+2) (CensoredFirstHeight.lower x)) := by
        funext x
        simp only [CensoredFirstHeight.active,Function.comp_apply,CensoredLeaf.objective]
        ring
      simp only [CensoredHierarchy.scalar,CensoredFirstHeight.scalar,he]
      rw [frontier_add]
      rfl
  | t+1,p,d,Z => by
      have he : CensoredHierarchy.scalar K t p.2.2 (d.children p.1) ∘ lower (Space Y E H m t) (H t)=
          fun x => known K t p.2.2 (d.children p.1) (lower (Space Y E H m t) (H t) x)+
            weight K t p.2.2 (d.children p.1) (lower (Space Y E H m t) (H t) x)*
              LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1)) (selectedMatrix t p.2.2 (d.children p.1))
                (numericalMap t (lower (Space Y E H m t) (H t) x)) :=
        funext (fun x => scalar_decomposition K t p.2.2 (d.children p.1) _)
      rw [CensoredHierarchy.scalar,he]
      simp only [known,weight,FrontierOracleScalar.scalar,Function.comp_apply]
      change _ = _ + (_ * _) * LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1))
        (selectedMatrix t p.2.2 (d.children p.1))
          (numericalMap t (lower (Space Y E H m t) (H t) Z))
      ring

end GradientHessian.CensoredOracle
