import Bilevel.ChiVirtualQueryInverse

/-! The disclosed-column evaluator is unchanged when the unused source
frames are replaced. This holds on all arrays, including invalid states. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension
set_option maxHeartbeats 1200000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def reframeNode (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E) : Node E := {D with frame := U}
def reframeGeometry (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F) : Geometry F :=
  fun j I => reframeNode (D j I) (U j I)

@[simp] theorem virtualH_reframe (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E)
    (r : ℕ) (columns : Fin (D.n+1) → E) (u : E) :
    virtualH (reframeNode D U) r columns u=virtualH D r columns u := rfl
@[simp] theorem virtualSelector_reframe (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E)
    (r : ℕ) (columns : Fin (D.n+1) → E) (i : Fin (D.n+1)) (u : E) :
    virtualSelector (reframeNode D U) r columns i u=virtualSelector D r columns i u := rfl
@[simp] theorem virtualResidual_reframe (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E)
    (r : ℕ) (columns : Fin (D.n+1) → E) (i : Fin (D.n+1)) (u : E) :
    virtualResidual (reframeNode D U) r columns i u=virtualResidual D r columns i u := rfl
@[simp] theorem virtualRelease_reframe (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E)
    (r : ℕ) (columns : Fin (D.n+1) → E) (u : E) :
    virtualRelease (reframeNode D U) r columns u=virtualRelease D r columns u := rfl
@[simp] theorem virtualOuterSelector_reframe (D : Node E) (U : Space D.n →ₗᵢ[ℝ] E)
    (r : ℕ) (columns : Fin (D.n+1) → E) (i : Fin (D.n+1)) (u : E) :
    virtualOuterSelector (reframeNode D U) r columns i u=virtualOuterSelector D r columns i u := rfl

variable (D : Geometry F) (U : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] F)
  (r : ℕ → List ℕ → ℕ) (columns : ∀ j I,Fin ((D j I).n+1) → F)

@[simp] theorem virtualPayload_reframe (d j : ℕ) (I : List ℕ) (u : ℕ → F) :
    virtualPayload (reframeGeometry D U) r columns d j I u=virtualPayload D r columns d j I u := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [virtualPayload,reframeGeometry,virtualH_reframe,virtualResidual_reframe,
      virtualRelease_reframe,virtualSelector_reframe,ih]; rfl

@[simp] theorem virtualCarrier_reframe (d j : ℕ) (I : List ℕ) (k : ℕ) (u : ℕ → F) :
    virtualCarrier (reframeGeometry D U) r columns d j I k u=virtualCarrier D r columns d j I k u := by
  induction d generalizing j I k with
  | zero => cases k <;> rfl
  | succ d ih => cases k <;> simp only [virtualCarrier,reframeGeometry,virtualH_reframe,
      virtualResidual_reframe,virtualRelease_reframe,virtualSelector_reframe,ih] <;> rfl

@[simp] theorem virtualSelect_reframe (leaf : ∀ j I,Space (D j I).n → ℝ)
    (d j : ℕ) (I : List ℕ) (u : ℕ → F) :
    virtualSelect (reframeGeometry D U) r columns leaf d j I u=virtualSelect D r columns leaf d j I u := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [virtualSelect,reframeGeometry,virtualSelector_reframe,ih]; rfl

variable (m : ℕ) (M : Node E) (UM : Space M.n →ₗᵢ[ℝ] E) (rM : ℕ)
  (macroColumns : Fin (M.n+1) → E)

@[simp] theorem virtualOuterCarrier_reframe (d t : ℕ) (z : Joint E (Blocks m F)) :
    virtualOuterCarrier m (reframeNode M UM) (reframeGeometry D U) rM r macroColumns columns d t z=
      virtualOuterCarrier m M D rM r macroColumns columns d t z := by
  simp only [virtualOuterCarrier,virtualOuterSelector_reframe,virtualCarrier_reframe]
  rfl

@[simp] theorem virtualOuterLeaf_reframe (leaf : ∀ j I,Space (D j I).n → ℝ)
    (d : ℕ) (z : Joint E (Blocks m F)) :
    virtualOuterLeaf m (reframeNode M UM) (reframeGeometry D U) rM r macroColumns columns leaf d z=
      virtualOuterLeaf m M D rM r macroColumns columns leaf d z := by
  simp only [virtualOuterLeaf,virtualOuterSelector_reframe,virtualSelect_reframe]
  rfl

@[simp] theorem virtualCoarse_reframe (J : ℕ) (i : Fin J) (z : Joint E (Blocks m F)) :
    virtualCoarse m (reframeNode M UM) (reframeGeometry D U) rM r macroColumns columns J i z=
      virtualCoarse m M D rM r macroColumns columns J i z := by
  have hf : frontierLeaf (reframeGeometry D U)=frontierLeaf D := rfl
  simp only [virtualCoarse,hf,virtualOuterCarrier_reframe,virtualOuterLeaf_reframe]

@[simp] theorem virtualActive_reframe (J : ℕ) (c θ : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (z : Full (Joint E (Blocks m F)) s) :
    virtualActive m (reframeNode M UM) (reframeGeometry D U) J rM r macroColumns columns
      c θ s index radialIndex fineIndex rad R dn z=
    virtualActive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  have hf : pieceLeaf (reframeGeometry D U)=pieceLeaf D := rfl
  have hw : ChiOuter.coarseWidth (reframeGeometry D U)=ChiOuter.coarseWidth D := rfl
  unfold virtualActive
  simp only [virtualCoarse_reframe,hf,hw,virtualOuterLeaf_reframe]
  rfl

@[simp] theorem virtualSignal_reframe (J : ℕ) (c θ : ℝ) (s : ℕ) (fineIndex : Fin s)
    (z : Full (Joint E (Blocks m F)) s) :
    virtualSignal m (reframeNode M UM) (reframeGeometry D U) J rM r macroColumns columns c θ s fineIndex z=
      virtualSignal m M D J rM r macroColumns columns c θ s fineIndex z := by
  have hf : signalLeaf (reframeGeometry D U)=signalLeaf D := rfl
  have hw : (reframeGeometry D U J []).width=(D J []).width := rfl
  simp only [virtualSignal,hw,hf,virtualOuterLeaf_reframe]

@[simp] theorem virtualInactive_reframe (J : ℕ) (c θ : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (z : Full (Joint E (Blocks m F)) s) :
    virtualInactive m (reframeNode M UM) (reframeGeometry D U) J rM r macroColumns columns
      c θ s index radialIndex fineIndex rad R dn z=
    virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  simp only [virtualInactive,virtualActive_reframe,virtualSignal_reframe]

@[simp] theorem statePotential_reframe (active : Bool) (J : ℕ) (rM : ℕ → ℕ)
    (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (s : ℕ)
    (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (p : VirtualState M D) :
    statePotential active m (reframeNode M UM) (reframeGeometry D U) J rM r c v s
      index radialIndex fineIndex rad R dn p=
    statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p := by
  funext z
  cases active <;> simp only [statePotential,Bool.false_eq_true,if_false,if_true,
    virtualActive_reframe,virtualInactive_reframe]

variable [CompleteSpace E] [CompleteSpace F]

theorem queryInverse_reframe (active : Bool) (J : ℕ) (rM : ℕ → ℕ)
    (r : ℕ → ℕ → List ℕ → ℕ) (c v : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hv : 1≤v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (hw : ∀ i : Fin J,0<(D (i.val+1) []).width)
    (h2 : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m M D J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12)
    (h2U : ∀ p : {p : VirtualState M D | ValidState M D rM r p},∀ z,
      ‖iteratedFDeriv ℝ 2 (statePotential active m (reframeNode M UM) (reframeGeometry D U)
        J rM r c v s index radialIndex fineIndex rad R dn p.1) z‖≤1/12) :
    queryInverse active m (reframeNode M UM) (reframeGeometry D U) J rM r c v hc hβ hv s
      index radialIndex fineIndex rad R dn hR hw h2U=
    queryInverse active m M D J rM r c v hc hβ hv s index radialIndex fineIndex rad R dn hR hw h2 := by
  unfold queryInverse
  have he : (fun p : VirtualQuery M D m s =>
      statePotential active m (reframeNode M UM) (reframeGeometry D U) J rM r c v s
        index radialIndex fineIndex rad R dn p.1)=
      (fun p : VirtualQuery M D m s => statePotential active m M D J rM r c v s
        index radialIndex fineIndex rad R dn p.1) := by
    funext p
    exact statePotential_reframe D U m M UM active J rM r c v s index radialIndex fineIndex rad R dn p.1
  let S : Set (VirtualQuery M D m s) := {p | ValidState M D rM r p.1}
  have hcongr (f g : VirtualQuery M D m s → Full (Joint E (Blocks m F)) s → ℝ) (he : f=g)
      (hf : ∀ p : S,ContDiff ℝ 3 (f p.1)) (hg : ∀ p : S,ContDiff ℝ 3 (g p.1))
      (hHf : ∀ p : S,∀ z,‖iteratedFDeriv ℝ 2 (f p.1) z‖≤(1/12:ℝ))
      (hHg : ∀ p : S,∀ z,‖iteratedFDeriv ℝ 2 (g p.1) z‖≤(1/12:ℝ)) :
      ParametricScalarInverse.inverseSlice S f (fun p => p.2.1) (fun p => p.2.2) (fun _ => 0)
        ⟨1/12,by norm_num⟩ (by change (1/12:ℝ)<1; norm_num) hf hHf=
      ParametricScalarInverse.inverseSlice S g (fun p => p.2.1) (fun p => p.2.2) (fun _ => 0)
        ⟨1/12,by norm_num⟩ (by change (1/12:ℝ)<1; norm_num) hg hHg := by
    cases he
    rfl
  exact hcongr _ _ he _ _ _ _

end Bilevel.ChiPrefixEvaluation

