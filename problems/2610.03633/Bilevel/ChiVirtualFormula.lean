import Bilevel.ChiVirtualFine

/-! Full virtual scalar formulas on arbitrary disclosed arrays. Auxiliary
coordinates and Gram witnesses do not occur in these evaluators. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension ChiExtensionCalibration ZeroChainSchedule
variable {E F A B : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]

def virtualActive (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (c θ : ℝ) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (z : Full (Joint E (Blocks m F)) s) : ℝ :=
  (1/dn)*((∑ i : Fin J,virtualCoarse m M D rM r macroColumns columns J i z.fst *
      SmallGapProfiles.normal (coarseWidth D (i.val+1)) (z.snd (index i)))+
    ∑ p ∈ Finset.range (levels θ+1),virtualOuterLeaf m M D rM r macroColumns columns
      (pieceLeaf D c θ p) J z.fst * SmallGapProfiles.normal (width c (D J []).width θ p) (z.snd fineIndex))+
    radialSum radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le m (i.val+1)) (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn z

def virtualSignal (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (c θ : ℝ) (s : ℕ) (fineIndex : Fin s) (z : Full (Joint E (Blocks m F)) s) : ℝ :=
  let W := width c (D J []).width θ (levels θ)
  virtualOuterLeaf m M D rM r macroColumns columns (signalLeaf D (W/8)) J z.fst *
    SmallGapProfiles.normal W (z.snd fineIndex)

def virtualInactive (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (c θ : ℝ) (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (z : Full (Joint E (Blocks m F)) s) : ℝ :=
  virtualActive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z-
    virtualSignal m M D J rM r macroColumns columns c θ s fineIndex z/dn

omit [CompleteSpace F] [CompleteSpace B] in
theorem radial_zero_auxiliary (ν R dn : ℝ) (hR : 0<R) (x : F) (t : ℝ) :
    PublicRadialExtension.radial ν R dn (pack (pack x (0:B)) t)=
      PublicRadialExtension.radial ν R dn (pack x t) := by
  rw [PublicRadialExtension.radial_formula ν R dn hR,
    PublicRadialExtension.radial_formula ν R dn hR,norm_pack_zero]

omit [CompleteSpace E] [CompleteSpace A] [CompleteSpace F] [CompleteSpace B] in
theorem completed_radialSum_restriction (m J s : ℕ) (index : Fin J → Fin s)
    (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
    (z : Full (Joint E (Blocks m F)) s) :
    radialSum index (fun i => hierarchyBlock (E:=Joint E A) (F:=Joint F B) m (i.val+1))
      (fun i => hierarchyBlock_norm_le m (i.val+1)) (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn
      (fullInclusion m s z)=
    radialSum index (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
      (fun i => hierarchyBlock_norm_le m (i.val+1)) (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn z := by
  unfold radialSum
  apply Finset.sum_congr rfl
  intro i _
  change PublicRadialExtension.radial (rad (i.val+1)) (R (i.val+1)) dn
    (pack (block m (i.val+1) (blockInclusion m z.fst.snd)) (z.snd (index i)))=
    PublicRadialExtension.radial (rad (i.val+1)) (R (i.val+1)) dn
      (pack (block m (i.val+1) z.fst.snd) (z.snd (index i)))
  rw [block_blockInclusion,radial_zero_auxiliary _ _ _ (hR i)]

variable (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ) (r : ℕ → List ℕ → ℕ)
  (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
  (VM : Space M.n →ₗᵢ[ℝ] A) (V : ∀ j I,Space (D j I).n →ₗᵢ[ℝ] B)
  (hmGram : ∀ a b : Fin (M.n+1),a.val<rM → b.val<rM →
    ⟪macroColumns a,macroColumns b⟫=if a=b then 1 else 0)
  (hGram : ∀ j I,∀ a b : Fin ((D j I).n+1),a.val<r j I → b.val<r j I →
    ⟪columns j I a,columns j I b⟫=if a=b then 1 else 0)
  (c θ : ℝ) (hc : 0<c) (hβ : 0<(D J []).width) (hθ : 1≤θ)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)

theorem activePotential_eq_virtualActive (hR : ∀ i : Fin J,0<R (i.val+1))
    (z : Full (Joint E (Blocks m F)) s) :
    activePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn z=
      virtualActive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  unfold activePotential hierarchyExtension total virtualActive
  dsimp only [Function.comp_apply]
  rw [completed_radialSum_restriction m J s radialIndex rad R dn hR]
  congr 1
  unfold ChiExtension.hidden coarseSum
  congr 1
  apply congrArg₂ (fun a b : ℝ => a+b)
  · apply Finset.sum_congr rfl
    intro i _
    change normalTerm s (index i) _ _ (pack (tangentialInclusion m z.fst) z.snd)=_
    rw [normalTerm_formula,completed_coarse_restriction]
    rfl
  · rw [fineTerm_sum]
    apply Finset.sum_congr rfl
    intro p _
    change normalTerm s fineIndex (outerFinePiece m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ p) (width c (D J []).width θ p)
      (pack (tangentialInclusion m z.fst) z.snd)=_
    rw [normalTerm_formula,completed_outerFinePiece_restriction]

theorem completed_outerSignalNormal_restriction (z : Full (Joint E (Blocks m F)) s) :
    outerSignalNormal m (completedNode M rM macroColumns VM hmGram)
      (completedGeometry D r columns V hGram) J c θ s fineIndex (fullInclusion m s z)=
      virtualSignal m M D J rM r macroColumns columns c θ s fineIndex z := by
  unfold outerSignalNormal virtualSignal
  change normalTerm s fineIndex _ _ (pack (tangentialInclusion m z.fst) z.snd)=_
  rw [normalTerm_formula,completed_outerSignal_restriction]
  rfl

theorem inactivePotential_eq_virtualInactive (hR : ∀ i : Fin J,0<R (i.val+1))
    (z : Full (Joint E (Blocks m F)) s) :
    inactivePotential m M D J rM r macroColumns columns VM V hmGram hGram
      c θ hc hβ hθ s index radialIndex fineIndex rad R dn z=
      virtualInactive m M D J rM r macroColumns columns c θ s index radialIndex fineIndex rad R dn z := by
  have hd := hierarchyInactiveExtension_difference m (completedNode M rM macroColumns VM hmGram)
    (completedGeometry D r columns V hGram) J c θ hc hβ hθ s index radialIndex fineIndex rad R dn
      (fullInclusion m s z)
  change activePotential m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn z-
    inactivePotential m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn z=_ at hd
  rw [activePotential_eq_virtualActive m M D J rM r macroColumns columns VM V hmGram hGram
    c θ hc hβ hθ s index radialIndex fineIndex rad R dn hR,
    completed_outerSignalNormal_restriction] at hd
  unfold virtualInactive
  linarith

end Bilevel.ChiPrefixEvaluation
