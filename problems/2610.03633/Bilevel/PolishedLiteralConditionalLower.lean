import Bilevel.PolishedLiteralObserverActivation
import Bilevel.PolishedLiteralObserverTerminal
import Bilevel.PolishedLiteralMicroMean

/-! The source hierarchical fixed-horizon lower bound for the actual
literal original-gradient experiment. The locality, projection failure,
actual--virtual coupling and activation bound are discharged by the
concrete implementation. The source's analytic prefix barrier remains
an explicit, algorithm-independent premise. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry SourceFrameActions PolishedProjectionDimension
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))

/-- Precisely the additional analytic prefix certificate of the source:
it holds for every outer point and every incomplete macro prefix. -/
def PrefixBarrier (κ τx τu ε : ℝ) : Prop :=
  ∀ a,(macroSchedule (P.macroNode.n+1) (P.n+1)).count a<P.macroNode.n+1 →
    ∀ y : Joint (Space dx) (Space du),PrefixSmall P κ a τx τu y →
      8*ε≤‖gradient (P.outerMean κ) y‖

variable [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St Private : Type} [MeasurableSpace St] [MeasurableSpace Private]
  (A : BorelAdaptive.Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))

/-- Source `hier:thm:conditional-lower`, fixed horizon: private randomness
and the fresh iid Bernoulli stream are independent of exactly two global
Haar frames. No assumed bad-event probability or local reply equality
remains. The complete actual original-gradient output has margin 8ε
with probability at least 13/16. -/
theorem conditional_fixed_horizon (initial : Private → St) (hi : Measurable initial)
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (κ τ p ε : ℝ) (hp : 0<p) (hp1 : p≤1) (N : ℕ)
    (hN : (N:ℝ)≤(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p))
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδsc : ∀ j,j<P.J → τ≤P.δ j)
    (hdx : sourceDimension (N+1) (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) (1/8)≤dx)
    (hdu : sourceDimension (2*N+1) ((P.macroNode.n+1)*(P.n+1)) P.radius τ (1/8)≤du)
    (hbarrier : ∀ (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
      (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V),
      PrefixBarrier (framedParameters P U hU V hV) κ (P.macroNode.width/4) τ ε) :
    ∃ hx : P.macroNode.n+1≤dx, ∃ hu : (P.macroNode.n+1)*(P.n+1)≤du,
      13/16≤(((ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))).prod
        ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)))).real
        {z | let U := HaarFrame.frame dx (P.macroNode.n+1) hx z.2.1
          let V := HaarFrame.frame du ((P.macroNode.n+1)*(P.n+1)) hu z.2.2
          let I := framedParameters P U (HaarFrame.frame_orthonormal _ _ hx _) V (HaarFrame.frame_orthonormal _ _ hu _)
          8*ε≤‖gradient (I.outerMean κ)
            (A.output (originalRun P A U (HaarFrame.frame_orthonormal _ _ hx _) V
              (HaarFrame.frame_orthonormal _ _ hu _) τ p z.1.2 N 0 (initial z.1.1,0)).1)‖} := by
  let stream := IndependentStream.law (BernoulliOracle.law p hp1)
  let privateLaw := ρ.prod stream
  let initialC : Private × (ℕ → Bool) → St := fun z => initial z.1
  let μ := privateLaw.prod ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du))
  obtain ⟨hx,hu,hprob⟩ := literal_source_coupling P A τ p initialC (hi.comp measurable_fst)
    Prod.snd measurable_snd privateLaw N (1/8) hRx hRu hb hβ hτ hτβ hτb hδsc (by norm_num) (by norm_num) hdx hdu
  let fx := fun z : OrthogonalHaar.Group dx × OrthogonalHaar.Group du => HaarFrame.frame dx (P.macroNode.n+1) hx z.1
  let fu := fun z : OrthogonalHaar.Group dx × OrthogonalHaar.Group du => HaarFrame.frame du ((P.macroNode.n+1)*(P.n+1)) hu z.2
  let B : Set ((Private × (ℕ → Bool)) × (OrthogonalHaar.Group dx × OrthogonalHaar.Group du)) :=
    {z | ¬SourceObserved (literalMacroRules P A τ p)
        ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
        (macroInitial initialC Prod.snd (z.1,fu z.2),(⊥,∅)) (fx z.2) ∨
      ¬SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
        (microInitial initialC Prod.snd (z.1,fx z.2),(⊥,∅)) (fu z.2) ∨
      ∃ n,n≤N ∧ originalRun P A (fx z.2) (HaarFrame.frame_orthonormal _ _ hx _) (fu z.2)
          (HaarFrame.frame_orthonormal _ _ hu _) τ p z.1.2 n 0 (initial z.1.1,0)≠
        literalRun P A τ p z.1.2 (fx z.2) (fu z.2) n 0 (initial z.1.1,0)}
  let act : Set ((Private × (ℕ → Bool)) × (OrthogonalHaar.Group dx × OrthogonalHaar.Group du)) :=
    {z | (P.macroNode.n+1)*(P.n+1)≤(literalRun P A τ p z.1.2 (fx z.2) (fu z.2) N 0 (initial z.1.1,0)).2}
  let G : Set ((Private × (ℕ → Bool)) × (OrthogonalHaar.Group dx × OrthogonalHaar.Group du)) :=
    {z | 8*ε≤‖gradient ((framedParameters P (fx z.2) (HaarFrame.frame_orthonormal _ _ hx _)
        (fu z.2) (HaarFrame.frame_orthonormal _ _ hu _)).outerMean κ)
      (A.output (originalRun P A (fx z.2) (HaarFrame.frame_orthonormal _ _ hx _) (fu z.2)
        (HaarFrame.frame_orthonormal _ _ hu _) τ p z.1.2 N 0 (initial z.1.1,0)).1)‖}
  have hbad : μ.real B≤1/8 := by
    have he : μ B≤ENNReal.ofReal (1/8) := hprob
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
    simpa only [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤1/8)] using ht
  have hact : μ.real act≤1/16 := master_activation_sixteenth
    (macroSchedule (P.macroNode.n+1) (P.n+1)) (microSchedule ((P.macroNode.n+1)*(P.n+1)))
    A (rawCounterReply P τ p) fx fu initial ((OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)) ρ
    p hp hp1 N ((P.macroNode.n+1)*(P.n+1)) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hN
  have hcover : Set.univ⊆(B∪act)∪G := by
    intro z _
    by_cases hbadz : z∈B
    · exact Or.inl (Or.inl hbadz)
    by_cases hactz : z∈act
    · exact Or.inl (Or.inr hactz)
    apply Or.inr
    have hgood := not_or.mp hbadz
    have hgood' := not_or.mp hgood.2
    let U := fx z.2
    let V := fu z.2
    have hU : Orthonormal ℝ U := HaarFrame.frame_orthonormal _ _ hx _
    have hV : Orthonormal ℝ V := HaarFrame.frame_orthonormal _ _ hu _
    let q := literalRun P A τ p z.1.2 U V N 0 (initial z.1.1,0)
    have hincomplete : q.2<(P.macroNode.n+1)*(P.n+1) := Nat.lt_of_not_ge hactz
    have hinitx : macroInitial (dx:=dx) initialC Prod.snd (z.1,V)=
        lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V z.1.2 (initial z.1.1,0) U := by
      simp [macroInitial,lift,prefixColumns,macroSchedule,initialC]
      change (0,(0:Frame dx (P.macroNode.n+1)))=(0,prefixColumns U 0)
      congr 1
    have hinitu : microInitial (du:=du) initialC Prod.snd (z.1,U)=
        lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U z.1.2 (initial z.1.1,0) V := by
      simp [microInitial,lift,prefixColumns,microSchedule,initialC]
      change (0,(0:Frame du ((P.macroNode.n+1)*(P.n+1))))=(0,prefixColumns V 0)
      congr 1
    have hxo : SourceObserved (literalMacroRules P A τ p)
        ((P.macroNode.width/4)^2/(4*P.macroNode.radius^2)) N 0
        (lift (macroSchedule (P.macroNode.n+1) (P.n+1)) V z.1.2 (initial z.1.1,0) U,(⊥,∅)) U := by
      rw [←hinitx]
      exact not_not.mp hgood.1
    have huo : SourceObserved (literalMicroRules P A τ p) (τ^2/(4*P.radius^2)) N 0
        (lift (microSchedule ((P.macroNode.n+1)*(P.n+1))) U z.1.2 (initial z.1.1,0) V,(⊥,∅)) V := by
      rw [←hinitu]
      exact not_not.mp hgood'.1
    have hs := source_observed_terminal_prefix P A U hU V hV τ p z.1.2 (initial z.1.1) N κ
      (P.macroNode.width/4) τ hRx hRu (by positivity) hτ hxo huo
    have hr : (macroSchedule (P.macroNode.n+1) (P.n+1)).count q.2<P.macroNode.n+1 := by
      rw [macroSchedule_count _ _ _ (Nat.succ_pos _),min_eq_left hincomplete.le]
      exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr hincomplete
    have hm := hbarrier U hU V hV q.2 hr (A.output q.1) hs
    have heq : originalRun P A U hU V hV τ p z.1.2 N 0 (initial z.1.1,0)=q := by
      by_contra hne
      exact hgood'.2 ⟨N,le_rfl,hne⟩
    change 8*ε≤‖gradient ((framedParameters P U hU V hV).outerMean κ)
      (A.output (originalRun P A U hU V hV τ p z.1.2 N 0 (initial z.1.1,0)).1)‖
    rw [heq]
    exact hm
  have hmono := measureReal_mono (μ:=μ) hcover
  have hsum := measureReal_union_le (B∪act) G (μ:=μ)
  have hsum' := measureReal_union_le B act (μ:=μ)
  have huniv : μ.real Set.univ=1 := measureReal_univ_eq_one
  refine ⟨hx,hu,?_⟩
  change 13/16≤μ.real G
  linarith

end Bilevel.PolishedLiteralActualObserver
