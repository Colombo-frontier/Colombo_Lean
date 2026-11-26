import Bilevel.TransportAugmentedAnyStore

/-! A public energy budget may dominate the calculated observer envelope.
The monotonicity changes no run, prior, release schedule or terminal output. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

theorem FrameObservedAny.mono (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hB : 0<B) (initial : C → S) (N : ℕ) {a b : ℝ} (hab : a≤b)
    (output : Fin k → CommonState C S k T D → Space D)
    (ho : ∀ i,Measurable (output i)) (i : Fin k)
    (s : C × TransportNetworkAuxiliary.Sample n D k)
    (h : FrameObservedAny P A hTnet hT hB initial N a output ho i s) :
    FrameObservedAny P A hTnet hT hB initial N b output ho i s := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ j => exact OrdinaryFrame.observed_mono _ hab _ _ _ _ _ h

theorem CompleteGoodAny.mono_aux (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hB : 0<B) (initial : C → S) (N : ℕ) (networkCap : ℝ) {a b : ℝ} (hab : a≤b)
    (output : Fin k → CommonState C S k T D → Space D)
    (ho : ∀ i,Measurable (output i)) (s : C × TransportNetworkAuxiliary.Sample n D k)
    (h : CompleteGoodAny P A hTnet hT hB initial N networkCap a output ho s) :
    CompleteGoodAny P A hTnet hT hB initial N networkCap b output ho s :=
  ⟨h.1,fun i => FrameObservedAny.mono P A hTnet hT hB initial N hab output ho i s (h.2 i)⟩

theorem complete_observer_budget (hk : 0<k) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hn : 0<n) (hpos : 0<Tnet) (hB : 0<B) (initial : C → S) (hi : Measurable initial)
    (N r : ℕ) (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i))
    {networkCap cap δ e : ℝ} (hb : 0<networkCap) (hδ : 0<δ)
    (hDnet : observerDimension n p Tnet (N+1) networkCap δ≤D)
    (he : 0<e) (he2 : e≤2) (hDaux : (2*(N*B)+1)+(N*B)+(r+1)≤D)
    (hsmall : ((N*B:ℕ):ℝ)*(((2*(N*B)+1:ℕ):ℝ)*e)≤1/2)
    (hcap : 2*((2*(N*B)+1:ℕ):ℝ)*e≤cap) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬CompleteGoodAny P A hTnet hT hB initial N networkCap cap output ho s}≤
      ENNReal.ofReal δ+(k:ℝ≥0∞)*(((2*(N*B)+1:ℕ):ℝ≥0∞)*GenieProtocol.failurePerQuery (T+1) r e) := by
  have hp := complete_observer_any hk ρ P A hTnet hT hn hpos hB initial hi N r output ho hb hδ hDnet he he2 hDaux hsmall
  refine (measure_mono ?_).trans hp
  intro s hbad hgood
  exact hbad (CompleteGoodAny.mono_aux P A hTnet hT hB initial N networkCap hcap output ho s hgood)

end Bilevel.TransportAugmented
