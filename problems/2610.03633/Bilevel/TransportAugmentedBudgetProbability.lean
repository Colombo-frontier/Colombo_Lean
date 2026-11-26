import Bilevel.TransportAugmentedBudget
import Bilevel.TransportUniformDimension

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

theorem complete_observer_of_budget (hk : 0<k) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet≤D) (hT : T+1≤D)
    (hn : 0<n) (hpos : 0<Tnet) (hB : 0<B) (initial : C → S) (hi : Measurable initial)
    (N : ℕ) (output : Fin k → CommonState C S k T D → Space D) (ho : ∀ i,Measurable (output i))
    {networkCap cap δ : ℝ} (hb : 0<networkCap) (hδ : 0<δ)
    (hbudget : ObserverBudget n p Tnet k T B D N networkCap cap δ) :
    (ρ.prod (TransportNetworkAuxiliary.law n D k))
      {s | ¬CompleteGoodAny P A hTnet hT hB initial N networkCap cap output ho s}≤ENNReal.ofReal δ := by
  rcases hbudget with ⟨r,e,hdn,hda,_,he,he2,hs,hc,hp⟩
  exact (complete_observer_budget hk ρ P A hTnet hT hn hpos hB initial hi N r output ho hb
    (half_pos hδ) hdn he he2 hda hs hc).trans hp

end Bilevel.TransportAugmented
