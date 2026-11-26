import HeavyTail.AdaptiveErasure

/-! Randomized algorithms with arbitrary measurable seed spaces. The algorithm
stores its seed probability law and its measurable adaptive policy together. -/
namespace HeavyTail
open MeasureTheory

structure RandomizedPolicy (X R Y : Type*)
    [MeasurableSpace X] [MeasurableSpace R] [MeasurableSpace Y] (T : ℕ) where
  Seed : Type
  seedSpace : MeasurableSpace Seed
  seedLaw : @Measure Seed seedSpace
  seedProbability : @IsProbabilityMeasure Seed seedSpace seedLaw
  policy : @AdaptivePolicy Seed X R Y seedSpace _ _ _ T

attribute [instance] RandomizedPolicy.seedSpace RandomizedPolicy.seedProbability

end HeavyTail
