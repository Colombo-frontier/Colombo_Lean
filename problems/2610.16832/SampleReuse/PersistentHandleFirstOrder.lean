import SampleReuse.PersistentHandleLaw
import SampleReuse.PersistentComparison

open SecondOrder
namespace SampleReuse
noncomputable section

theorem persistentQueryRun_firstOrder {d T : ℕ} {H S : Type}
    (P : PersistentFirstOrderPolicy d T H S) (Θ : Fin (T+1) → Fin d → Bool)
    (A β : ℝ) {R : ℝ} (table : H → FirstOrderCoefficients d T R) : ∀ n,
    persistentQueryRun P (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) table n =
      persistentRichRun P Θ A β table n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [persistentQueryRun,persistentRichRun,ih]

/-- Exact unrestricted-label bridge for the actual hard scalar family.
The same normalization works simultaneously for every hidden vector. -/
theorem normalized_firstOrder_state_law {d T : ℕ} {H S : Type} (N : ℕ)
    (P : PersistentFirstOrderPolicy d T H S) (Θ : Fin (T+1) → Fin d → Bool)
    (A β : ℝ) {R : ℝ} (p : PMF (FirstOrderCoefficients d T R)) :
    (finitePiPMF (fun _ : Fin (N+1) => p)).map
      (fun table => (persistentRichRun (normalizePersistentPolicy N P) Θ A β table N).1) =
      lazyPersistentStateLaw P (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) p N := by
  simpa only [persistentQueryRun_firstOrder] using normalized_persistent_state_law N P
    (fun x z => richReply (scaledFirstOrderSample Θ A β) z x) p

end
end SampleReuse
