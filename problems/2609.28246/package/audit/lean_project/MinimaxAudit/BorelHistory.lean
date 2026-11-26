import MinimaxAudit.RevisedModel

open Set MeasureTheory
namespace MinimaxAudit
noncomputable section
namespace BorelHistory
variable {p dx dy : ℕ}
abbrev Entry (p dx dy : ℕ) := SaddleSpace dx dy × ScalarJet p (SaddleSpace dx dy)

theorem history_ofFn_measurable (n : ℕ) :
    Measurable (fun v : Fin n → Entry p dx dy => List.ofFn v :
      (Fin n → Entry p dx dy) → ScalarHistory p dx dy) := by
  change Measurable[_, MeasurableSpace.comap historyEncoding inferInstance] _
  apply measurable_comap_iff.2
  have he : (historyEncoding ∘ (fun v : Fin n → Entry p dx dy => List.ofFn v)) =
      (fun v => (⟨n, v⟩ : Σ k : ℕ, Fin k → Entry p dx dy)) := by
    funext v
    simp [historyEncoding]
    apply (Fin.heq_fun_iff (by simp)).2
    intro i
    rfl
  rw [he]
  apply Measurable.of_le_map
  exact iInf_le _ n

/-- A map on finite histories is measurable precisely when each fixed-length
Borel sequence restriction is measurable. -/
theorem measurable_history_iff {B : Type*} [MeasurableSpace B]
    (f : ScalarHistory p dx dy → B) :
    Measurable f ↔ ∀ n, Measurable (fun v : Fin n → Entry p dx dy => f (List.ofFn v)) := by
  constructor
  · intro hf n
    exact hf.comp (history_ofFn_measurable n)
  · intro hf
    have hd : Measurable (fun s : Σ n : ℕ, Fin n → Entry p dx dy => f (List.ofFn s.2)) := by
      apply measurable_iff_comap_le.2
      change MeasurableSpace.comap _ _ ≤ ⨅ n : ℕ, MeasurableSpace.map (Sigma.mk n) _
      apply le_iInf
      intro n
      apply MeasurableSpace.comap_le_iff_le_map.1
      simpa only [MeasurableSpace.comap_comp, Function.comp_def] using (hf n).comap_le
    have henc : Measurable (historyEncoding (p := p) (dx := dx) (dy := dy)) :=
      comap_measurable _
    have hh := hd.comp henc
    have heq : (fun s : Σ n : ℕ, Fin n → Entry p dx dy => f (List.ofFn s.2)) ∘ historyEncoding = f := by
      funext h
      simp [historyEncoding]
    rwa [heq] at hh

/-- A Borel Option decision has a measurable stop set under the canonical
Option encoding, without assuming an unrelated library Option sigma algebra. -/
theorem measurable_query_none {Omega : Type*} [MeasurableSpace Omega]
    {q : Omega → Option (SaddleSpace dx dy)} (hq : Measurable q) :
    MeasurableSet {w | q w = none} := by
  have he := (comap_measurable optionPointEncoding).comp hq
  convert he (measurableSet_range_inl : MeasurableSet
    (Set.range (Sum.inl : Unit → Unit ⊕ SaddleSpace dx dy))) using 1
  ext w
  cases hw : q w <;> simp [optionPointEncoding, hw]

end BorelHistory
end
end MinimaxAudit
