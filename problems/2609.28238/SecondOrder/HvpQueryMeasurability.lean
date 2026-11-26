import SecondOrder.BranchedOja

namespace SecondOrder
noncomputable section

def hvpQueryEquiv (d : ℕ) : HvpQuery d ≃ Point d ⊕ (Point d × Point d) where
  toFun q := match q with | .grad x => .inl x | .hvp x v => .inr (x,v)
  invFun q := q.elim HvpQuery.grad (fun xv => .hvp xv.1 xv.2)
  left_inv q := by cases q <;> rfl
  right_inv q := by rcases q with x|⟨x,v⟩ <;> rfl

instance hvpQueryMeasurableSpace (d : ℕ) : MeasurableSpace (HvpQuery d) :=
  MeasurableSpace.comap (hvpQueryEquiv d) inferInstance

def hvpQueryMeasurableEquiv (d : ℕ) : HvpQuery d ≃ᵐ Point d ⊕ (Point d × Point d) where
  toEquiv := hvpQueryEquiv d
  measurable_toFun := comap_measurable _
  measurable_invFun := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (hvpQueryEquiv d).symm (MeasurableSpace.comap (hvpQueryEquiv d) _)≤_
    rw [MeasurableSpace.comap_comp]
    simp only [Equiv.self_comp_symm,MeasurableSpace.comap_id]
    exact le_rfl

theorem queryPoint_measurable (d : ℕ) : Measurable (@queryPoint d) := by
  have hh := (measurable_id.sumElim measurable_fst).comp (hvpQueryMeasurableEquiv d).measurable
  convert hh using 1
  funext q
  cases q <;> rfl

theorem extractHvp_measurable (d : ℕ) : Measurable (fun w : HvpQuery d × RichReply d => extractHvp w.1 w.2) := by
  have hleft : Measurable (fun w : RichReply d × Point d => w.1.2.1) := measurable_fst.snd.fst
  have hright : Measurable (fun w : RichReply d × (Point d × Point d) => w.1.2.2 w.2.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp
      (measurable_fst.snd.snd.prodMk measurable_snd.snd)
  have hh := (measurable_prod_sum_elim hleft hright).comp
    (measurable_snd.prodMk ((hvpQueryMeasurableEquiv d).measurable.comp measurable_fst))
  convert hh using 1
  funext w
  rcases w with ⟨q,r⟩
  cases q <;> rfl

end
end SecondOrder
