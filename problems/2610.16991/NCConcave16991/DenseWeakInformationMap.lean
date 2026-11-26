import NCConcave16991.DenseWeakActualChannel

/-! # Information identities for actual finite pushforwards and reindexings -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {A I J K : Type*} [Fintype A] [Fintype I] [Fintype J] [Fintype K]

theorem map_map_mass (P : FiniteLaw A) (f : A → I) (g : I → J) :
    ((P.map f).map g).mass = (P.map (g ∘ f)).mass := by
  funext j
  change (P.map f).eventMass {i | g i = j} = P.eventMass {a | g (f a) = j}
  rw [map_eventMass]
  rfl

theorem map_equiv_mass (P : FiniteLaw I) (e : I ≃ J) (j : J) :
    (P.map e).mass j = P.mass (e.symm j) := by
  simp only [map]
  have he (i : I) : e i = j ↔ i = e.symm j := e.apply_eq_iff_eq_symm_apply
  simp_rw [he]
  simp

theorem map_equiv_entropy (P : FiniteLaw I) (e : I ≃ J) :
    (P.map e).entropy = P.entropy := by
  unfold entropy finiteEntropy
  simp only [map_equiv_mass]
  apply Fintype.sum_equiv e.symm
  intro j
  rfl

theorem map_pair_snd_mass (P : FiniteLaw A) (label : A → I) (history : A → J) (j : J) :
    (P.map (fun a ↦ (label a,history a))).snd.mass j = P.eventMass {a | history a = j} := by
  simp only [snd, map, eventMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : history a = j <;> simp [Prod.mk.injEq, ha]

theorem equiv_second_mutualInformation (P : FiniteLaw (I × J)) (e : J ≃ K) :
    (P.map (Equiv.prodCongr (Equiv.refl I) e)).mutualInformation = P.mutualInformation := by
  let Q := P.map (Equiv.prodCongr (Equiv.refl I) e)
  have hQmass (i : I) (k : K) : Q.mass (i,k) = P.mass (i,e.symm k) :=
    map_equiv_mass P (Equiv.prodCongr (Equiv.refl I) e) (i,k)
  have hfst : Q.fst.mass = P.fst.mass := by
    funext i
    change (∑ k, Q.mass (i,k)) = ∑ j, P.mass (i,j)
    simp_rw [hQmass]
    apply Fintype.sum_equiv e.symm
    intro k
    rfl
  have hsnd : Q.snd.mass = (P.snd.map e).mass := by
    funext k
    change (∑ i, Q.mass (i,k)) = _
    simp_rw [hQmass]
    rw [map_equiv_mass]
    rfl
  have hH : Q.entropy = P.entropy := map_equiv_entropy P _
  have hF : Q.fst.entropy = P.fst.entropy := congrArg finiteEntropy hfst
  have hS : Q.snd.entropy = P.snd.entropy := by
    change finiteEntropy _ = _
    rw [hsnd]
    exact map_equiv_entropy P.snd e
  change Q.mutualInformation = _
  simp only [mutualInformation, hH, hF, hS]

theorem map_second_equiv_information (P : FiniteLaw A) (label : A → I)
    (history : A → J) (e : J ≃ K) :
    (P.map (fun a ↦ (label a,e (history a)))).mutualInformation =
      (P.map (fun a ↦ (label a,history a))).mutualInformation := by
  have hm := map_map_mass P (fun a ↦ (label a,history a))
    (Equiv.prodCongr (Equiv.refl I) e)
  have hEq : (P.map (fun a ↦ (label a,history a))).map (Equiv.prodCongr (Equiv.refl I) e) =
      P.map (fun a ↦ (label a,e (history a))) := by
    exact eq_of_mass_eq _ _ hm
  rw [← hEq]
  exact equiv_second_mutualInformation _ e

theorem condition_map_congr_mass (P : FiniteLaw A) (E : Set A)
    (hE : 0 < P.eventMass E) (f g : A → I) (hfg : ∀ a ∈ E, f a = g a) :
    ((P.condition E hE).map f).mass = ((P.condition E hE).map g).mass := by
  funext i
  simp only [map, condition]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ E
  · rw [hfg a ha]
  · simp [ha]

theorem triple_labelHistory_mass (P : FiniteLaw A) (history : A → I)
    (label : A → J) (reply : A → K) :
    (P.map (fun a ↦ (history a,(label a,reply a)))).labelHistory.mass =
      (P.map (fun a ↦ (label a,history a))).mass := by
  funext z
  rcases z with ⟨l,h⟩
  simp only [labelHistory, historyLabels, map]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hh : history a = h <;> by_cases hl : label a = l <;>
    simp [Prod.mk.injEq, hh, hl]

theorem triple_labelHistoryReply_mass (P : FiniteLaw A) (history : A → I)
    (label : A → J) (reply : A → K) :
    (P.map (fun a ↦ (history a,(label a,reply a)))).labelHistoryReply.mass =
      (P.map (fun a ↦ (label a,(history a,reply a)))).mass := by
  funext z
  rcases z with ⟨l,h,y⟩
  simp only [labelHistoryReply, map]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp [Prod.mk.injEq, and_comm, and_left_comm]

theorem constant_reply_information (P : FiniteLaw A) (label : A → I)
    [Subsingleton J] [Nonempty J] (history : A → J) :
    (P.map (fun a ↦ (label a,history a))).mutualInformation = 0 := by
  letI : Unique J := ⟨⟨Classical.choice ‹Nonempty J›⟩,fun _ ↦ Subsingleton.elim _ _⟩
  let Q := P.map (fun a ↦ (label a,history a))
  have hprod : Q.mass = (Q.fst.product (uniform J)).mass := by
    funext z
    have hf : Q.fst.mass z.1 = Q.mass z := by
      simp only [fst, rowMass, Fintype.sum_unique, Subsingleton.elim (default : J) z.2]
    simp only [product, uniform, Fintype.card_unique, Nat.cast_one, inv_one, mul_one, hf]
  have hQ : Q.entropy = Q.fst.entropy + (uniform J).entropy := by
    rw [entropy, hprod]
    exact product_entropy _ _
  have hs : Q.snd.mass = (uniform J).mass := by
    funext j
    have he : Q.snd.mass j = 1 := by
      simpa only [Fintype.sum_unique, Subsingleton.elim (default : J) j] using Q.snd.sum_one
    simpa only [uniform, Fintype.card_unique, Nat.cast_one, inv_one] using he
  have hS : Q.snd.entropy = (uniform J).entropy := congrArg finiteEntropy hs
  change Q.mutualInformation = 0
  simp only [mutualInformation, hQ, hS]
  ring

end NCConcave16991.DenseWeakHiding.FiniteLaw
