import Nonsmooth.SelectedUpdate

open MeasureTheory Function
open scoped ENNReal InnerProductSpace
set_option autoImplicit false
universe u
namespace Nonsmooth
noncomputable section

/-- A length-n word of query choices, in recursive product form. -/
def QueryBranches (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => QueryBranches ι n × ι

instance queryBranches_countable {ι : Type u} [Countable ι] :
    (n : ℕ) → Countable (QueryBranches ι n)
  | 0 => inferInstanceAs (Countable PUnit.{u + 1})
  | n + 1 => by
    letI := queryBranches_countable (ι := ι) n
    exact inferInstanceAs (Countable (QueryBranches ι n × ι))

instance queryBranches_measurableSpace {ι : Type u} [MeasurableSpace ι] :
    (n : ℕ) → MeasurableSpace (QueryBranches ι n)
  | 0 => inferInstanceAs (MeasurableSpace PUnit.{u + 1})
  | n + 1 => by
    letI := queryBranches_measurableSpace (ι := ι) n
    exact inferInstanceAs (MeasurableSpace (QueryBranches ι n × ι))

instance queryBranches_measurableSingleton {ι : Type u} [MeasurableSpace ι]
    [MeasurableSingletonClass ι] : (n : ℕ) → MeasurableSingletonClass (QueryBranches ι n)
  | 0 => inferInstanceAs (MeasurableSingletonClass PUnit.{u + 1})
  | n + 1 => by
    letI := queryBranches_measurableSingleton (ι := ι) n
    exact inferInstanceAs (MeasurableSingletonClass (QueryBranches ι n × ι))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [mE : MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
variable {ι : Type u} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def protocolBranch (decision : ℕ → E → ι) : (n : ℕ) → E → QueryBranches ι n
  | 0, _ => PUnit.unit
  | n + 1, x => (protocolBranch decision n x, decision n x)

def protocolSpace (q : (n : ℕ) → QueryBranches ι n → ι → E) :
    (n : ℕ) → QueryBranches ι n → Submodule ℝ E
  | 0, _ => ⊥
  | n + 1, p => protocolSpace q n p.1 ⊔ ℝ ∙ q n p.1 p.2

def protocolResponse (q : (n : ℕ) → QueryBranches ι n → ι → E)
    (decision : ℕ → E → ι) (n : ℕ) (x : E) : ℝ :=
  ⟪q n (protocolBranch decision n x) (decision n x), x⟫_ℝ

/-- Only the scalar responses are added to the information at each round. -/
def protocolInformation (q : (n : ℕ) → QueryBranches ι n → ι → E)
    (decision : ℕ → E → ι) : ℕ → MeasurableSpace E
  | 0 => ⊥
  | n + 1 => protocolInformation q decision n ⊔
    MeasurableSpace.comap (protocolResponse q decision n) inferInstance

theorem orthogonal_unit_extension_finrank (K : Submodule ℝ E) {v : E}
    (hv : v ∈ Kᗮ) (hvn : ‖v‖ = 1) :
    Module.finrank ℝ (K ⊔ ℝ ∙ v : Submodule ℝ E) = Module.finrank ℝ K + 1 := by
  have hv0 : v ≠ 0 := by intro h; simp only [h, norm_zero] at hvn; exact zero_ne_one hvn
  have hs : (ℝ ∙ v) ≤ Kᗮ := Submodule.span_le.mpr (by
    intro x hx
    have hxeq : x = v := Set.mem_singleton_iff.mp hx
    subst x
    exact hv)
  have hinf : (K ⊓ (ℝ ∙ v) : Submodule ℝ E) = ⊥ := le_antisymm
    ((inf_le_inf_left K hs).trans (le_of_eq K.inf_orthogonal_eq_bot)) bot_le
  have h := Submodule.finrank_sup_add_finrank_inf_eq K (ℝ ∙ v)
  rw [hinf, finrank_bot, add_zero, finrank_span_singleton hv0] at h
  exact h

theorem projectionInformation_bot : projectionInformation (mE := mE) (⊥ : Submodule ℝ E) = ⊥ := by
  simp only [projectionInformation, Submodule.orthogonalProjection_bot, ContinuousLinearMap.zero_apply,
    Submodule.coe_zero, MeasurableSpace.comap_const]

/-- These five invariants connect actual scalar histories to the countably branching posterior. -/
theorem countable_protocol_invariants
    (q : (n : ℕ) → QueryBranches ι n → ι → E) (decision : ℕ → E → ι)
    (T : ℕ) (hT : T ≤ Module.finrank ℝ E)
    (hdecision : ∀ n < T, @Measurable E ι (protocolInformation q decision n) inferInstance (decision n))
    (hq : ∀ n < T, ∀ b i, q n b i ∈ (protocolSpace q n b)ᗮ)
    (hqn : ∀ n < T, ∀ b i, ‖q n b i‖ = 1) :
    ∀ n ≤ T,
      Measurable (protocolBranch decision n) ∧
      (∀ b, MeasurableSet[projectionInformation (protocolSpace q n b)]
        {x | protocolBranch decision n x = b}) ∧
      selectedProjectionInformation (protocolSpace q n) (protocolBranch decision n) =
        protocolInformation q decision n ∧
      (∀ b, Module.finrank ℝ (protocolSpace q n b) = n) ∧
      (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | protocolInformation q decision n]) x‖ ^ 2
        ∂sphericalLaw E) = (n : ℝ) / (Module.finrank ℝ E : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨measurable_const, ?_, ?_, ?_, ?_⟩
    · intro b
      cases b
      simp only [protocolBranch, Set.setOf_true, MeasurableSet.univ]
    · change MeasurableSpace.comap
        (fun x : E => (PUnit.unit, selectedProjection (protocolSpace q 0) (protocolBranch decision 0) x)) _ = ⊥
      have hz : selectedProjection (protocolSpace q 0) (protocolBranch decision 0) =
          (fun _ : E => (0 : E)) := by
        funext x
        change ((⊥ : Submodule ℝ E).orthogonalProjection x : E) = 0
        exact (Submodule.mem_bot ℝ).mp ((⊥ : Submodule ℝ E).orthogonalProjection x).property
      rw [hz]
      exact MeasurableSpace.comap_const _
    · intro b
      exact finrank_bot ℝ E
    · simpa only [protocolInformation, projectionInformation_bot, finrank_bot, Nat.cast_zero, zero_div]
        using spherical_condExp_projection_energy (E := E) (⊥ : Submodule ℝ E)
  | succ n ih =>
    intro hnT
    have hnlt : n < T := Nat.lt_of_succ_le hnT
    obtain ⟨hc, hbranch, hinfo, hrank, henergy⟩ := ih (Nat.le_of_succ_le hnT)
    have hnext : @Measurable E ι
        (selectedProjectionInformation (protocolSpace q n) (protocolBranch decision n)) inferInstance
        (decision n) := by rw [hinfo]; exact hdecision n hnlt
    have hnexta : Measurable (decision n) :=
      hnext.mono (selectedProjectionInformation_le _ hc) le_rfl
    have hnewinfo : selectedProjectionInformation (protocolSpace q (n + 1)) (protocolBranch decision (n + 1)) =
        protocolInformation q decision (n + 1) := by
      change selectedProjectionInformation
        (fun p : QueryBranches ι n × ι => protocolSpace q n p.1 ⊔ ℝ ∙ q n p.1 p.2)
        (fun x => (protocolBranch decision n x, decision n x)) = _
      rw [selected_refinement_information _ _ _ hnext _ (hq n hnlt) (hqn n hnlt), hinfo]
      rfl
    refine ⟨hc.prodMk hnexta, ?_, hnewinfo, ?_, ?_⟩
    · exact selected_refinement_branch _ _ hbranch _ hnext _
    · intro b
      rw [protocolSpace, orthogonal_unit_extension_finrank _ (hq n hnlt b.1 b.2)
        (hqn n hnlt b.1 b.2), hrank]
    · have hnd : n < Module.finrank ℝ E := lt_of_lt_of_le hnlt hT
      have hrem : ∀ b, Module.finrank ℝ (protocolSpace q n b)ᗮ = Module.finrank ℝ E - n := by
        intro b
        have hd := (protocolSpace q n b).finrank_add_finrank_orthogonal
        rw [hrank] at hd
        omega
      have hrec := spherical_selected_posterior_energy_update (protocolSpace q n)
        (protocolBranch decision n) hc hbranch (decision n) hnext (q n) (hq n hnlt) (hqn n hnlt)
        (Module.finrank ℝ E - n) (Nat.sub_pos_of_lt hnd) hrem
      change (∫ x, ‖((sphericalLaw E)[(fun x : E => x) |
        selectedProjectionInformation (protocolSpace q (n + 1)) (protocolBranch decision (n + 1))]) x‖ ^ 2
        ∂sphericalLaw E) = _ at hrec
      rw [hnewinfo, hinfo, henergy] at hrec
      rw [hrec, Nat.cast_add, Nat.cast_one, Nat.cast_sub hnd.le]
      have hd : (Module.finrank ℝ E : ℝ) ≠ 0 := ne_of_gt (by
        exact_mod_cast lt_of_le_of_lt (Nat.zero_le n) hnd)
      have hndR : (n : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hnd
      have hr : (Module.finrank ℝ E : ℝ) - n ≠ 0 := ne_of_gt (sub_pos.mpr hndR)
      field_simp

/-- The manuscript's T/d posterior identity for actual multiround, countably branching,
orthogonal unit queries. No posterior-energy estimate is a premise. -/
theorem countable_protocol_energy
    (q : (n : ℕ) → QueryBranches ι n → ι → E) (decision : ℕ → E → ι)
    (T : ℕ) (hT : T ≤ Module.finrank ℝ E)
    (hdecision : ∀ n < T, @Measurable E ι (protocolInformation q decision n) inferInstance (decision n))
    (hq : ∀ n < T, ∀ b i, q n b i ∈ (protocolSpace q n b)ᗮ)
    (hqn : ∀ n < T, ∀ b i, ‖q n b i‖ = 1) :
    (∫ x, ‖((sphericalLaw E)[(fun x : E => x) | protocolInformation q decision T]) x‖ ^ 2
      ∂sphericalLaw E) = (T : ℝ) / (Module.finrank ℝ E : ℝ) :=
  (countable_protocol_invariants q decision T hT hdecision hq hqn T le_rfl).2.2.2.2

theorem countable_protocol_information_le
    (q : (n : ℕ) → QueryBranches ι n → ι → E) (decision : ℕ → E → ι)
    (T : ℕ) (hT : T ≤ Module.finrank ℝ E)
    (hdecision : ∀ n < T, @Measurable E ι (protocolInformation q decision n) inferInstance (decision n))
    (hq : ∀ n < T, ∀ b i, q n b i ∈ (protocolSpace q n b)ᗮ)
    (hqn : ∀ n < T, ∀ b i, ‖q n b i‖ = 1) :
    protocolInformation q decision T ≤ mE := by
  obtain ⟨hc, _, hi, _⟩ := countable_protocol_invariants q decision T hT hdecision hq hqn T le_rfl
  rw [← hi]
  exact selectedProjectionInformation_le _ hc

theorem countable_protocol_posterior
    (q : (n : ℕ) → QueryBranches ι n → ι → E) (decision : ℕ → E → ι)
    (T : ℕ) (hT : T ≤ Module.finrank ℝ E)
    (hdecision : ∀ n < T, @Measurable E ι (protocolInformation q decision n) inferInstance (decision n))
    (hq : ∀ n < T, ∀ b i, q n b i ∈ (protocolSpace q n b)ᗮ)
    (hqn : ∀ n < T, ∀ b i, ‖q n b i‖ = 1) :
    selectedProjection (protocolSpace q T) (protocolBranch decision T) =ᵐ[sphericalLaw E]
      (sphericalLaw E)[(fun x : E => x) | protocolInformation q decision T] := by
  obtain ⟨hc, hb, hi, _⟩ := countable_protocol_invariants q decision T hT hdecision hq hqn T le_rfl
  rw [← hi]
  exact spherical_condExp_selectedProjection _ hc hb


end
end Nonsmooth
