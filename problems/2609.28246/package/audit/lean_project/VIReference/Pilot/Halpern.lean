import VIReference.Pilot.Contracts

/-!
# Kernel-checked Halpern proof components

These are the first nontrivial proof obligations behind `lem:firstdiff` and
`lem:second-energy`.  They are kept separate from the source contracts so the
pilot can report statement coverage and proof coverage independently.
-/

namespace VIReference.Pilot

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Firm nonexpansiveness implies ordinary nonexpansiveness. -/
theorem firmlyNonexpansive_norm_le {P : E → E} (hP : FirmlyNonexpansive P)
    (x y : E) : ‖P x - P y‖ ≤ ‖x - y‖ := by
  have h := hP x y
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  nlinarith [sq_nonneg ‖(x - P x) - (y - P y)‖]

/-- The exact `b_t` identity in `lem:firstdiff`. -/
theorem firstDifference_identity {P : E → E} {x0 : E} {x y : ℕ → E}
    (horbit : IsHalpernOrbit P x0 x y) (t : ℕ) (ht : 2 ≤ t) :
    x t - x (t - 1) =
      ((t : ℝ) / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2)) +
      (1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0) := by
  have ht_one : 1 ≤ t := by omega
  have ht_sub_one : t - 1 + 1 = t := by omega
  have ht_sub_two : t - 2 + 1 = t - 1 := by omega
  have hxt := horbit.2.2 (t - 1)
  have hxprev := horbit.2.2 (t - 2)
  rw [ht_sub_one] at hxt
  rw [ht_sub_two] at hxprev
  rw [Nat.cast_sub ht_one] at hxt
  rw [Nat.cast_sub ht] at hxprev
  rw [hxt, hxprev]
  push_cast
  have htR : (t : ℝ) ≠ 0 := by positivity
  have htpR : 1 + (t : ℝ) ≠ 0 := by positivity
  have hpolyR : (t : ℝ) + (t : ℝ) ^ 2 ≠ 0 := by positivity
  have hcancel := mul_inv_cancel₀ htpR
  match_scalars
  all_goals norm_num
  all_goals field_simp [htR, htpR, hpolyR]
  all_goals ring_nf
  all_goals nlinarith [hcancel]

/-- Every exact Halpern iterate stays in the radius-`R` ball around a fixed
point.  This discharges the contextual sentence immediately before
`lem:firstdiff`; it is not an extra assumption added to the audited lemma. -/
theorem halpern_orbit_stays {P : E → E} {zStar x0 : E} {x y : ℕ → E}
    {R : ℝ} (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (horbit : IsHalpernOrbit P x0 x y) (hR : ‖x0 - zStar‖ ≤ R) :
    ∀ t, ‖x t - zStar‖ ≤ R ∧ ‖y t - zStar‖ ≤ R := by
  intro t
  induction t with
  | zero =>
      have hx : ‖x 0 - zStar‖ ≤ R := by simpa [horbit.1] using hR
      refine ⟨hx, ?_⟩
      rw [horbit.2.1 0, ← hfix]
      exact (firmlyNonexpansive_norm_le hP (x 0) zStar).trans hx
  | succ t ih =>
      have ha : 0 ≤ (1 / (t + 2 : ℝ)) := by positivity
      have hb : 0 ≤ ((t + 1 : ℝ) / (t + 2 : ℝ)) := by positivity
      have hab : (1 / (t + 2 : ℝ)) +
          ((t + 1 : ℝ) / (t + 2 : ℝ)) = 1 := by
        field_simp
        ring
      have hx : ‖x (t + 1) - zStar‖ ≤ R := by
        rw [horbit.2.2 t]
        have hid :
            (1 / (t + 2 : ℝ)) • x0 +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) • y t - zStar =
              (1 / (t + 2 : ℝ)) • (x0 - zStar) +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) • (y t - zStar) := by
          have hden : 2 + (t : ℝ) ≠ 0 := by positivity
          match_scalars
          all_goals norm_num
          all_goals field_simp [hden]
          all_goals ring_nf
        rw [hid]
        calc
          ‖(1 / (t + 2 : ℝ)) • (x0 - zStar) +
              ((t + 1 : ℝ) / (t + 2 : ℝ)) • (y t - zStar)‖
              ≤ ‖(1 / (t + 2 : ℝ)) • (x0 - zStar)‖ +
                ‖((t + 1 : ℝ) / (t + 2 : ℝ)) • (y t - zStar)‖ :=
                  norm_add_le _ _
          _ = (1 / (t + 2 : ℝ)) * ‖x0 - zStar‖ +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) * ‖y t - zStar‖ := by
                  rw [norm_smul, norm_smul]
                  simp only [Real.norm_eq_abs]
                  rw [abs_of_nonneg ha, abs_of_nonneg hb]
          _ ≤ (1 / (t + 2 : ℝ)) * R +
                ((t + 1 : ℝ) / (t + 2 : ℝ)) * R := by
                  gcongr
                  exact ih.2
          _ = R := by rw [← add_mul, hab, one_mul]
      refine ⟨hx, ?_⟩
      rw [horbit.2.1 (t + 1), ← hfix]
      exact (firmlyNonexpansive_norm_le hP (x (t + 1)) zStar).trans hx

/-- Scalar induction used for the harmonic first-difference estimate. -/
theorem harmonic_recurrence_bound (u : ℕ → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hbase : u 1 ≤ R)
    (hrec : ∀ t, 2 ≤ t →
      u t ≤ ((t : ℝ) / (t + 1 : ℝ)) * u (t - 1) +
        2 * R / ((t : ℝ) * (t + 1 : ℝ))) :
    ∀ t, 1 ≤ t → u t ≤ 2 * R * harmonicR t / (t + 1 : ℝ) := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
      norm_num [harmonicR]
      exact hbase
  | succ t ht ih =>
      have hstep := hrec (t + 1) (by omega)
      have hsub : t + 1 - 1 = t := by omega
      rw [hsub] at hstep
      have hcoef : 0 ≤ ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) + 1 : ℝ) := by
        positivity
      have hmul := mul_le_mul_of_nonneg_left ih hcoef
      calc
        u (t + 1) ≤ ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) + 1 : ℝ) * u t +
            2 * R / (((t + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) + 1 : ℝ)) := hstep
        _ ≤ ((t + 1 : ℕ) : ℝ) / ((t + 1 : ℕ) + 1 : ℝ) *
              (2 * R * harmonicR t / (t + 1 : ℝ)) +
            2 * R / (((t + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) + 1 : ℝ)) := by
              simpa [add_comm] using
                add_le_add_right hmul
                  (2 * R / (((t + 1 : ℕ) : ℝ) * ((t + 1 : ℕ) + 1 : ℝ)))
        _ = 2 * R * harmonicR (t + 1) / ((t + 1 : ℕ) + 1 : ℝ) := by
              rw [harmonicR]
              push_cast
              have ht0 : (t : ℝ) + 1 ≠ 0 := by positivity
              have ht1 : (t : ℝ) + 2 ≠ 0 := by positivity
              field_simp [ht0, ht1]

theorem harmonicR_nonneg (t : ℕ) : 0 ≤ harmonicR t := by
  induction t with
  | zero => simp [harmonicR]
  | succ t ih =>
      rw [harmonicR]
      positivity

theorem harmonicR_monotone : Monotone harmonicR := by
  apply monotone_nat_of_le_succ
  intro t
  rw [harmonicR]
  have : 0 ≤ (1 / (t + 1 : ℝ)) := by positivity
  linarith

/-- Finite telescoping form used by the firm-energy argument. -/
theorem finite_energy_telescope (A D Q : ℕ → ℝ) {k ell : ℕ}
    (hkle : k ≤ ell)
    (hpoint : ∀ t, k ≤ t → t ≤ ell →
      D t ≤ A (t - 1) - A t + Q t) :
    (∑ t ∈ Finset.Icc k ell, D t) ≤
      A (k - 1) - A ell + ∑ t ∈ Finset.Icc k ell, Q t := by
  induction ell, hkle using Nat.le_induction with
  | base =>
      simp only [Finset.Icc_self, Finset.sum_singleton]
      exact hpoint k le_rfl le_rfl
  | succ ell hkle ih =>
      rw [Finset.sum_Icc_succ_top (by omega) D]
      rw [Finset.sum_Icc_succ_top (by omega) Q]
      have hlast := hpoint (ell + 1) (by omega) le_rfl
      have hprev : ell + 1 - 1 = ell := by omega
      rw [hprev] at hlast
      have hi := ih (fun t hkt hte => hpoint t hkt (by omega))
      linarith

/-- Kernel proof of all conclusions in `lem:firstdiff`. -/
theorem firstDifference {P : E → E} {zStar x0 : E} {x y : ℕ → E}
    {R : ℝ} (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (horbit : IsHalpernOrbit P x0 x y) (hR : ‖x0 - zStar‖ ≤ R) :
    FirstDifferenceConclusion x0 x y R := by
  have hR0 : 0 ≤ R := (norm_nonneg (x0 - zStar)).trans hR
  have hstay := halpern_orbit_stays hP hfix horbit hR
  have hyx0 : ∀ t, ‖y t - x0‖ ≤ 2 * R := by
    intro t
    have hsplit : y t - x0 = (y t - zStar) + (zStar - x0) := by abel
    calc
      ‖y t - x0‖ = ‖(y t - zStar) + (zStar - x0)‖ := by rw [hsplit]
      _ ≤ ‖y t - zStar‖ + ‖zStar - x0‖ := norm_add_le _ _
      _ = ‖y t - zStar‖ + ‖x0 - zStar‖ := by rw [norm_sub_rev zStar x0]
      _ ≤ R + R := add_le_add (hstay t).2 hR
      _ = 2 * R := by ring
  have ha_le : ∀ t, 1 ≤ t →
      ‖y t - y (t - 1)‖ ≤ ‖x t - x (t - 1)‖ := by
    intro t _ht
    rw [horbit.2.1 t, horbit.2.1 (t - 1)]
    exact firmlyNonexpansive_norm_le hP _ _
  have hbbase : ‖x 1 - x 0‖ ≤ R := by
    have hx1 := horbit.2.2 0
    norm_num at hx1
    have hid : x 1 - x 0 = (1 / 2 : ℝ) • (y 0 - x0) := by
      rw [hx1, horbit.1]
      module
    rw [hid, norm_smul]
    norm_num [Real.norm_eq_abs]
    nlinarith [hyx0 0]
  have hbrec : ∀ t, 2 ≤ t →
      ‖x t - x (t - 1)‖ ≤
        ((t : ℝ) / (t + 1 : ℝ)) * ‖x (t - 1) - x (t - 2)‖ +
          2 * R / ((t : ℝ) * (t + 1 : ℝ)) := by
    intro t ht
    rw [firstDifference_identity horbit t ht]
    calc
      ‖((t : ℝ) / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2)) +
          (1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0)‖
          ≤ ‖((t : ℝ) / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2))‖ +
            ‖(1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0)‖ :=
              norm_add_le _ _
      _ = ((t : ℝ) / (t + 1 : ℝ)) * ‖y (t - 1) - y (t - 2)‖ +
            (1 / ((t : ℝ) * (t + 1 : ℝ))) * ‖y (t - 2) - x0‖ := by
              rw [norm_smul, norm_smul]
              simp only [Real.norm_eq_abs]
              rw [abs_of_nonneg (by positivity : 0 ≤ (t : ℝ) / (t + 1 : ℝ))]
              rw [abs_of_nonneg (by positivity :
                0 ≤ (1 : ℝ) / ((t : ℝ) * (t + 1 : ℝ)))]
      _ ≤ ((t : ℝ) / (t + 1 : ℝ)) * ‖x (t - 1) - x (t - 2)‖ +
            (1 / ((t : ℝ) * (t + 1 : ℝ))) * (2 * R) := by
              gcongr
              · exact ha_le (t - 1) (by omega)
              · exact hyx0 (t - 2)
      _ = ((t : ℝ) / (t + 1 : ℝ)) * ‖x (t - 1) - x (t - 2)‖ +
            2 * R / ((t : ℝ) * (t + 1 : ℝ)) := by ring
  have hb : ∀ t, 1 ≤ t →
      ‖x t - x (t - 1)‖ ≤ 2 * R * harmonicR t / (t + 1 : ℝ) :=
    harmonic_recurrence_bound
      (fun t => ‖x t - x (t - 1)‖) R hR0 hbbase hbrec
  have hc : ∀ t, 2 ≤ t →
      ‖(x t - x (t - 1)) - (y (t - 1) - y (t - 2))‖ ≤
        2 * R * (1 + harmonicR (t - 1)) /
          ((t : ℝ) * (t + 1 : ℝ)) := by
    intro t ht
    have hid := firstDifference_identity horbit t ht
    have hcidentity :
        (x t - x (t - 1)) - (y (t - 1) - y (t - 2)) =
          (-1 / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2)) +
          (1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0) := by
      rw [hid]
      have ht0 : (t : ℝ) ≠ 0 := by positivity
      have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
      match_scalars
      all_goals field_simp [ht0, ht1]
      all_goals ring
    rw [hcidentity]
    calc
      ‖(-1 / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2)) +
          (1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0)‖
          ≤ ‖(-1 / (t + 1 : ℝ)) • (y (t - 1) - y (t - 2))‖ +
            ‖(1 / ((t : ℝ) * (t + 1 : ℝ))) • (y (t - 2) - x0)‖ :=
              norm_add_le _ _
      _ = (1 / (t + 1 : ℝ)) * ‖y (t - 1) - y (t - 2)‖ +
            (1 / ((t : ℝ) * (t + 1 : ℝ))) * ‖y (t - 2) - x0‖ := by
              rw [norm_smul, norm_smul]
              simp only [Real.norm_eq_abs]
              rw [abs_of_nonneg (by positivity :
                0 ≤ (1 : ℝ) / ((t : ℝ) * (t + 1 : ℝ)))]
              have ht1 : 0 < (t + 1 : ℝ) := by positivity
              rw [abs_div, abs_neg, abs_one, abs_of_pos ht1]
      _ ≤ (1 / (t + 1 : ℝ)) *
              (2 * R * harmonicR (t - 1) / (t : ℝ)) +
            (1 / ((t : ℝ) * (t + 1 : ℝ))) * (2 * R) := by
              gcongr
              · have hprev := hb (t - 1) (by omega)
                have hcast : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
                  rw [Nat.cast_sub (by omega : 1 ≤ t)]
                  push_cast
                  ring
                rw [hcast] at hprev
                simpa [Nat.sub_sub] using
                  (ha_le (t - 1) (by omega)).trans hprev
              · exact hyx0 (t - 2)
      _ = 2 * R * (1 + harmonicR (t - 1)) /
            ((t : ℝ) * (t + 1 : ℝ)) := by
              have ht0 : (t : ℝ) ≠ 0 := by positivity
              have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
              field_simp [ht0, ht1]
              ring
  have hresidual : ∀ t, 1 ≤ t →
      ‖x t - y t‖ ≤ 2 * R * (1 + harmonicR (t + 1)) / (t + 1 : ℝ) := by
    intro t ht
    have hupdate := horbit.2.2 t
    have hid :
        (t + 1 : ℝ) • (x t - y t) =
          x0 - x t - (t + 2 : ℝ) • (x (t + 1) - x t) := by
      rw [hupdate]
      have ht1 : (t : ℝ) + 1 ≠ 0 := by positivity
      have ht2 : (t : ℝ) + 2 ≠ 0 := by positivity
      match_scalars
      all_goals field_simp [ht1, ht2]
      all_goals ring
    have hx0xt : ‖x0 - x t‖ ≤ 2 * R := by
      have hsplit : x0 - x t = (x0 - zStar) + (zStar - x t) := by abel
      calc
        ‖x0 - x t‖ = ‖(x0 - zStar) + (zStar - x t)‖ := by rw [hsplit]
        _ ≤ ‖x0 - zStar‖ + ‖zStar - x t‖ := norm_add_le _ _
        _ = ‖x0 - zStar‖ + ‖x t - zStar‖ := by rw [norm_sub_rev zStar (x t)]
        _ ≤ R + R := add_le_add hR (hstay t).1
        _ = 2 * R := by ring
    have hnorm := congrArg norm hid
    rw [norm_smul] at hnorm
    simp only [Real.norm_eq_abs] at hnorm
    rw [abs_of_nonneg (by positivity : 0 ≤ (t : ℝ) + 1)] at hnorm
    have hscaled :
        (t + 1 : ℝ) * ‖x t - y t‖ ≤
          2 * R + (t + 2 : ℝ) *
          (2 * R * harmonicR (t + 1) / (t + 2 : ℝ)) := by
      rw [hnorm]
      calc
        ‖x0 - x t - (t + 2 : ℝ) • (x (t + 1) - x t)‖
            ≤ ‖x0 - x t‖ + ‖(t + 2 : ℝ) • (x (t + 1) - x t)‖ :=
              norm_sub_le _ _
        _ = ‖x0 - x t‖ + (t + 2 : ℝ) * ‖x (t + 1) - x t‖ := by
              rw [norm_smul]
              simp only [Real.norm_eq_abs]
              rw [abs_of_nonneg (by positivity : 0 ≤ (t : ℝ) + 2)]
        _ ≤ 2 * R + (t + 2 : ℝ) *
              (2 * R * harmonicR (t + 1) / (t + 2 : ℝ)) := by
              gcongr
              have hnext := hb (t + 1) (by omega)
              simp only [Nat.add_sub_cancel] at hnext
              have hden : ((t + 1 : ℕ) : ℝ) + 1 = (t : ℝ) + 2 := by
                push_cast
                ring
              rw [hden] at hnext
              exact hnext
    apply (le_div_iff₀ (by positivity : 0 < (t + 1 : ℝ))).2
    calc
      ‖x t - y t‖ * (t + 1 : ℝ) =
          (t + 1 : ℝ) * ‖x t - y t‖ := by ring
      _ ≤ 2 * R + (t + 2 : ℝ) *
          (2 * R * harmonicR (t + 1) / (t + 2 : ℝ)) := hscaled
      _ = 2 * R * (1 + harmonicR (t + 1)) := by
          have ht2 : (t : ℝ) + 2 ≠ 0 := by positivity
          field_simp [ht2]
  constructor
  · intro t ht
    exact ⟨ha_le t ht, hb t ht, hresidual t ht⟩
  · intro t ht
    exact ⟨firstDifference_identity horbit t ht, hc t ht⟩

/-- Kernel proof of `lem:second-energy`, retaining the dissipative term from
firm nonexpansiveness and telescoping it over the exact finite interval. -/
theorem secondEnergy {P : E → E} {zStar x0 : E} {x y : ℕ → E}
    {R : ℝ} (hP : FirmlyNonexpansive P) (hfix : P zStar = zStar)
    (horbit : IsHalpernOrbit P x0 x y) (hR : ‖x0 - zStar‖ ≤ R) :
    SecondEnergyConclusion y R := by
  intro k ell hk hkle hell
  have hR0 : 0 ≤ R := (norm_nonneg (x0 - zStar)).trans hR
  have hfirst := firstDifference hP hfix horbit hR
  let avec : ℕ → E := fun t => y t - y (t - 1)
  let bvec : ℕ → E := fun t => x t - x (t - 1)
  let cvec : ℕ → E := fun t => bvec t - avec (t - 1)
  let evec : ℕ → E := fun t => bvec t - avec t
  let h : ℝ := 1 + harmonicR (2 * k)
  let M : ℝ := R * h
  have hh0 : 0 ≤ h := by
    dsimp [h]
    linarith [harmonicR_nonneg (2 * k)]
  have hM0 : 0 ≤ M := mul_nonneg hR0 hh0
  have hkR : 0 < (k : ℝ) := by positivity
  have ha_uniform : ∀ t, k ≤ t → t ≤ ell →
      ‖avec (t - 1)‖ ≤ 2 * M / (k : ℝ) := by
    intro t hkt hte
    have ht2 : 2 ≤ t := hk.trans hkt
    have hraw := (hfirst.1 (t - 1) (by omega)).1.trans
      (hfirst.1 (t - 1) (by omega)).2.1
    have hden : ((t - 1 : ℕ) : ℝ) + 1 = (t : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ t)]
      push_cast
      ring
    rw [hden] at hraw
    have hHt : harmonicR (t - 1) ≤ h := by
      have hm := harmonicR_monotone (by omega : t - 1 ≤ 2 * k)
      dsimp [h]
      linarith
    calc
      ‖avec (t - 1)‖ ≤ 2 * R * harmonicR (t - 1) / (t : ℝ) := by
        simpa [avec, Nat.sub_sub] using hraw
      _ ≤ 2 * R * h / (t : ℝ) := by gcongr
      _ = 2 * M / (t : ℝ) := by simp [M]; ring
      _ ≤ 2 * M / (k : ℝ) :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hM0) hkR (by exact_mod_cast hkt)
  have hc_uniform : ∀ t, k ≤ t → t ≤ ell →
      ‖cvec t‖ ≤ 2 * M / (k : ℝ) ^ 2 := by
    intro t hkt hte
    have ht2 : 2 ≤ t := hk.trans hkt
    have hraw := (hfirst.2 t ht2).2
    have hHt : 1 + harmonicR (t - 1) ≤ h := by
      have hm := harmonicR_monotone (by omega : t - 1 ≤ 2 * k)
      dsimp [h]
      linarith
    have hden : (k : ℝ) ^ 2 ≤ (t : ℝ) * (t + 1 : ℝ) := by
      have hktR : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
      have hk0 : 0 ≤ (k : ℝ) := by positivity
      have ht0 : 0 ≤ (t : ℝ) := by positivity
      nlinarith
    have hidx : t - 1 - 1 = t - 2 := by omega
    calc
      ‖cvec t‖ ≤ 2 * R * (1 + harmonicR (t - 1)) /
          ((t : ℝ) * (t + 1 : ℝ)) := by
            simpa [cvec, bvec, avec, hidx] using hraw
      _ ≤ 2 * R * h / ((t : ℝ) * (t + 1 : ℝ)) := by gcongr
      _ = 2 * M / ((t : ℝ) * (t + 1 : ℝ)) := by simp [M]; ring
      _ ≤ 2 * M / (k : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hM0)
          (sq_pos_of_pos hkR) hden
  have hfirm : ∀ t, 1 ≤ t →
      ‖avec t‖ ^ 2 + ‖evec t‖ ^ 2 ≤ ‖bvec t‖ ^ 2 := by
    intro t ht
    have hf := hP (x t) (x (t - 1))
    have haid : P (x t) - P (x (t - 1)) = avec t := by
      simp only [avec]
      rw [← horbit.2.1 t, ← horbit.2.1 (t - 1)]
    have heid :
        ((x t - P (x t)) - (x (t - 1) - P (x (t - 1)))) = evec t := by
      simp only [evec, bvec, avec]
      rw [← horbit.2.1 t, ← horbit.2.1 (t - 1)]
      abel
    rw [haid, heid] at hf
    simpa [bvec] using hf
  have hb_decomp : ∀ t, bvec t = avec (t - 1) + cvec t := by
    intro t
    simp only [cvec]
    abel
  have hpoint : ∀ t, k ≤ t → t ≤ ell →
      ‖evec t‖ ^ 2 ≤ ‖avec (t - 1)‖ ^ 2 - ‖avec t‖ ^ 2 +
        (2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2) := by
    intro t hkt hte
    have hf := hfirm t (by omega)
    have htri : ‖bvec t‖ ≤ ‖avec (t - 1)‖ + ‖cvec t‖ := by
      rw [hb_decomp t]
      exact norm_add_le _ _
    have hsq : ‖bvec t‖ ^ 2 ≤
        (‖avec (t - 1)‖ + ‖cvec t‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
    nlinarith
  have htelescope := finite_energy_telescope
    (fun t => ‖avec t‖ ^ 2) (fun t => ‖evec t‖ ^ 2)
    (fun t => 2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2)
    hkle hpoint
  have hcard : (Finset.Icc k ell).card ≤ k := by
    rw [Nat.card_Icc]
    omega
  have hqpoint : ∀ t ∈ Finset.Icc k ell,
      2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2 ≤
        12 * M ^ 2 / (k : ℝ) ^ 3 := by
    intro t htmem
    have hkt := (Finset.mem_Icc.mp htmem).1
    have hte := (Finset.mem_Icc.mp htmem).2
    have ha := ha_uniform t hkt hte
    have hc := hc_uniform t hkt hte
    have hA0 : 0 ≤ 2 * M / (k : ℝ) := by positivity
    have hC0 : 0 ≤ 2 * M / (k : ℝ) ^ 2 := by positivity
    have hprod := mul_le_mul ha hc (norm_nonneg _) hA0
    have hcsq := (sq_le_sq₀ (norm_nonneg _) hC0).2 hc
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
    calc
      2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2
          ≤ 2 * (2 * M / (k : ℝ)) * (2 * M / (k : ℝ) ^ 2) +
            (2 * M / (k : ℝ) ^ 2) ^ 2 := by nlinarith
      _ ≤ 12 * M ^ 2 / (k : ℝ) ^ 3 := by
        field_simp [hk0]
        nlinarith [sq_nonneg M, sq_nonneg ((k : ℝ) - 1)]
  have hqsum :
      (∑ t ∈ Finset.Icc k ell,
        (2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2)) ≤
        12 * M ^ 2 / (k : ℝ) ^ 2 := by
    calc
      (∑ t ∈ Finset.Icc k ell,
          (2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2))
          ≤ ∑ _t ∈ Finset.Icc k ell, 12 * M ^ 2 / (k : ℝ) ^ 3 := by
            exact Finset.sum_le_sum hqpoint
      _ = ((Finset.Icc k ell).card : ℝ) *
          (12 * M ^ 2 / (k : ℝ) ^ 3) := by simp
      _ ≤ (k : ℝ) * (12 * M ^ 2 / (k : ℝ) ^ 3) := by
          gcongr
      _ = 12 * M ^ 2 / (k : ℝ) ^ 2 := by
          field_simp [ne_of_gt hkR]
  have ha0 := ha_uniform k le_rfl hkle
  have ha0sq : ‖avec (k - 1)‖ ^ 2 ≤ 4 * M ^ 2 / (k : ℝ) ^ 2 := by
    have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2 * M / (k : ℝ))).2 ha0
    calc
      ‖avec (k - 1)‖ ^ 2 ≤ (2 * M / (k : ℝ)) ^ 2 := hs
      _ = 4 * M ^ 2 / (k : ℝ) ^ 2 := by ring
  have hesum : (∑ t ∈ Finset.Icc k ell, ‖evec t‖ ^ 2) ≤
      16 * M ^ 2 / (k : ℝ) ^ 2 := by
    have haell0 : 0 ≤ ‖avec ell‖ ^ 2 := sq_nonneg _
    calc
      (∑ t ∈ Finset.Icc k ell, ‖evec t‖ ^ 2)
          ≤ ‖avec (k - 1)‖ ^ 2 - ‖avec ell‖ ^ 2 +
              ∑ t ∈ Finset.Icc k ell,
                (2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2) := htelescope
      _ ≤ ‖avec (k - 1)‖ ^ 2 +
              ∑ t ∈ Finset.Icc k ell,
                (2 * ‖avec (t - 1)‖ * ‖cvec t‖ + ‖cvec t‖ ^ 2) := by linarith
      _ ≤ 4 * M ^ 2 / (k : ℝ) ^ 2 + 12 * M ^ 2 / (k : ℝ) ^ 2 :=
        add_le_add ha0sq hqsum
      _ = 16 * M ^ 2 / (k : ℝ) ^ 2 := by ring
  have hcpoint_sq : ∀ t ∈ Finset.Icc k ell,
      ‖cvec t‖ ^ 2 ≤ 4 * M ^ 2 / (k : ℝ) ^ 3 := by
    intro t htmem
    have hc := hc_uniform t (Finset.mem_Icc.mp htmem).1 (Finset.mem_Icc.mp htmem).2
    have hs := (sq_le_sq₀ (norm_nonneg _)
      (by positivity : 0 ≤ 2 * M / (k : ℝ) ^ 2)).2 hc
    have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkR
    calc
      ‖cvec t‖ ^ 2 ≤ (2 * M / (k : ℝ) ^ 2) ^ 2 := hs
      _ ≤ 4 * M ^ 2 / (k : ℝ) ^ 3 := by
        have hmul := mul_le_mul_of_nonneg_left
          (show (1 : ℝ) ≤ (k : ℝ) by exact_mod_cast (show 1 ≤ k by omega))
          (sq_nonneg M)
        field_simp [hk0]
        nlinarith
  have hcsum : (∑ t ∈ Finset.Icc k ell, ‖cvec t‖ ^ 2) ≤
      4 * M ^ 2 / (k : ℝ) ^ 2 := by
    calc
      (∑ t ∈ Finset.Icc k ell, ‖cvec t‖ ^ 2)
          ≤ ∑ _t ∈ Finset.Icc k ell, 4 * M ^ 2 / (k : ℝ) ^ 3 := by
            exact Finset.sum_le_sum hcpoint_sq
      _ = ((Finset.Icc k ell).card : ℝ) *
          (4 * M ^ 2 / (k : ℝ) ^ 3) := by simp
      _ ≤ (k : ℝ) * (4 * M ^ 2 / (k : ℝ) ^ 3) := by
          gcongr
      _ = 4 * M ^ 2 / (k : ℝ) ^ 2 := by
          field_simp [ne_of_gt hkR]
  have hdpoint : ∀ t ∈ Finset.Icc k ell,
      ‖y t - (2 : ℝ) • y (t - 1) + y (t - 2)‖ ^ 2 ≤
        2 * ‖cvec t‖ ^ 2 + 2 * ‖evec t‖ ^ 2 := by
    intro t htmem
    have hidentity :
        y t - (2 : ℝ) • y (t - 1) + y (t - 2) = cvec t - evec t := by
      simp only [cvec, evec, bvec, avec]
      module
    rw [hidentity]
    have htri := norm_sub_le (cvec t) (evec t)
    have hsq := (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).2 htri
    nlinarith [sq_nonneg (‖cvec t‖ - ‖evec t‖)]
  calc
    (∑ t ∈ Finset.Icc k ell,
      ‖y t - (2 : ℝ) • y (t - 1) + y (t - 2)‖ ^ 2)
        ≤ ∑ t ∈ Finset.Icc k ell,
          (2 * ‖cvec t‖ ^ 2 + 2 * ‖evec t‖ ^ 2) :=
            Finset.sum_le_sum hdpoint
    _ = 2 * (∑ t ∈ Finset.Icc k ell, ‖cvec t‖ ^ 2) +
        2 * (∑ t ∈ Finset.Icc k ell, ‖evec t‖ ^ 2) := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.mul_sum]
    _ ≤ 2 * (4 * M ^ 2 / (k : ℝ) ^ 2) +
        2 * (16 * M ^ 2 / (k : ℝ) ^ 2) := by gcongr
    _ = 40 * M ^ 2 / (k : ℝ) ^ 2 := by ring
    _ ≤ 64 * (R ^ 2 * (1 + harmonicR (2 * k)) ^ 2) / (k : ℝ) ^ 2 := by
      dsimp [M, h]
      have hden : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
      have hnum : 0 ≤ R ^ 2 * (1 + harmonicR (2 * k)) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      gcongr
      · nlinarith
      · exact le_of_eq (by ring)

end VIReference.Pilot
