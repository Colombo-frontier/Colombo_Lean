import GradientHessian.LeafFullOracle

/-! Joint C3 regularity in raw marked coefficients and physical coordinates.
No unit-vector, certificate, or bounded-parameter premise is required. -/

noncomputable section
namespace GradientHessian.JointMarkedCalculus
open InnerCoordinates EuclideanRegisters
open scoped InnerProductSpace

variable {F Y E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem readout_contDiff (r : ℝ) {v z : F → E} (hv : ContDiff ℝ 3 v) (hz : ContDiff ℝ 3 z) :
    ContDiff ℝ 3 (fun x => LatchChain.u r (v x) (z x)) :=
  hv.inner ℝ (((RadialSquash.squash_contDiff (by norm_num : (0:ℝ) < 8)).of_le
    (by decide : (3:WithTop ℕ∞) ≤ 4)).comp (contDiff_const.smul hz))

theorem atom_contDiff (r : ℝ) {a : F → ℝ} {v z : F → E}
    (ha : ContDiff ℝ 3 a) (hv : ContDiff ℝ 3 v) (hz : ContDiff ℝ 3 z) :
    ContDiff ℝ 3 (fun x => LatchChain.atom (a x) r (v x) (z x)) := by
  have hu := readout_contDiff r hv hz
  have hc := Profiles.contDiff_chi.comp hu
  have he := (IntegralProfiles.ell₀_contDiff.of_le (by decide : (3:WithTop ℕ∞) ≤ 4)).comp hu
  exact contDiff_const.mul ((contDiff_const.mul ((contDiff_const.smul hz).norm_sq ℝ)).sub
    ((hc.add ((contDiff_const.sub hc).mul ha)).mul he))

theorem incoming_contDiff (r : ℝ) {v z : F → E} (hv : ContDiff ℝ 3 v) (hz : ContDiff ℝ 3 z) :
    ContDiff ℝ 3 (fun x => LatchChain.incoming r (v x) (z x)) := by
  have hu := readout_contDiff r hv hz
  exact (contDiff_const.mul (contDiff_const.sub (Profiles.contDiff_chi.comp hu))).mul
    ((IntegralProfiles.ell₀_contDiff.of_le (by decide : (3:WithTop ℕ∞) ≤ 4)).comp hu)

theorem self_contDiff (n : ℕ) (r : Fin (n+1) → ℝ) {a : F → ℝ}
    {v : F → Fin (n+1) → E} {U : F → Registers E (n+1)} (ha : ContDiff ℝ 3 a)
    (hv : ∀ j, ContDiff ℝ 3 (fun x => v x j)) (hU : ContDiff ℝ 3 U) :
    ContDiff ℝ 3 (fun x => LatchChain.self n (v x) r (a x) (U x)) := by
  have hz (j : Fin (n+1)) : ContDiff ℝ 3 (fun x => U x j) :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n+1) => E) j).contDiff.comp hU
  have he : (fun x => LatchChain.self n (v x) r (a x) (U x)) =
      fun x => LatchChain.atom (a x) (r 0) (v x 0) (U x 0) +
        ∑ j : Fin n, LatchChain.atom (Profiles.chi (LatchChain.u (r j.castSucc) (v x j.castSucc) (U x j.castSucc)))
          (r j.succ) (v x j.succ) (U x j.succ) := by
    funext x
    exact LatchChain.self_eq_adjacent_sum n (v x) r (a x) (U x)
  rw [he]
  exact (atom_contDiff (r 0) ha (hv 0) (hz 0)).add (ContDiff.sum (fun j _ =>
    atom_contDiff (r j.succ)
      (Profiles.contDiff_chi.comp (readout_contDiff (r j.castSucc) (hv j.castSucc) (hz j.castSucc)))
      (hv j.succ) (hz j.succ)))

theorem forcing_contDiff {b y : F → Y} (hb : ContDiff ℝ 3 b) (hy : ContDiff ℝ 3 y) :
    ContDiff ℝ 3 (fun x => InverseGate.forcing (b x) (y x)) :=
  contDiff_const.mul (contDiff_const.add
    ((IntegralProfiles.theta_contDiff.of_le (by decide : (3:WithTop ℕ∞) ≤ 4)).comp
      ((hb.inner ℝ hy).div_const _)))

theorem gate_contDiff {a y : F → Y} (ha : ContDiff ℝ 3 a) (hy : ContDiff ℝ 3 y) :
    ContDiff ℝ 3 (fun x => InverseGate.gate (a x) (y x)) :=
  Profiles.contDiff_chi.comp ((ha.inner ℝ
    (((RadialSquash.squash_contDiff InverseGate.B₀_pos).of_le
      (by decide : (3:WithTop ℕ∞) ≤ 4)).comp hy)).div_const _)

variable {m k : ℕ} {Z : F → InnerCoordinates.Space Y E m (k+2)}

theorem coordinate_contDiff (hZ : ContDiff ℝ 3 Z) (i : Fin m) (j : Fin (k+2)) :
    ContDiff ℝ 3 (fun x => tasks Y E m (k+2) (Z x) i j) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+2) => E) j).contDiff.comp
    ((Inner.taskProjection (Y := Y) (E := E) m k i).contDiff.comp hZ)

theorem ports_contDiff {v : F → Fin m → Fin (k+2) → E}
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) (i : Fin m) :
    ContDiff ℝ 3 (fun x => Inner.ports (v x) (Z x) i) :=
  Profiles.contDiff_varpi.comp (readout_contDiff _ (hv i _) (coordinate_contDiff hZ i _))

theorem payload_contDiff {b a : F → Fin m → Y} {v : F → Fin m → Fin (k+2) → E}
    (hb : ∀ i, ContDiff ℝ 3 (fun x => b x i)) (ha : ∀ i, ContDiff ℝ 3 (fun x => a x i))
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) (i : Fin m) :
    ContDiff ℝ 3 (fun x => Inner.payload (b x) (a x) (v x) (Z x) i) := by
  have hy := (numerical Y E m (k+2)).contDiff.comp hZ
  exact (forcing_contDiff (hb i) hy).add
    ((incoming_contDiff 1 (hv i 0) (coordinate_contDiff hZ i 0)).mul (gate_contDiff (ha i) hy))

theorem forcingSum_contDiff {b a : F → Fin m → Y} {v : F → Fin m → Fin (k+2) → E}
    (hb : ∀ i, ContDiff ℝ 3 (fun x => b x i)) (ha : ∀ i, ContDiff ℝ 3 (fun x => a x i))
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) :
    ContDiff ℝ 3 (fun x => Inner.forcingSum (b x) (a x) (v x) (Z x)) :=
  InnerSelector.select_contDiff m _ _ (ports_contDiff hv hZ) (payload_contDiff hb ha hv hZ)

theorem selfSum_contDiff {v : F → Fin m → Fin (k+2) → E}
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) :
    ContDiff ℝ 3 (fun x => Inner.selfSum (v x) (Z x)) :=
  ContDiff.sum (fun i _ => self_contDiff (k+1) (Inner.radius k) contDiff_const (hv i)
    ((Inner.taskProjection (Y := Y) (E := E) m k i).contDiff.comp hZ))

theorem residual_contDiff {b a : F → Fin m → Y} {v : F → Fin m → Fin (k+2) → E}
    (hb : ∀ i, ContDiff ℝ 3 (fun x => b x i)) (ha : ∀ i, ContDiff ℝ 3 (fun x => a x i))
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) :
    ContDiff ℝ 3 (fun x => Inner.residual (b x) (a x) (v x) (Z x)) :=
  ((selfSum_contDiff hv hZ).sub ((Inner.publicQuadratic_contDiff m k).comp hZ)).sub
    (forcingSum_contDiff hb ha hv hZ)

theorem knownTerm_contDiff {b a : F → Fin m → Y} {v : F → Fin m → Fin (Inner.absoluteDepth+2) → E}
    {Z : F → Leaf.Space Y E m}
    (hb : ∀ i, ContDiff ℝ 3 (fun x => b x i)) (ha : ∀ i, ContDiff ℝ 3 (fun x => a x i))
    (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j)) (hZ : ContDiff ℝ 3 Z) :
    ContDiff ℝ 3 (fun x => Leaf.knownTerm (b x) (a x) (v x) (Z x)) :=
  ((Inner.publicQuadratic_contDiff m Inner.absoluteDepth).comp hZ).add (residual_contDiff hb ha hv hZ)

theorem objective_contDiff {A : F → Y →L[ℝ] Y} {b a : F → Fin m → Y}
    {v : F → Fin m → Fin (Inner.absoluteDepth+2) → E} {Z : F → Leaf.Space Y E m} (hm : 1 ≤ m)
    (hA : ContDiff ℝ 3 A) (hb : ∀ i, ContDiff ℝ 3 (fun x => b x i))
    (ha : ∀ i, ContDiff ℝ 3 (fun x => a x i)) (hv : ∀ i j, ContDiff ℝ 3 (fun x => v x i j))
    (hZ : ContDiff ℝ 3 Z) : ContDiff ℝ 3 (fun x => Leaf.objective (A x) (b x) (a x) (v x) (Z x)) := by
  have hy := (numerical Y E m (Inner.absoluteDepth+2)).contDiff.comp hZ
  have hquad := hy.inner ℝ ((hA.clm_apply hy).sub
    ((contDiff_const : ContDiff ℝ 3 (fun _ : F => 2*(m:ℝ))).smul hy))
  have hcap := (LeafCutoff.cutoff_contDiff (Leaf.capRadius_pos hm)).comp hy
  exact ((Leaf.publicQuadratic_contDiff m).comp hZ).add
    (((contDiff_const.mul hcap).mul hquad).add (residual_contDiff hb ha hv hZ))

end GradientHessian.JointMarkedCalculus
