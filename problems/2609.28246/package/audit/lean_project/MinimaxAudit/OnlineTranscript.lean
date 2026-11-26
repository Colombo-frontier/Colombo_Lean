import MinimaxAudit.Deterministic

/-!
# Explicit causal deterministic scalar transcript certificate

The static final-frame consequence is accompanied by the actual one-step
online statement. New columns and the scalar answer are chosen from the old
prefix, history, and current query *before* every quantifier over future
completions. At least one such completion exists, and every completion gives
the same complete scalar jet. The older static terminal is not modified.
-/
open Set
open scoped RealInnerProductSpace
namespace MinimaxAudit.OnlineTranscript
open Deterministic
noncomputable section
set_option maxHeartbeats 1000000

variable {p dx dy N : ℕ}

/-- One real online resisting-oracle step. The existential answer is an
explicit function of only the selected prefix and the current query. Future
frames are universally quantified after this answer, and their nonemptiness
is proved, so consistency is not a vacuous implication. -/
theorem online_step
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy)
    (t : ℕ) (htN : t < N)
    (h : ScalarHistory p dx dy) (hlen : h.length ≤ t)
    (u : Fin t → Primal dx) (v : Fin t → Dual dy)
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v)
    (z : SaddleSpace dx dy) :
    ∃ (u' : Fin (t + 1) → Primal dx) (v' : Fin (t + 1) → Dual dy)
      (answer : ScalarJet p (SaddleSpace dx dy)),
      Orthonormal ℝ u' ∧ Orthonormal ℝ v' ∧
      (∀ i : Fin t, u' (Fin.castAdd 1 i) = u i) ∧
      (∀ i : Fin t, v' (Fin.castAdd 1 i) = v i) ∧
      (∀ entry ∈ h ++ [(z, answer)],
        inner ℝ (u' (Fin.last t)) (primalBlock entry.1) = 0 ∧
        inner ℝ (v' (Fin.last t)) (dualBlock entry.1) = 0) ∧
      answer = exactScalarJet p (truncatedPotential profile tau lam c q t
        (prefixPad N t (Nat.le_of_lt htN) u')
        (prefixPad N t (Nat.le_of_lt htN) v')) z ∧
      (∃ U V, FrameExtension N (t + 1) u' v' (h ++ [(z, answer)]) U V) ∧
      (∀ U V, FrameExtension N (t + 1) u' v' (h ++ [(z, answer)]) U V →
        FrameExtension N t u v h U V ∧
        answer = exactScalarJet p (hardPotential profile tau lam c q U V) z) := by
  let qx : List (Primal dx) :=
    List.ofFn u ++ (h.map (fun e => primalBlock e.1) ++ [primalBlock z])
  let qy : List (Dual dy) :=
    List.ofFn v ++ (h.map (fun e => dualBlock e.1) ++ [dualBlock z])
  have hcx : qx.length < Module.finrank ℝ (Primal dx) := by
    have hd : 2 * N + 2 ≤ Module.finrank ℝ (Primal dx) := by simpa [Primal] using hdx
    simp only [qx, List.length_append, List.length_ofFn, List.length_map,
      List.length_singleton]
    omega
  have hcy : qy.length < Module.finrank ℝ (Dual dy) := by
    have hd : 2 * N + 2 ≤ Module.finrank ℝ (Dual dy) := by simpa [Dual] using hdy
    simp only [qy, List.length_append, List.length_ofFn, List.length_map,
      List.length_singleton]
    omega
  obtain ⟨wx, hwx, hox⟩ := Frame.exists_unit_orthogonal_list qx hcx
  obtain ⟨wy, hwy, hoy⟩ := Frame.exists_unit_orthogonal_list qy hcy
  have hwxu : ∀ i, inner ℝ wx (u i) = 0 := fun i => hox (u i) (by simp [qx])
  have hwyv : ∀ i, inner ℝ wy (v i) = 0 := fun i => hoy (v i) (by simp [qy])
  let u' : Fin (t + 1) → Primal dx := Fin.append u (fun _ : Fin 1 => wx)
  let v' : Fin (t + 1) → Dual dy := Fin.append v (fun _ : Fin 1 => wy)
  have hu' : Orthonormal ℝ u' := orthonormal_fin_snoc u wx hu hwx hwxu
  have hv' : Orthonormal ℝ v' := orthonormal_fin_snoc v wy hv hwy hwyv
  have hlastx : u' (Fin.last t) = wx := by
    change Fin.append u (fun _ : Fin 1 => wx) (Fin.last t) = wx
    rw [show Fin.last t = Fin.natAdd t (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
  have hlasty : v' (Fin.last t) = wy := by
    change Fin.append v (fun _ : Fin 1 => wy) (Fin.last t) = wy
    rw [show Fin.last t = Fin.natAdd t (0 : Fin 1) from Fin.ext rfl, Fin.append_right]
  let fakeU := prefixPad N t (Nat.le_of_lt htN) u'
  let fakeV := prefixPad N t (Nat.le_of_lt htN) v'
  let answer := exactScalarJet p (truncatedPotential profile tau lam c q t fakeU fakeV) z
  have hnew : ∀ entry ∈ h ++ [(z, answer)],
      inner ℝ (u' (Fin.last t)) (primalBlock entry.1) = 0 ∧
      inner ℝ (v' (Fin.last t)) (dualBlock entry.1) = 0 := by
    intro entry he
    rw [hlastx, hlasty]
    constructor
    · apply hox
      apply List.mem_append_right
      have hm : primalBlock entry.1 ∈ (h ++ [(z, answer)]).map (fun e => primalBlock e.1) :=
        List.mem_map_of_mem he
      simpa only [List.map_append, List.map_cons, List.map_nil] using hm
    · apply hoy
      apply List.mem_append_right
      have hm : dualBlock entry.1 ∈ (h ++ [(z, answer)]).map (fun e => dualBlock e.1) :=
        List.mem_map_of_mem he
      simpa only [List.map_append, List.map_cons, List.map_nil] using hm
  have hlen' : (h ++ [(z, answer)]).length ≤ t + 1 := by
    simp only [List.length_append, List.length_singleton]
    omega
  obtain ⟨U0, V0, hext0, _⟩ := complete_pair_at_output N (t + 1) (by omega)
    u' v' hu' hv' (h ++ [(z, answer)]) hlen' (0 : SaddleSpace dx dy) hdx hdy
  refine ⟨u', v', answer, hu', hv', ?_, ?_, hnew, rfl, ⟨U0, V0, hext0⟩, ?_⟩
  · intro i
    exact Fin.append_left _ _ i
  · intro i
    exact Fin.append_left _ _ i
  · intro U V hext
    have hUt : ∀ i : Fin (N + 1), i.1 = t → U i = u' (Fin.last t) := by
      intro i hi
      exact hext.primal_prefix i (Fin.last t) (by simpa using hi)
    have hVt : ∀ i : Fin (N + 1), i.1 = t → V i = v' (Fin.last t) := by
      intro i hi
      exact hext.dual_prefix i (Fin.last t) (by simpa using hi)
    have hcurrent : ∀ i : Fin (N + 1), t ≤ i.1 →
        inner ℝ (U i) (primalBlock z) = 0 ∧ inner ℝ (V i) (dualBlock z) = 0 := by
      intro i hi
      by_cases hieq : i.1 = t
      · rw [hUt i hieq, hVt i hieq]
        exact hnew (z, answer) (by simp)
      · exact hext.future_queries i (by omega) (z, answer) (by simp)
    have hfakeU : ∀ i : Fin (t + 1),
        fakeU (Fin.castLE (by omega) i) = U (Fin.castLE (by omega) i) := by
      intro i
      rw [show fakeU (Fin.castLE (by omega) i) = u' i from
        prefixPad_prefix N t (Nat.le_of_lt htN) u' i]
      exact (hext.primal_prefix _ i rfl).symm
    have hfakeV : ∀ i : Fin (t + 1),
        fakeV (Fin.castLE (by omega) i) = V (Fin.castLE (by omega) i) := by
      intro i
      rw [show fakeV (Fin.castLE (by omega) i) = v' i from
        prefixPad_prefix N t (Nat.le_of_lt htN) v' i]
      exact (hext.dual_prefix _ i rfl).symm
    have htrunc := truncatedPotential_congr_prefix profile tau lam c q t (Nat.le_of_lt htN)
      fakeU U fakeV V hfakeU hfakeV
    have hfull := exactJet_full_eq_truncated_of_future_orthogonal
      profile htau lam c q p t (Nat.le_of_lt htN) U V z hcurrent
    constructor
    · refine ⟨hext.primal_orthonormal, hext.dual_orthonormal, ?_, ?_, ?_⟩
      · intro i j hij
        have hp := hext.primal_prefix i (Fin.castAdd 1 j) (by simpa using hij)
        simpa [u'] using hp
      · intro i j hij
        have hp := hext.dual_prefix i (Fin.castAdd 1 j) (by simpa using hij)
        simpa [v'] using hp
      · intro i hi entry he
        by_cases hieq : i.1 = t
        · rw [hUt i hieq, hVt i hieq]
          exact hnew entry (List.mem_append_left _ he)
        · exact hext.future_queries i (by omega) entry (List.mem_append_left _ he)
    · dsimp only [answer]
      rw [htrunc]
      exact hfull.symm

/-- Source-facing exact deterministic transcript proposition. In addition
to final zero coordinates, this explicitly certifies every possible online
round with its causal existential/universal quantifier order. -/
theorem deterministic_transcript_source
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    {X : Set (Primal dx)} {Y : Set (Dual dy)}
    (A : DeterministicScalarPolicy p dx dy N X Y)
    (hdx : 2 * N + 2 ≤ dx) (hdy : 2 * N + 2 ≤ dy) :
    (∃ (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy),
      Orthonormal ℝ U ∧ Orthonormal ℝ V ∧
      let output := runScalarPolicy A
        (exactScalarJet p (hardPotential profile tau lam c q U V)) N []
      plusForm U V (Fin.last N) output = 0 ∧ minusForm U V (Fin.last N) output = 0) ∧
    (∀ (t : ℕ) (ht : t < N), ∀ h : ScalarHistory p dx dy, h.length ≤ t →
      ∀ (u : Fin t → Primal dx) (v : Fin t → Dual dy),
      Orthonormal ℝ u → Orthonormal ℝ v → ∀ z : SaddleSpace dx dy,
      ∃ (u' : Fin (t + 1) → Primal dx) (v' : Fin (t + 1) → Dual dy)
        (answer : ScalarJet p (SaddleSpace dx dy)),
        Orthonormal ℝ u' ∧ Orthonormal ℝ v' ∧
        (∀ i : Fin t, u' (Fin.castAdd 1 i) = u i) ∧
        (∀ i : Fin t, v' (Fin.castAdd 1 i) = v i) ∧
        (∀ entry ∈ h ++ [(z, answer)],
          inner ℝ (u' (Fin.last t)) (primalBlock entry.1) = 0 ∧
          inner ℝ (v' (Fin.last t)) (dualBlock entry.1) = 0) ∧
        answer = exactScalarJet p (truncatedPotential profile tau lam c q t
          (prefixPad N t (Nat.le_of_lt ht) u')
          (prefixPad N t (Nat.le_of_lt ht) v')) z ∧
        (∃ U V, FrameExtension N (t + 1) u' v' (h ++ [(z, answer)]) U V) ∧
        (∀ U V, FrameExtension N (t + 1) u' v' (h ++ [(z, answer)]) U V →
          FrameExtension N t u v h U V ∧
          answer = exactScalarJet p (hardPotential profile tau lam c q U V) z)) ∧
    (∀ (t : ℕ), t ≤ N → ∀ h : ScalarHistory p dx dy, h.length ≤ t →
      ∀ (u : Fin t → Primal dx) (v : Fin t → Dual dy),
      Orthonormal ℝ u → Orthonormal ℝ v → ∀ output : SaddleSpace dx dy,
      ∃ U V, FrameExtension N t u v h U V ∧ OutputHidden U V output) := by
  refine ⟨exists_paired_resisting_zero_coordinates profile htau lam c q A hdx hdy, ?_, ?_⟩
  · intro t ht h hlen u v hu hv z
    exact online_step profile htau lam c q hdx hdy t ht h hlen u v hu hv z
  · intro t ht h hlen u v hu hv output
    exact complete_pair_at_output N t ht u v hu hv h hlen output hdx hdy

end
end MinimaxAudit.OnlineTranscript
