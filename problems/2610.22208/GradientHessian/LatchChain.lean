import GradientHessian.LatchActivation
import GradientHessian.EuclideanRegisters

/-! The literal scaled latch chain on the Euclidean direct sum of registers.
The recursive sum lists registers in the same order as the manuscript. -/

noncomputable section
namespace GradientHessian.LatchChain

open scoped InnerProductSpace
open EuclideanRegisters LatchActivation Profiles IntegralProfiles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def u (r : ℝ) (v x : E) : ℝ := readout v (r⁻¹ • x)

def atom (a r : ℝ) (v x : E) : ℝ :=
  8 * r * ((1 / 2) * ‖r⁻¹ • x‖ ^ 2 -
    (chi (u r v x) + (1 - chi (u r v x)) * a) * ell₀ (u r v x))

def incoming (r : ℝ) (v x : E) : ℝ :=
  8 * r * (1 - chi (u r v x)) * ell₀ (u r v x)

def self : (n : ℕ) → (Fin (n + 1) → E) → (Fin (n + 1) → ℝ) →
    ℝ → Registers E (n + 1) → ℝ
  | 0, v, r, a, U => atom a (r 0) (v 0) (U 0)
  | n + 1, v, r, a, U => atom a (r 0) (v 0) (U 0) +
      self n (fun i => v i.succ) (fun i => r i.succ)
        (chi (u (r 0) (v 0) (U 0))) (tail E (n + 1) U)

def port (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (U : Registers E (n + 1)) : ℝ := varpi (u (r (Fin.last n)) (v (Fin.last n)) (U (Fin.last n)))

def driven (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ) (l : ℝ)
    (U : Registers E (n + 1)) : ℝ := self n v r 1 U - l * port n v r U

theorem self_input_affine (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (a : ℝ) (U : Registers E (n + 1)) :
    self n v r a U = self n v r 0 U - a * incoming (r 0) (v 0) (U 0) := by
  cases n <;> simp only [self, atom, incoming] <;> ring

theorem driven_eq_source (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (l : ℝ) (U : Registers E (n + 1)) :
    driven n v r l U = self n v r 0 U - incoming (r 0) (v 0) (U 0) - l * port n v r U := by
  rw [driven, self_input_affine]
  ring

theorem self_succ (n : ℕ) (v : Fin (n + 2) → E) (r : Fin (n + 2) → ℝ)
    (a : ℝ) (U : Registers E (n + 2)) :
    self (n + 1) v r a U = atom a (r 0) (v 0) (U 0) +
      self n (fun i => v i.succ) (fun i => r i.succ) 0 (tail E (n + 1) U) -
      chi (u (r 0) (v 0) (U 0)) * incoming (r 1) (v 1) (U 1) := by
  rw [self, self_input_affine]
  simp only [tail_apply, Fin.succ_zero_eq_one]
  ring

/-- The recursive potential is exactly the source's first term plus the sum
of adjacent-register self terms. -/
theorem self_eq_adjacent_sum (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (a : ℝ) (U : Registers E (n + 1)) :
    self n v r a U = atom a (r 0) (v 0) (U 0) +
      ∑ i : Fin n, atom (chi (u (r i.castSucc) (v i.castSucc) (U i.castSucc)))
        (r i.succ) (v i.succ) (U i.succ) := by
  induction n generalizing a with
  | zero => simp [self]
  | succ n ih =>
    rw [self, ih, Fin.sum_univ_succ]
    have hidx : ∀ i : Fin n, i.castSucc.succ = i.succ.castSucc := by intro i; rfl
    simp only [tail_apply, Fin.castSucc_zero, Fin.succ_zero_eq_one, hidx]
    rfl

theorem incoming_nonneg {r : ℝ} (hr : 0 ≤ r) (v x : E) : 0 ≤ incoming r v x := by
  unfold incoming
  apply mul_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) hr) (sub_nonneg.mpr (chi_bounds _).2)
  · have h := (ell₀_bounds (u r v x)).1
    linarith

theorem u_contDiff (r : ℝ) (v : E) : ContDiff ℝ 3 (u r v) := by
  unfold u readout
  exact (innerSL ℝ v).contDiff.comp
    (((RadialSquash.squash_contDiff (by norm_num : (0 : ℝ) < 8)).of_le
      (by decide : (3 : WithTop ℕ∞) ≤ 4)).comp (contDiff_const.smul contDiff_id))

theorem atom_contDiff (a r : ℝ) (v : E) : ContDiff ℝ 3 (atom a r v) := by
  have hu := u_contDiff r v
  have hc := contDiff_chi.comp hu
  have he := (ell₀_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)).comp hu
  exact contDiff_const.mul ((contDiff_const.mul ((contDiff_const.smul contDiff_id).norm_sq ℝ)).sub
    ((hc.add ((contDiff_const.sub hc).mul contDiff_const)).mul he))

theorem incoming_contDiff (r : ℝ) (v : E) : ContDiff ℝ 3 (incoming r v) := by
  have hu := u_contDiff r v
  exact (contDiff_const.mul (contDiff_const.sub (contDiff_chi.comp hu))).mul
    ((ell₀_contDiff.of_le (by decide : (3 : WithTop ℕ∞) ≤ 4)).comp hu)

theorem self_contDiff (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ) (a : ℝ) :
    ContDiff ℝ 3 (self n v r a) := by
  induction n generalizing a with
  | zero => exact (atom_contDiff a (r 0) (v 0)).comp (head E 0).contDiff
  | succ n ih =>
    have he : self (n + 1) v r a = fun U => atom a (r 0) (v 0) (U 0) +
        self n (fun i => v i.succ) (fun i => r i.succ) 0 (tail E (n + 1) U) -
        chi (u (r 0) (v 0) (U 0)) * incoming (r 1) (v 1) (U 1) :=
      funext (self_succ n v r a)
    rw [he]
    exact (((atom_contDiff a (r 0) (v 0)).comp (head E (n + 1)).contDiff).add
      ((ih _ _ 0).comp (tail E (n + 1)).contDiff)).sub
      (((contDiff_chi.comp (u_contDiff (r 0) (v 0))).comp (head E (n + 1)).contDiff).mul
        ((incoming_contDiff (r 1) (v 1)).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 2) => E) 1).contDiff))

theorem port_contDiff (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ) :
    ContDiff ℝ 3 (port n v r) :=
  (contDiff_varpi.comp (u_contDiff (r (Fin.last n)) (v (Fin.last n)))).comp
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (n + 1) => E) (Fin.last n)).contDiff

theorem driven_contDiff (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ) (l : ℝ) :
    ContDiff ℝ 3 (driven n v r l) :=
  (self_contDiff n v r 1).sub (contDiff_const.mul (port_contDiff n v r))

theorem port_succ (n : ℕ) (v : Fin (n + 2) → E) (r : Fin (n + 2) → ℝ)
    (U : Registers E (n + 2)) :
    port (n + 1) v r U = port n (fun i => v i.succ) (fun i => r i.succ) (tail E (n + 1) U) := rfl

theorem driven_single_slice (v : Fin 1 → E) (r : Fin 1 → ℝ) (hr : r 0 ≠ 0)
    (l : ℝ) (V : Registers E 0) (x : E) :
    driven 0 v r l (join E x V) = r 0 * potential (v 0) 0 (l / r 0) ((r 0)⁻¹ • x) := by
  simp [driven, self, atom, port, u, potential, Fin.last_zero]
  field_simp
  ring

theorem driven_head_slice (n : ℕ) (v : Fin (n + 2) → E) (r : Fin (n + 2) → ℝ)
    (hr : r 0 ≠ 0) (l : ℝ) (V : Registers E (n + 1)) (x : E) :
    driven (n + 1) v r l (join E x V) =
      r 0 * potential (v 0) (incoming (r 1) (v 1) (V 0) / r 0) 0 ((r 0)⁻¹ • x) +
        (self n (fun i => v i.succ) (fun i => r i.succ) 0 V -
          l * port n (fun i => v i.succ) (fun i => r i.succ) V) := by
  rw [driven, self_succ, port_succ]
  simp only [join_zero, join_succ, tail_join]
  rw [show join E x V 1 = V 0 from join_succ E x V 0]
  simp only [atom, potential, u]
  field_simp
  ring

theorem driven_tail_slice (n : ℕ) (v : Fin (n + 2) → E) (r : Fin (n + 2) → ℝ)
    (l : ℝ) (x : E) (hx : chi (u (r 0) (v 0) x) = 1) (V : Registers E (n + 1)) :
    driven (n + 1) v r l (join E x V) = atom 1 (r 0) (v 0) x +
      driven n (fun i => v i.succ) (fun i => r i.succ) l V := by
  rw [driven, self, port_succ]
  simp only [join_zero, tail_join, hx, driven]
  ring

variable [CompleteSpace E]

theorem scaled_potential_hasGradientAt {r : ℝ} (hr : r ≠ 0) (v x : E) (d l : ℝ) :
    HasGradientAt (fun y => r * potential v d l (r⁻¹ • y))
      (force v d l (r⁻¹ • x)) x := by
  have h := ((potential_hasGradientAt v (r⁻¹ • x) d l).hasFDerivAt.comp x
    (((r⁻¹) • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := x))).const_mul r
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h using 1
  ext w
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, InnerProductSpace.toDual_apply, smul_eq_mul,
    real_inner_smul_right]
  field_simp

theorem add_constant_hasGradientAt {f : E → ℝ} {g x : E}
    (h : HasGradientAt f g x) (c : ℝ) : HasGradientAt (fun y => f y + c) g x :=
  h.hasFDerivAt.add_const c

theorem const_add_hasGradientAt {f : E → ℝ} {g x : E}
    (h : HasGradientAt f g x) (c : ℝ) : HasGradientAt (fun y => c + f y) g x :=
  h.hasFDerivAt.const_add c

/-- Every register in the actual scaled Euclidean chain activates. Positivity
of scales suffices; the source's geometric scale schedule is a special case. -/
theorem driven_activation (n : ℕ) (v : Fin (n + 1) → E) (r : Fin (n + 1) → ℝ)
    (hv : ∀ i, ‖v i‖ = 1) (hr : ∀ i, 0 < r i) {l : ℝ} (hl : 0 ≤ l)
    (U : Registers E (n + 1)) (hg : ‖gradient (driven n v r l) U‖ ≤ 1) :
    (∀ i, 7 / 8 ≤ u (r i) (v i) (U i)) ∧ port n v r U = 1 := by
  induction n with
  | zero =>
    have hslice := (head_slice_gradient_norm_le 0 (driven 0 v r l) U
      ((driven_contDiff 0 v r l).differentiable (by norm_num) U)).trans hg
    have he : (fun x => driven 0 v r l (join E x (tail E 0 U))) =
        (fun x => r 0 * potential (v 0) 0 (l / r 0) ((r 0)⁻¹ • x)) :=
      funext (driven_single_slice v r (hr 0).ne' l (tail E 0 U))
    rw [he, (scaled_potential_hasGradientAt (hr 0).ne' (v 0) (U 0) 0 (l / r 0)).gradient] at hslice
    have h := force_activation (v 0) ((r 0)⁻¹ • U 0) (hv 0) (by norm_num)
      (div_nonneg hl (hr 0).le) hslice
    refine ⟨?_, ?_⟩
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact h.1
    · simpa only [port, u, Fin.last_zero] using h.2
  | succ n ih =>
    have hslice := (head_slice_gradient_norm_le (n + 1) (driven (n + 1) v r l) U
      ((driven_contDiff (n + 1) v r l).differentiable (by norm_num) U)).trans hg
    let V := tail E (n + 1) U
    let d := incoming (r 1) (v 1) (V 0) / r 0
    let c := self n (fun i => v i.succ) (fun i => r i.succ) 0 V -
      l * port n (fun i => v i.succ) (fun i => r i.succ) V
    have he : (fun x => driven (n + 1) v r l (join E x V)) =
        (fun x => r 0 * potential (v 0) d 0 ((r 0)⁻¹ • x) + c) :=
      funext (driven_head_slice n v r (hr 0).ne' l V)
    change ‖gradient (fun x => driven (n + 1) v r l (join E x V)) (U 0)‖ ≤ 1 at hslice
    rw [he, (add_constant_hasGradientAt
      (scaled_potential_hasGradientAt (hr 0).ne' (v 0) (U 0) d 0) c).gradient] at hslice
    have hd : 0 ≤ d := div_nonneg (incoming_nonneg (hr 1).le _ _) (hr 0).le
    have hhead := (force_activation (v 0) ((r 0)⁻¹ • U 0) (hv 0) hd (by norm_num) hslice).1
    have ha : chi (u (r 0) (v 0) (U 0)) = 1 := chi_one (by exact le_trans (by norm_num) hhead)
    have htail := (tail_slice_gradient_norm_le (n + 1) (driven (n + 1) v r l) U
      ((driven_contDiff (n + 1) v r l).differentiable (by norm_num) U)).trans hg
    have ht : (fun X => driven (n + 1) v r l (join E (U 0) X)) =
        (fun X => atom 1 (r 0) (v 0) (U 0) +
          driven n (fun i => v i.succ) (fun i => r i.succ) l X) :=
      funext (driven_tail_slice n v r l (U 0) ha)
    rw [ht] at htail
    have htgrad := ((driven_contDiff n (fun i => v i.succ) (fun i => r i.succ) l).differentiable
      (by norm_num) V).hasGradientAt
    rw [(const_add_hasGradientAt htgrad (atom 1 (r 0) (v 0) (U 0))).gradient] at htail
    obtain ⟨hall, hport⟩ := ih (fun i => v i.succ) (fun i => r i.succ)
      (fun i => hv i.succ) (fun i => hr i.succ) V htail
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hhead
      · exact hall j
    · rw [port_succ]
      exact hport

def sourceScale {k : ℕ} (s : ℝ) (i : Fin k) : ℝ := s * (2 : ℝ) ^ i.val

theorem sourceScale_pos {k : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin k) : 0 < sourceScale s i := by
  exact mul_pos hs (pow_pos (by norm_num) _)

/-- Source activation with at least two registers, first scale at least one,
the exact geometric scale schedule, and the actual scalar `V - B - λ π`. -/
theorem source_activation (n : ℕ) (v : Fin (n + 2) → E) {s l : ℝ}
    (hs : 1 ≤ s) (hl : 0 ≤ l) (hv : ∀ i, ‖v i‖ = 1) (U : Registers E (n + 2))
    (hg : ‖gradient (fun X => self (n + 1) v (sourceScale s) 0 X -
      incoming s (v 0) (X 0) - l * port (n + 1) v (sourceScale s) X) U‖ ≤ 1) :
    (∀ i, 7 / 8 ≤ u (sourceScale s i) (v i) (U i)) ∧
      port (n + 1) v (sourceScale s) U = 1 := by
  have hr : ∀ i : Fin (n + 2), 0 < sourceScale s i := sourceScale_pos (by linarith)
  have he : (fun X => self (n + 1) v (sourceScale s) 0 X -
      incoming s (v 0) (X 0) - l * port (n + 1) v (sourceScale s) X) =
      driven (n + 1) v (sourceScale s) l := by
    funext X
    rw [driven_eq_source]
    simp [sourceScale]
  rw [he] at hg
  exact driven_activation (n + 1) v (sourceScale s) hv hr hl U hg

end GradientHessian.LatchChain
