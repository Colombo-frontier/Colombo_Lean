import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

/-! # Explicit canonical prefix/tail coordinates in Euclidean space -/

noncomputable section

namespace NCConcave16991.MixedHaar

open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 700000

def canonicalHead (r d : ℕ) (x : EuclideanSpace ℝ (Fin (r + d))) : EuclideanSpace ℝ (Fin r) :=
  WithLp.toLp 2 (fun i ↦ x (Fin.castAdd d i))

def canonicalTail (r d : ℕ) (x : EuclideanSpace ℝ (Fin (r + d))) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i ↦ x (Fin.natAdd r i))

def canonicalJoin (r d : ℕ) (u : EuclideanSpace ℝ (Fin r)) (v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (r + d)) := WithLp.toLp 2 (Fin.append (WithLp.ofLp u) (WithLp.ofLp v))

@[simp] theorem canonicalHead_join (r d : ℕ) (u : EuclideanSpace ℝ (Fin r))
    (v : EuclideanSpace ℝ (Fin d)) : canonicalHead r d (canonicalJoin r d u v) = u := by
  ext i
  simp only [canonicalHead,canonicalJoin,PiLp.toLp_apply,Fin.append_left]

@[simp] theorem canonicalTail_join (r d : ℕ) (u : EuclideanSpace ℝ (Fin r))
    (v : EuclideanSpace ℝ (Fin d)) : canonicalTail r d (canonicalJoin r d u v) = v := by
  ext i
  simp only [canonicalTail,canonicalJoin,PiLp.toLp_apply,Fin.append_right]

@[simp] theorem canonicalJoin_split (r d : ℕ) (x : EuclideanSpace ℝ (Fin (r + d))) :
    canonicalJoin r d (canonicalHead r d x) (canonicalTail r d x) = x := by
  ext i
  refine Fin.addCases (fun a ↦ ?_) (fun b ↦ ?_) i
  · simp only [canonicalJoin,canonicalHead,PiLp.toLp_apply,Fin.append_left]
  · simp only [canonicalJoin,canonicalTail,PiLp.toLp_apply,Fin.append_right]

theorem canonicalJoin_norm_sq (r d : ℕ) (u : EuclideanSpace ℝ (Fin r))
    (v : EuclideanSpace ℝ (Fin d)) : ‖canonicalJoin r d u v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2,Fin.sum_univ_add]
  simp only [canonicalJoin,PiLp.toLp_apply,Fin.append_left,Fin.append_right]

theorem canonicalSplit_norm_sq (r d : ℕ) (x : EuclideanSpace ℝ (Fin (r + d))) :
    ‖x‖ ^ 2 = ‖canonicalHead r d x‖ ^ 2 + ‖canonicalTail r d x‖ ^ 2 := by
  simpa only [canonicalJoin_split] using canonicalJoin_norm_sq r d (canonicalHead r d x) (canonicalTail r d x)

theorem canonicalJoin_inner (r d : ℕ) (u u' : EuclideanSpace ℝ (Fin r))
    (v v' : EuclideanSpace ℝ (Fin d)) :
    ⟪canonicalJoin r d u v,canonicalJoin r d u' v'⟫_ℝ = ⟪u,u'⟫_ℝ + ⟪v,v'⟫_ℝ := by
  rw [PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,Fin.sum_univ_add]
  simp only [canonicalJoin,PiLp.toLp_apply,Fin.append_left,Fin.append_right]

def canonicalSplitEquiv (r d : ℕ) : EuclideanSpace ℝ (Fin (r + d)) ≃ₗ[ℝ]
    EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin d) where
  toFun x := (canonicalHead r d x,canonicalTail r d x)
  invFun p := canonicalJoin r d p.1 p.2
  left_inv := canonicalJoin_split r d
  right_inv p := by simp only [canonicalHead_join,canonicalTail_join]
  map_add' x y := by ext <;> rfl
  map_smul' a x := by ext <;> rfl

def canonicalBlock (r d : ℕ) (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (r + d)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (r + d)) where
  toLinearEquiv := (canonicalSplitEquiv r d).trans
    (((LinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin r))).prodCongr U.toLinearEquiv).trans
      (canonicalSplitEquiv r d).symm)
  norm_map' x := by
    change ‖canonicalJoin r d (canonicalHead r d x) (U (canonicalTail r d x))‖ = ‖x‖
    have hh := canonicalJoin_norm_sq r d (canonicalHead r d x) (U (canonicalTail r d x))
    rw [U.norm_map] at hh
    have hs := canonicalSplit_norm_sq r d x
    nlinarith [norm_nonneg (canonicalJoin r d (canonicalHead r d x) (U (canonicalTail r d x))),norm_nonneg x]

@[simp] theorem canonicalBlock_apply (r d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin (r + d))) :
    canonicalBlock r d U x = canonicalJoin r d (canonicalHead r d x) (U (canonicalTail r d x)) := rfl

@[simp] theorem canonicalBlock_join (r d : ℕ)
    (U : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d))
    (u : EuclideanSpace ℝ (Fin r)) (v : EuclideanSpace ℝ (Fin d)) :
    canonicalBlock r d U (canonicalJoin r d u v) = canonicalJoin r d u (U v) := by
  simp only [canonicalBlock_apply,canonicalHead_join,canonicalTail_join]

end NCConcave16991.MixedHaar
