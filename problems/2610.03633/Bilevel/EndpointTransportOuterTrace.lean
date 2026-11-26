import Bilevel.EndpointTransportPayload
import Bilevel.ChiOuterAttachment

/-! Exact trace of the full macro/recursive objective, including all public
radial penalties. Every equality is valid for arbitrary ambient variables. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiOuter RadialWrapper

def physicalPublic {n D : ℕ} (ρ R : ℕ → ℝ) :
    ℕ → ℕ → (ℕ → Block D) → Physical n D → ℝ
  | 0,j,_u,Y => bowl (ρ j/gamma n^2) (gamma n*R j) Y
  | d+1,j,u,Y => bowl (ρ j) (R j) (u j)+physicalPublic ρ R d (j+1) u Y

theorem physical_public_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (ρ R : ℕ → ℝ) (d j : ℕ) (u : ℕ → Block D) (v : Block D)
    (hlast : u (j+d)=gain n δ c • v) :
    physicalPublic ρ R d j u (physicalResponse δ c Q v)=publicValue ρ R d j u := by
  induction d generalizing j with
  | zero =>
    simp only [Nat.add_zero] at hlast
    simp only [physicalPublic,publicValue,response_exact_bowl,hlast]
  | succ d ih =>
    simp only [physicalPublic,publicValue]
    rw [ih (j+1) (by rw [show j+1+d=j+(d+1) by omega]; exact hlast)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def physicalOuter {n D : ℕ} (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (d : ℕ) (x : E)
    (u : ℕ → Block D) (Y : Physical n D) : ℝ :=
  attachment M ν
    (fun i => if d=0 then physicalRelease Q (G 0 [i.val]) Y else (G 0 [i.val]).release (u 0))
    (fun i => physicalRecursive Q G d 0 [i.val] u Y) x+physicalPublic ρ R d 0 u Y

theorem physical_outer_response {n D : ℕ} (δ c : ℝ) (Q : Rotations n D)
    (M : Node E) (ν : ℝ) (G : Geometry (Block D)) (ρ R : ℕ → ℝ) (d : ℕ)
    (x : E) (u : ℕ → Block D) (v : Block D) (hlast : u d=gain n δ c • v) :
    physicalOuter Q M ν G ρ R d x u (physicalResponse δ c Q v)=outerObjective M ν G ρ R d x u := by
  have hl : u (0+d)=gain n δ c • v := by simpa only [Nat.zero_add] using hlast
  have hr (i : Fin (M.n+1)) :
      (if d=0 then physicalRelease Q (G 0 [i.val]) (physicalResponse δ c Q v)
        else (G 0 [i.val]).release (u 0))=(G 0 [i.val]).release (u 0) := by
    by_cases hd : d=0
    · subst d
      rw [if_pos rfl,physical_release_response,hlast]
    · rw [if_neg hd]
  simp only [physicalOuter,outerObjective,hr,
    physical_recursive_response δ c Q G d 0 _ u v hl,
    physical_public_response δ c Q ρ R d 0 u v hl]

end Bilevel.EndpointTransportResponse
