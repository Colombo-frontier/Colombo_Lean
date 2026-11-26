import Bilevel.ChiCarrierFinePieceLocality
import Bilevel.ChiCarrierSignalLedger

/-! Prefix support of the actual fixed inactive fine atoms, after every
ancestor selector. The last atom alone is changed, at the globally fixed
resolution; no query-dependent potential is introduced. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def jointInactivePiece (m j : ℕ) (D : Node E) (c θ τ : ℝ) (p : ℕ) (x : Blocks m E) : ℝ :=
  jointFinePiece m j D c θ p x-if p=levels θ then jointFineSignal m j D τ x else 0

theorem jointInactivePiece_contDiff (m j : ℕ) (D : Node E) (c θ τ : ℝ) (p : ℕ) :
    ContDiff ℝ 3 (jointInactivePiece m j D c θ τ p) := by
  unfold jointInactivePiece
  by_cases hp : p=levels θ
  · simpa only [if_pos hp] using (jointFinePiece_contDiff m j D c θ p).sub
      (jointFineSignal_contDiff m j D τ)
  · simpa only [if_neg hp,sub_zero] using jointFinePiece_contDiff m j D c θ p

def selectedInactivePiece (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ τ : ℝ) (p : ℕ) : Blocks m E → ℝ :=
  selectFamily m D (fun k P => jointInactivePiece m k (D k P) c θ τ p) d j I

theorem selectedInactivePiece_contDiff (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ τ : ℝ) (p : ℕ) : ContDiff ℝ 3 (selectedInactivePiece m D d j I c θ τ p) :=
  selectFamily_contDiff m D _ (fun k P => jointInactivePiece_contDiff m k (D k P) c θ τ p) d j I

theorem selectedInactivePiece_eq (m : ℕ) (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (c θ τ : ℝ) (p : ℕ) (x : Blocks m E) :
    selectedInactivePiece m D d j I c θ τ p x=selectedFinePiece m D d j I c θ p x-
      if p=levels θ then selectedFineSignal m D d j I τ x else 0 := by
  by_cases hp : p=levels θ
  · have he : (fun k P => jointInactivePiece m k (D k P) c θ τ p)=
        (fun k P y => jointFinePiece m k (D k P) c θ p y-jointFineSignal m k (D k P) τ y) := by
      funext k P y
      simp only [jointInactivePiece,if_pos hp]
    rw [selectedInactivePiece,he,if_pos hp]
    exact selectFamily_sub m D _ _ d j I x
  · have he : (fun k P => jointInactivePiece m k (D k P) c θ τ p)=
        (fun k P => jointFinePiece m k (D k P) c θ p) := by
      funext k P y
      simp only [jointInactivePiece,if_neg hp,sub_zero]
    rw [selectedInactivePiece,he,if_neg hp,sub_zero]
    rfl

theorem jointInactivePiece_gradient_mem {m : ℕ} (W : Fin m → Submodule ℝ E) (x : Blocks m E)
    (j : Fin m) (D : Node E) (c θ τ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : 0≤D.ell) (hh : 0<D.width) (hR : 0<D.radius)
    (hτ : τ=width c D.width θ (levels θ)/8) (p r : ℕ) (hp : p≤levels θ)
    (hu : x j∈W j)
    (hU : ∀ k : Fin (D.n+1),k.val < r → D.frame (basis k)∈W j)
    (hz : ∀ k : Fin (D.n+1),r ≤ k.val → |D.coordinates (x j) k|≤τ) :
    gradient (jointInactivePiece m j.val D c θ τ p) x∈knownSpace W := by
  let P : ChiFine.Parameters := ⟨D.ell,D.width,θ,c,hell,hh,hθ,hc,hcs⟩
  have he : jointInactivePiece m j.val D c θ τ p=
      ((P.inactivePiece D.n p ∘ D.coordinates) ∘ block m j.val) := by
    funext y
    rw [hτ]
    rfl
  rw [he]
  apply block_composition_gradient_mem W x j
    ((P.inactivePiece_contDiff D.n p).comp (D.coordinates_contDiff 3))
  apply WrappedPrefixLocality.carried_gradient_mem D.n r D.radius hR D.frame _
    ((P.inactivePiece_contDiff D.n p).differentiable (by norm_num)) (x j) (W j) hu hU
  intro k hk
  apply P.inactivePiece_gradient_support D.n p r hp _ _ k hk
  intro a ha
  simpa only [hτ] using hz a ha

theorem selectedInactivePiece_gradient_mem {m : ℕ} (D : Geometry E) (d j : ℕ) (I : List ℕ)
    (hm : j+d < m) (W : Fin m → Submodule ℝ E) (x : Blocks m E) (r : ℕ → List ℕ → ℕ)
    (hblind : ∀ k P (_hk : j ≤ k) (hkt : k < j+d),
      BlindNode W x ⟨k,by omega⟩ (D k P) (r k P))
    (c θ τ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell) (hh : ∀ P,0<(D (j+d) P).width)
    (hR : ∀ P,0<(D (j+d) P).radius)
    (hτ : ∀ P,τ=width c (D (j+d) P).width θ (levels θ)/8)
    (hu : x ⟨j+d,hm⟩∈W ⟨j+d,hm⟩)
    (hU : ∀ P,∀ k : Fin ((D (j+d) P).n+1),k.val < r (j+d) P →
      (D (j+d) P).frame (basis k)∈W ⟨j+d,hm⟩)
    (hz : ∀ P,∀ k : Fin ((D (j+d) P).n+1),r (j+d) P ≤ k.val →
      |(D (j+d) P).coordinates (x ⟨j+d,hm⟩) k|≤τ)
    (p : ℕ) (hp : p≤levels θ) :
    gradient (selectedInactivePiece m D d j I c θ τ p) x∈knownSpace W := by
  apply selectFamily_gradient_mem_of_blind D _
    (fun k P => jointInactivePiece_contDiff m k (D k P) c θ τ p) d j I hm W x r hblind
  intro P
  exact jointInactivePiece_gradient_mem W x ⟨j+d,hm⟩ (D (j+d) P) c θ τ hc hcs hθ
    (hell P) (hh P) (hR P) (hτ P) p (r (j+d) P) hp hu (hU P) (hz P)

end Bilevel.ChiCarrier
