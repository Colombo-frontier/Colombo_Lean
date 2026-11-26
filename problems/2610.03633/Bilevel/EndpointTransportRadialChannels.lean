import Bilevel.EndpointTransportRadialSpace
import Bilevel.EndpointTransportPayloadBudgets
import Bilevel.ChiExtensionRadialSum

/-! The J public normal channels: levels 1 through J-1 are ordinary,
and the final channel is the whole physical block with its exact gamma scaling. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiCarrier RadialWrapper EndpointTransportMatrix ChiExtension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def publicRadialProjection {J : ℕ} (n D : ℕ) (i : Fin J) :
    PhysicalBase E J n D →L[ℝ] HybridTangent (Blocks J (Block D)) n D :=
  if h : i.val+1<J then ordinaryRadialProjection ⟨i.val+1,h⟩ else physicalRadialProjection J n D

def publicRadialCurvature {J : ℕ} (n : ℕ) (ρ : ℕ → ℝ) (i : Fin J) : ℝ :=
  if i.val+1<J then ρ (i.val+1) else ρ (i.val+1)/gamma n^2

def publicRadialRadius {J : ℕ} (n : ℕ) (R : ℕ → ℝ) (i : Fin J) : ℝ :=
  if i.val+1<J then R (i.val+1) else gamma n*R (i.val+1)

theorem publicRadialProjection_norm_le {J : ℕ} (n D : ℕ) (i : Fin J) :
    ‖publicRadialProjection (E:=E) n D i‖≤1 := by
  unfold publicRadialProjection
  split_ifs with h
  · exact ordinaryRadialProjection_norm_le ⟨i.val+1,h⟩
  · exact physicalRadialProjection_norm_le J n D

theorem publicRadialRadius_pos {J : ℕ} (n : ℕ) (R : ℕ → ℝ)
    (hR : ∀ i : Fin J,0<R (i.val+1)) (i : Fin J) : 0<publicRadialRadius n R i := by
  unfold publicRadialRadius
  split_ifs
  · exact hR i
  · exact mul_pos (gamma_positive n) (hR i)

theorem publicRadialCurvature_nonneg {J : ℕ} (n : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ i : Fin J,0≤ρ (i.val+1)) (i : Fin J) : 0≤publicRadialCurvature n ρ i := by
  unfold publicRadialCurvature
  split_ifs
  · exact hρ i
  · exact div_nonneg (hρ i) (sq_nonneg _)

theorem publicRadialCurvature_le {J : ℕ} (n : ℕ) (ρ : ℕ → ℝ)
    (hρ : ∀ i : Fin J,0≤ρ (i.val+1)) (i : Fin J) : publicRadialCurvature n ρ i≤ρ (i.val+1) := by
  unfold publicRadialCurvature
  split_ifs
  · exact le_rfl
  · exact div_le_self (hρ i) (by nlinarith only [(gamma_range n).1])

theorem publicRadial_product_le {J : ℕ} (n : ℕ) (ρ R : ℕ → ℝ)
    (hρ : ∀ i : Fin J,0≤ρ (i.val+1)) (hR : ∀ i : Fin J,0≤R (i.val+1)) (i : Fin J) :
    publicRadialCurvature n ρ i*publicRadialRadius n R i≤ρ (i.val+1)*R (i.val+1) := by
  unfold publicRadialCurvature publicRadialRadius
  split_ifs
  · exact le_rfl
  · have hg := (gamma_positive n).ne'
    have he : (ρ (i.val+1)/gamma n^2)*(gamma n*R (i.val+1))=
        (ρ (i.val+1)*R (i.val+1))/gamma n := by field_simp;ring
    rw [he]
    exact div_le_self (mul_nonneg (hρ i) (hR i)) (gamma_range n).1

theorem physical_public_channel_sum {n D : ℕ} (ρ R : ℕ → ℝ) (j : ℕ)
    (z : PhysicalBase E (j+1) n D) :
    bowl (ρ 0) (R 0) (block (j+1) 0 z.snd.fst)+
      (∑ i : Fin (j+1),bowl (publicRadialCurvature n ρ i) (publicRadialRadius n R i)
        (publicRadialProjection n D i z))=
      physicalPublic ρ R (j+1) 0 (padded z.snd.fst) z.snd.snd := by
  rw [physicalPublic_sum,Fin.sum_univ_castSucc (fun i : Fin (j+1) =>
      bowl (publicRadialCurvature n ρ i) (publicRadialRadius n R i) (publicRadialProjection n D i z)),
    Fin.sum_univ_succ (fun i : Fin (j+1) => bowl (ρ (0+i.val)) (R (0+i.val)) (padded z.snd.fst (0+i.val)))]
  have hi (i : Fin j) : i.castSucc.val+1<j+1 := by change i.val+1<j+1;omega
  have hiv (i : Fin j) : i.val+1<j+1 := by omega
  have hc (i : Fin j) : i.castSucc.val=i.val := rfl
  have hl : ¬(Fin.last j).val+1<j+1 := by simp only [Fin.val_last];omega
  simp only [publicRadialCurvature,publicRadialRadius,publicRadialProjection,hi,hl,if_true,if_false,
    dite_true,dite_false,ordinary_radial_bowl,physical_radial_bowl,Fin.val_last,Fin.val_zero,
    Fin.val_succ,hc,Nat.zero_add,padded,Nat.lt_irrefl,hiv]
  have he : (∑ i : Fin j,bowl (ρ (i.val+1)) (R (i.val+1)) (z.snd.fst ⟨i.val+1,hi i⟩))=
      ∑ i : Fin j,bowl (ρ (i.val+1)) (R (i.val+1)) (block (j+1) (i.val+1) z.snd.fst) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [block,dif_pos (hiv i),PiLp.proj_apply]
  rw [he]
  ring

theorem physical_radial_sum_jets {J s : ℕ} (n D : ℕ) (index : Fin J → Fin s)
    (ρ R : ℕ → ℝ) (d : ℝ) (hρ : ∀ i : Fin J,0≤ρ (i.val+1))
    (hR : ∀ i : Fin J,0<R (i.val+1)) (hd : 0<d) (z : Full (PhysicalBase E J n D) s) :
    ‖iteratedFDeriv ℝ 2 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤∑ i : Fin J,3*(ρ (i.val+1)*R (i.val+1)/d) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
      (publicRadialCurvature n ρ) (publicRadialRadius n R) d) z‖≤∑ i : Fin J,9*ρ (i.val+1)/d := by
  have hb := radialSum_jets index (publicRadialProjection n D) (publicRadialProjection_norm_le n D)
    (publicRadialCurvature n ρ) (publicRadialRadius n R) d
    (publicRadialCurvature_nonneg n ρ hρ) (publicRadialRadius_pos n R hR) hd z
  constructor
  · apply hb.1.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
      (publicRadial_product_le n ρ R hρ (fun i => (hR i).le) i) hd.le) (by norm_num)
  · apply hb.2.trans (Finset.sum_le_sum (fun i _ => ?_))
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (publicRadialCurvature_le n ρ hρ i) (by norm_num)) hd.le

end Bilevel.EndpointTransportResponse
