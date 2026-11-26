import FullJet.SnapshotJet

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

/-- Read the first derivative from the already returned value-inclusive packet. -/
noncomputable def packetGradient (hp : 1 ≤ p) (J : JetPacket p E) : E →L[ℝ] ℝ :=
  continuousMultilinearCurryFin1 ℝ E ℝ (J ⟨1, Nat.lt_succ_of_le hp⟩)

theorem packetGradient_fullJet (hp : 1 ≤ p) (f : E → ℝ) (x : E) :
    packetGradient hp (fullJet p f x) = fderiv ℝ f x := by
  ext v
  simp only [packetGradient, fullJet, continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
  simp only [Fin.snoc_zero]

theorem packetGradient_add (hp : 1 ≤ p) (J K : JetPacket p E) :
    packetGradient hp (J + K) = packetGradient hp J + packetGradient hp K := by
  simp only [packetGradient, Pi.add_apply, map_add]

theorem packetGradient_sub (hp : 1 ≤ p) (J K : JetPacket p E) :
    packetGradient hp (J - K) = packetGradient hp J - packetGradient hp K := by
  simp only [packetGradient, Pi.sub_apply, map_sub]

theorem norm_packetGradient_sub (hp : 1 ≤ p) (J K : JetPacket p E) :
    ‖packetGradient hp J - packetGradient hp K‖ =
      ‖J ⟨1, Nat.lt_succ_of_le hp⟩ - K ⟨1, Nat.lt_succ_of_le hp⟩‖ := by
  rw [← packetGradient_sub]
  exact (continuousMultilinearCurryFin1 ℝ E ℝ).norm_map _

/-- Replace only the first derivative by the recursively estimated gradient. -/
noncomputable def replacePacketGradient (hp : 1 ≤ p) (J : JetPacket p E)
    (g : E →L[ℝ] ℝ) : JetPacket p E :=
  Function.update J ⟨1, Nat.lt_succ_of_le hp⟩ ((continuousMultilinearCurryFin1 ℝ E ℝ).symm g)

@[simp] theorem packetGradient_replace (hp : 1 ≤ p) (J : JetPacket p E) (g : E →L[ℝ] ℝ) :
    packetGradient hp (replacePacketGradient hp J g) = g := by
  simp [packetGradient, replacePacketGradient]

theorem replacePacketGradient_other (hp : 1 ≤ p) (J : JetPacket p E) (g : E →L[ℝ] ℝ)
    (j : Fin (p + 1)) (hj : j.val ≠ 1) : replacePacketGradient hp J g j = J j := by
  apply Function.update_of_ne
  intro h
  exact hj (congrArg Fin.val h)

theorem replacePacketGradient_first_error (hp : 1 ≤ p) (J : JetPacket p E)
    (g : E →L[ℝ] ℝ) (f : E → ℝ) (x : E) :
    ‖fullJet p f x ⟨1, Nat.lt_succ_of_le hp⟩ -
      replacePacketGradient hp J g ⟨1, Nat.lt_succ_of_le hp⟩‖ =
      ‖fderiv ℝ f x - g‖ := by
  rw [← norm_packetGradient_sub hp, packetGradient_fullJet, packetGradient_replace]

end FullJet
