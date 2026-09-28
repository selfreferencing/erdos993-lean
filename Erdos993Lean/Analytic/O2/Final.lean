import Erdos993Lean.Analytic.O2.Main
import Erdos993Lean.Analytic.O2.Small

/-!
# O2 for the certified profile from the certificates alone

Campaign `ProofRuns/2026-09-28_analytic_large_n` (lane A16).  Source: `PRO_R2_PROOF.md` Theorem 4,
§7 (the small-message boundary, proved in `Small.lean` for all 14 bands), and the band
propositions of `Defs.lean`.

* `smallMessageOK_bands`: `SmallMessageOK` for the 14 bands (their §7 guards are kernel-checked);
* **`varianceRatioBound_profile30_of_certs`**: `VarianceRatioBound Profile30.P` from the two
  certificate propositions of the 14 bands — the certified local payment on the cover
  `xmin·q ≤ p < q` (`LocalPaymentOK`) and the leaf endpoint `p = q, z = 1` (`LeafOK`), both of which
  the band certificates verify (lane A18).

Scalarity check.  No new scalar: `θ(λ) = γ − 1` is the output price of the band containing `λ`.
-/

namespace Erdos993Lean.Analytic.O2

/-- **The small-message boundary for the 14 rows.** -/
theorem smallMessageOK_bands : ∀ b ∈ bands, b.SmallMessageOK := by
  intro b hb
  simp only [bands, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact BandData.smallMessageOK_of_guards guards_low smallGuards_low
  · exact BandData.smallMessageOK_of_guards guards_L1 smallGuards_L1
  · exact BandData.smallMessageOK_of_guards guards_L23 smallGuards_L23
  · exact BandData.smallMessageOK_of_guards guards_L4e smallGuards_L4e
  · exact BandData.smallMessageOK_of_guards guards_central0 smallGuards_central0
  · exact BandData.smallMessageOK_of_guards guards_central1 smallGuards_central1
  · exact BandData.smallMessageOK_of_guards guards_central2 smallGuards_central2
  · exact BandData.smallMessageOK_of_guards guards_central3 smallGuards_central3
  · exact BandData.smallMessageOK_of_guards guards_upperShoulder smallGuards_upperShoulder
  · exact BandData.smallMessageOK_of_guards guards_H1 smallGuards_H1
  · exact BandData.smallMessageOK_of_guards guards_H2b smallGuards_H2b
  · exact BandData.smallMessageOK_of_guards guards_H3b smallGuards_H3b
  · exact BandData.smallMessageOK_of_guards guards_H4b smallGuards_H4b
  · exact BandData.smallMessageOK_of_guards guards_H8 smallGuards_H8

/-- **O2 for the certified profile from the certificates alone**: `VarianceRatioBound Profile30.P`
from the certified local payment and the leaf endpoint of the 14 O2 bands. -/
theorem varianceRatioBound_profile30_of_certs (hpay : ∀ b ∈ bands, b.LocalPaymentOK)
    (hleaf : ∀ b ∈ bands, b.LeafOK) : VarianceRatioBound Profile30.P :=
  varianceRatioBound_profile30_of_ok hpay hleaf smallMessageOK_bands

end Erdos993Lean.Analytic.O2
