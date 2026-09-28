import Erdos993Lean.Analytic.O2.Cert.Bands.Low
import Erdos993Lean.Analytic.O2.Cert.Bands.L1
import Erdos993Lean.Analytic.O2.Cert.Bands.L23
import Erdos993Lean.Analytic.O2.Cert.Bands.L4e
import Erdos993Lean.Analytic.O2.Cert.Bands.Central0
import Erdos993Lean.Analytic.O2.Cert.Bands.Central1
import Erdos993Lean.Analytic.O2.Cert.Bands.Central2
import Erdos993Lean.Analytic.O2.Cert.Bands.Central3
import Erdos993Lean.Analytic.O2.Cert.Bands.UpperShoulder
import Erdos993Lean.Analytic.O2.Cert.Bands.H1
import Erdos993Lean.Analytic.O2.Cert.Bands.H2b
import Erdos993Lean.Analytic.O2.Cert.Bands.H3b
import Erdos993Lean.Analytic.O2.Cert.Bands.H4b
import Erdos993Lean.Analytic.O2.Cert.Bands.H8

/-!
# O2 certificates: `LocalPaymentOK` and `LeafOK` for the 14 rows (lane A18)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  For each of the 14 rows of `Erdos993Lean/Analytic/O2/Defs.lean`
(`bands`: R2's `low`, `central_0` … `central_3`, `upper_shoulder` and the gap rows `L1`, `L23`, `L4e`, `H1`, `H2b`,
`H3b`, `H4b`, `H8`), the band module `Bands/<row>.lean` proves `localPaymentOK_<row>` and `leafOK_<row>` from the
twelve root-box checks of the row; here they are collected:

* **`localPaymentOK_all : ∀ b ∈ bands, b.LocalPaymentOK`**;
* **`leafOK_all : ∀ b ∈ bands, b.LeafOK`**.

With lane A16's `O2.varianceRatioBound_profile30_of_certs` this gives `VarianceRatioBound Profile30.P`.

Trust: the soundness of the checker (`Erdos993Lean/Analytic/O2/Cert/*Sound*.lean`, `Bridge.lean`) uses only
`propext`, `Classical.choice`, `Quot.sound`; the 168 root-box checks use one `native_decide` each
(`Lean.ofReduceBool`, the Lean compiler with the natively compiled libraries `Erdos993LeanO2CertCompute` and
`Erdos993LeanTailCertCompute`).  Build by module name, one module at a time (the check modules first).
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.O2

/-- The soundness of one root-box check (the name used in the headers of `Checks/*.lean`): a passing root box
`[lo, hi] × [edges[i], edges[i+1]]` certifies every point of it (`checkRoot_sound`, `CoverSound.lean`). -/
theorem rootOK_sound {sd : Compute.SegData} (hγ : 0 ≤ (sd.gamma : ℝ)) {i : ℕ} {s : String}
    (h : Compute.rootOK sd i s = true) :
    BoxGood sd sd.lo sd.hi (Compute.edges.getD i 0) (Compute.edges.getD (i + 1) 0) :=
  checkRoot_sound hγ h

/-- **The certified local payment of the 14 O2 rows.** -/
theorem localPaymentOK_all : ∀ b ∈ bands, b.LocalPaymentOK := by
  intro b hb
  simp only [bands, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bands.localPaymentOK_low
  · exact Bands.localPaymentOK_L1
  · exact Bands.localPaymentOK_L23
  · exact Bands.localPaymentOK_L4e
  · exact Bands.localPaymentOK_central0
  · exact Bands.localPaymentOK_central1
  · exact Bands.localPaymentOK_central2
  · exact Bands.localPaymentOK_central3
  · exact Bands.localPaymentOK_upperShoulder
  · exact Bands.localPaymentOK_H1
  · exact Bands.localPaymentOK_H2b
  · exact Bands.localPaymentOK_H3b
  · exact Bands.localPaymentOK_H4b
  · exact Bands.localPaymentOK_H8

/-- **The leaf endpoint of the 14 O2 rows.** -/
theorem leafOK_all : ∀ b ∈ bands, b.LeafOK := by
  intro b hb
  simp only [bands, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Bands.leafOK_low
  · exact Bands.leafOK_L1
  · exact Bands.leafOK_L23
  · exact Bands.leafOK_L4e
  · exact Bands.leafOK_central0
  · exact Bands.leafOK_central1
  · exact Bands.leafOK_central2
  · exact Bands.leafOK_central3
  · exact Bands.leafOK_upperShoulder
  · exact Bands.leafOK_H1
  · exact Bands.leafOK_H2b
  · exact Bands.leafOK_H3b
  · exact Bands.leafOK_H4b
  · exact Bands.leafOK_H8

end Erdos993Lean.Analytic.O2.Cert
