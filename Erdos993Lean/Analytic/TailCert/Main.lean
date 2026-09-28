import Mathlib
import Erdos993Lean.Analytic.TailCert.Glue
import Erdos993Lean.Analytic.TailCert.Sound
import Erdos993Lean.Analytic.TailCert.Compute.Bands
import Erdos993Lean.Analytic.TailCert.Checks.Band00
import Erdos993Lean.Analytic.TailCert.Checks.Band01
import Erdos993Lean.Analytic.TailCert.Checks.Band02
import Erdos993Lean.Analytic.TailCert.Checks.Band03
import Erdos993Lean.Analytic.TailCert.Checks.Band04
import Erdos993Lean.Analytic.TailCert.Checks.Band05
import Erdos993Lean.Analytic.TailCert.Checks.Band06
import Erdos993Lean.Analytic.TailCert.Checks.Band07
import Erdos993Lean.Analytic.TailCert.Checks.Band08
import Erdos993Lean.Analytic.TailCert.Checks.Band09
import Erdos993Lean.Analytic.TailCert.Checks.Band10
import Erdos993Lean.Analytic.TailCert.Checks.Band11
import Erdos993Lean.Analytic.TailCert.Checks.Band12
import Erdos993Lean.Analytic.TailCert.Checks.Band13
import Erdos993Lean.Analytic.TailCert.Checks.Band14
import Erdos993Lean.Analytic.TailCert.Checks.Band15
import Erdos993Lean.Analytic.TailCert.Checks.Band16
import Erdos993Lean.Analytic.TailCert.Checks.Band17
import Erdos993Lean.Analytic.TailCert.Checks.Band18
import Erdos993Lean.Analytic.TailCert.Checks.Band19
import Erdos993Lean.Analytic.TailCert.Checks.Band20
import Erdos993Lean.Analytic.TailCert.Checks.Band21
import Erdos993Lean.Analytic.TailCert.Checks.Band22
import Erdos993Lean.Analytic.TailCert.Checks.Band23
import Erdos993Lean.Analytic.TailCert.Checks.Band24
import Erdos993Lean.Analytic.TailCert.Checks.Band25
import Erdos993Lean.Analytic.TailCert.Checks.Band26
import Erdos993Lean.Analytic.TailCert.Checks.Band27
import Erdos993Lean.Analytic.TailCert.Checks.Band28
import Erdos993Lean.Analytic.TailCert.Checks.Band29

/-!
# O3 for the certified profile: `TailBound Profile30.P` (lane A10, optional target)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Sources: `SOUL/O3/repaired_potential_proof.md`
(the repaired T3 potential), `SOUL/O3/certify_repaired_potential.py` (Soul's adaptive cover),
`SOUL/O3/repaired_band_XX_t_Y.json` (the certified `a` and `ℓ`), lane A3's Theorem T3-2 (repaired)
`Tail.tail_t3`.

**Theorems.**
* `bandCert_of_checkIJ`: a passing check `checkIJ i j = true` gives `BandCert i j`
  (`checkBand_sound`, standard axioms, and the equality of the data copies `edgesC_eq`, `tvalsC_eq`,
  `ratesC_eq`, `aTabC_eq`);
* **`bandCertificates : BandCertificates`** (the 30 band checks `Checks.band_00` … `band_29`);
* **`tailBound_profile30 : TailBound Profile30.P`** (O3 for the certified profile), from
  `tailBound_profile30_of_certificates` (`TailCert/Glue.lean`, standard axioms).

**Trust.**  `native_decide` is used exactly 30 times, once in each of
`Erdos993Lean/Analytic/TailCert/Checks/Band00.lean` … `Band29.lean`:
`Checks.band_XX : Compute.checkRow XX = true` (the five Laplace parameters of band `XX`).  They trust the
Lean compiler (`Lean.ofReduceBool`), here including the natively compiled code of the library
`Erdos993LeanTailCertCompute` (`precompileModules = true`) and the C compiler used by Lake.  The checker
and its data are plain structural recursion in Lean core (no `partial`, `unsafe`, `implemented_by`,
`extern`); the soundness proof (`Erdos993Lean/Analytic/TailCert/Sound.lean` and its imports) and the glue
use only `propext`, `Classical.choice`, `Quot.sound`.

**Build.**  `lake build Erdos993LeanTailCert` (not part of the default target; see the header of each
check module).
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute

theorem edgesC_eq : edgesC = Profile30.edges := by decide +kernel

theorem tvalsC_eq : tvalsC = Profile30.tvals := by decide +kernel

theorem ratesC_eq : ratesC = Profile30.rates := by decide +kernel

theorem aTabC_eq : aTabC = aTab := by decide +kernel

/-- A passing check of band `i` at the Laplace parameter `t_j` gives its certificate. -/
theorem bandCert_of_checkIJ {i j : ℕ} (h : checkIJ i j = true) : BandCert i j := by
  unfold checkIJ at h
  rw [edgesC_eq, tvalsC_eq, ratesC_eq, aTabC_eq] at h
  exact checkBand_sound h

/-- The five checks of band `i` give its five certificates. -/
theorem bandCerts_of_checkRow {i : ℕ} (h : checkRow i = true) : ∀ j < 5, BandCert i j := by
  simp only [checkRow, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  intro j hj
  interval_cases j
  exacts [bandCert_of_checkIJ h0, bandCert_of_checkIJ h1, bandCert_of_checkIJ h2,
    bandCert_of_checkIJ h3, bandCert_of_checkIJ h4]

/-- **The band certificates of the repaired T3 potential**: `Tail.T3UNonneg λ t_j a(i, j) ℓ(i, j)` on
each of the 30 bands for the five Laplace parameters (the 30 `native_decide` checks
`Checks.band_XX`). -/
theorem bandCertificates : BandCertificates := by
  intro i hi
  interval_cases i
  exacts [
    bandCerts_of_checkRow Checks.band_00,
    bandCerts_of_checkRow Checks.band_01,
    bandCerts_of_checkRow Checks.band_02,
    bandCerts_of_checkRow Checks.band_03,
    bandCerts_of_checkRow Checks.band_04,
    bandCerts_of_checkRow Checks.band_05,
    bandCerts_of_checkRow Checks.band_06,
    bandCerts_of_checkRow Checks.band_07,
    bandCerts_of_checkRow Checks.band_08,
    bandCerts_of_checkRow Checks.band_09,
    bandCerts_of_checkRow Checks.band_10,
    bandCerts_of_checkRow Checks.band_11,
    bandCerts_of_checkRow Checks.band_12,
    bandCerts_of_checkRow Checks.band_13,
    bandCerts_of_checkRow Checks.band_14,
    bandCerts_of_checkRow Checks.band_15,
    bandCerts_of_checkRow Checks.band_16,
    bandCerts_of_checkRow Checks.band_17,
    bandCerts_of_checkRow Checks.band_18,
    bandCerts_of_checkRow Checks.band_19,
    bandCerts_of_checkRow Checks.band_20,
    bandCerts_of_checkRow Checks.band_21,
    bandCerts_of_checkRow Checks.band_22,
    bandCerts_of_checkRow Checks.band_23,
    bandCerts_of_checkRow Checks.band_24,
    bandCerts_of_checkRow Checks.band_25,
    bandCerts_of_checkRow Checks.band_26,
    bandCerts_of_checkRow Checks.band_27,
    bandCerts_of_checkRow Checks.band_28,
    bandCerts_of_checkRow Checks.band_29]

/-- **O3 for the certified profile**: `P(M ≤ M') ≤ T(λ, m, M')` for every forest with at least 61
vertices, every activity in range at an interior rank and every maximum-weight independent set,
with the profile's tail function `T = Profile30.tailFn`. -/
theorem tailBound_profile30 : TailBound Profile30.P :=
  tailBound_profile30_of_certificates bandCertificates

end Erdos993Lean.Analytic.TailCert
