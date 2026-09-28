import Mathlib
import Erdos993Lean.Analytic.O2.Cert.KernelSound
import Erdos993Lean.Analytic.O2.Cert.Compute.Engine
import Erdos993Lean.Analytic.O2.Knots

/-!
# O2 certificate checker (lane A18): the packed child masses

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  The checker's context
(`Erdos993Lean/Analytic/O2/Cert/Compute/Engine.lean`, `packing`) encloses the packed child masses of
`Erdos993Lean/Analytic/O2/Defs.lean` (`PRO_R2_PROOF.md` (7)–(8)):
`packH = min_j (jλ + A/(1+λ)ʲ − 1)` and `packPhi = max_j (jq + 1 − (1+λ)ʲ/A)`, `A = λ(1−p)/p` (`packH_eq`,
`packH_le`, `packPhi_eq`, `le_packPhi`, from `j = ⌊T/L⌋₊`: `packJ_facts`), so the checker's hulls over the possible
`j` enclose them (**`de_packing`**, with the loops `jLow_spec`, `jHigh_spec`).

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2

/-! ## The packed child masses as a minimum/maximum over `j` -/

/-- `f_j = jλ + A/(1+λ)ʲ − 1`. -/
noncomputable def fH (l A : ℝ) (j : ℕ) : ℝ := j * l + A / (1 + l) ^ j - 1

/-- `g_j = jq + 1 − (1+λ)ʲ/A`. -/
noncomputable def gP (l A : ℝ) (j : ℕ) : ℝ := j * actQ l + 1 - (1 + l) ^ j / A

theorem fH_succ (l A : ℝ) (hl : 0 < l) (k : ℕ) :
    fH l A (k + 1) - fH l A k = l * (1 - A / (1 + l) ^ (k + 1)) := by
  unfold fH
  have h1 : (0 : ℝ) < 1 + l := by linarith
  have h2 : (1 + l) ^ (k + 1) = (1 + l) ^ k * (1 + l) := pow_succ _ _
  rw [h2]
  have h3 : (1 + l) ^ k ≠ 0 := by positivity
  field_simp; push_cast; ring

theorem gP_succ (l A : ℝ) (hl : 0 < l) (hA : 0 < A) (k : ℕ) :
    gP l A (k + 1) - gP l A k = actQ l * (1 - (1 + l) ^ (k + 1) / A) := by
  unfold gP actQ
  have h1 : (0 : ℝ) < 1 + l := by linarith
  rw [pow_succ]
  field_simp; push_cast; ring

theorem fH_le_of_le (l A : ℝ) (hl : 0 < l) (J : ℕ) (hJ : (1 + l) ^ J ≤ A) (hJ1 : A < (1 + l) ^ (J + 1)) :
    ∀ j, fH l A J ≤ fH l A j := by
  have h1 : (1 : ℝ) ≤ 1 + l := by linarith
  have hdown : ∀ k, k < J → fH l A (k + 1) ≤ fH l A k := by
    intro k hk
    have := fH_succ l A hl k
    have hp : (1 + l) ^ (k + 1) ≤ A := (pow_le_pow_right₀ h1 hk).trans hJ
    have hpos : (0 : ℝ) < (1 + l) ^ (k + 1) := by positivity
    have : 1 - A / (1 + l) ^ (k + 1) ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hpos]; linarith
    nlinarith
  have hup : ∀ k, J ≤ k → fH l A k ≤ fH l A (k + 1) := by
    intro k hk
    have := fH_succ l A hl k
    have hp : A < (1 + l) ^ (k + 1) := hJ1.trans_le (pow_le_pow_right₀ h1 (by omega))
    have hpos : (0 : ℝ) < (1 + l) ^ (k + 1) := by positivity
    have : 0 ≤ 1 - A / (1 + l) ^ (k + 1) := by rw [sub_nonneg, div_le_one hpos]; linarith
    nlinarith
  intro j
  rcases le_total j J with h | h
  · have key : ∀ m, j ≤ m → m ≤ J → fH l A m ≤ fH l A j := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ m hm ih => intro hmJ; exact (hdown m (by omega)).trans (ih (by omega))
    exact key J h le_rfl
  · have key : ∀ m, J ≤ m → fH l A J ≤ fH l A m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact le_rfl
      | succ m hm ih => exact ih.trans (hup m hm)
    exact key j h

theorem gP_le_of_le (l A : ℝ) (hl : 0 < l) (hA : 0 < A) (J : ℕ) (hJ : (1 + l) ^ J ≤ A)
    (hJ1 : A < (1 + l) ^ (J + 1)) : ∀ j, gP l A j ≤ gP l A J := by
  have h1 : (1 : ℝ) ≤ 1 + l := by linarith
  have hq : 0 < actQ l := by unfold actQ; positivity
  have hup : ∀ k, k < J → gP l A k ≤ gP l A (k + 1) := by
    intro k hk
    have := gP_succ l A hl hA k
    have hp : (1 + l) ^ (k + 1) ≤ A := (pow_le_pow_right₀ h1 hk).trans hJ
    have : 0 ≤ 1 - (1 + l) ^ (k + 1) / A := by rw [sub_nonneg, div_le_one hA]; exact hp
    nlinarith
  have hdown : ∀ k, J ≤ k → gP l A (k + 1) ≤ gP l A k := by
    intro k hk
    have := gP_succ l A hl hA k
    have hp : A < (1 + l) ^ (k + 1) := hJ1.trans_le (pow_le_pow_right₀ h1 (by omega))
    have : 1 - (1 + l) ^ (k + 1) / A ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hA]; linarith
    nlinarith
  intro j
  rcases le_total j J with h | h
  · have key : ∀ m, j ≤ m → m ≤ J → gP l A j ≤ gP l A m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ m hm ih => intro hmJ; exact (ih (by omega)).trans (hup m (by omega))
    exact key J h le_rfl
  · have key : ∀ m, J ≤ m → gP l A m ≤ gP l A J := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => exact le_rfl
      | succ m hm ih => exact (hdown m hm).trans ih
    exact key j h

/-- The facts about `j = ⌊T/L⌋₊` at a message `0 < p < q`. -/
theorem packJ_facts {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) :
    1 < l * (1 - p) / p ∧ (1 + l) ^ packJ l p ≤ l * (1 - p) / p ∧
      l * (1 - p) / p < (1 + l) ^ (packJ l p + 1) := by
  have hq1 : actQ l < 1 := by unfold actQ; rw [div_lt_one (by linarith)]; linarith
  have hp1 : p < 1 := hpq.trans hq1
  have hA : 1 < l * (1 - p) / p := by
    rw [one_lt_div hp]
    unfold actQ at hpq; rw [lt_div_iff₀ (by linarith)] at hpq; nlinarith
  have hA0 : 0 < l * (1 - p) / p := by linarith
  have hL : 0 < Real.log (1 + l) := Real.log_pos (by linarith)
  have hT : 0 ≤ logMass l p := by unfold logMass; exact (Real.log_pos hA).le
  have hexp : ∀ n : ℕ, (1 + l) ^ n = Real.exp (n * Real.log (1 + l)) := by
    intro n; rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
  refine ⟨hA, ?_, ?_⟩
  · rw [hexp, ← Real.exp_log hA0]
    apply Real.exp_le_exp.mpr
    have h := Nat.floor_le (div_nonneg hT hL.le)
    unfold packJ
    unfold logMass at h ⊢
    rw [le_div_iff₀ hL] at h; linarith
  · rw [hexp, ← Real.exp_log hA0]
    apply Real.exp_lt_exp.mpr
    have h := Nat.lt_floor_add_one (logMass l p / Real.log (1 + l))
    unfold packJ
    unfold logMass at h ⊢
    rw [div_lt_iff₀ hL] at h; push_cast; linarith

theorem packH_eq {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) :
    packH l p = fH l (l * (1 - p) / p) (packJ l p) := by
  obtain ⟨hA, -, -⟩ := packJ_facts hl hp hpq
  unfold packH packRes fH logMass
  rw [Real.exp_sub, Real.exp_log (by linarith), mul_comm (packJ l p : ℝ), Real.exp_nat_mul,
    Real.exp_log (by linarith)]

theorem packPhi_eq {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) :
    packPhi l p = gP l (l * (1 - p) / p) (packJ l p) := by
  obtain ⟨hA, -, -⟩ := packJ_facts hl hp hpq
  unfold packPhi packRes gP logMass
  rw [neg_sub, Real.exp_sub, Real.exp_log (by linarith), mul_comm (packJ l p : ℝ), Real.exp_nat_mul,
    Real.exp_log (by linarith)]

theorem packH_le {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) (j : ℕ) :
    packH l p ≤ fH l (l * (1 - p) / p) j := by
  obtain ⟨hA, h1, h2⟩ := packJ_facts hl hp hpq
  rw [packH_eq hl hp hpq]; exact fH_le_of_le l _ hl _ h1 h2 j

theorem le_packPhi {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) (j : ℕ) :
    gP l (l * (1 - p) / p) j ≤ packPhi l p := by
  obtain ⟨hA, h1, h2⟩ := packJ_facts hl hp hpq
  rw [packPhi_eq hl hp hpq]; exact gP_le_of_le l _ hl (by linarith) _ h1 h2 j

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The packing loops -/

section Pack

variable {L X : Ival}

theorem de_dpow {fb : ℝ → ℝ → ℝ} {bb : DN} (hb : DE L X fb bb) :
    ∀ j, DE L X (fun l x => fb l x ^ j) (dpow bb j)
  | 0 => by simpa using (de_cst (L := L) (X := X) mem_oneI)
  | j + 1 => by
    have := de_mul (de_dpow hb j) hb
    simpa [pow_succ] using this

theorem dpow_ok {bb : DN} : ∀ j, (dpow bb (j + 1)).ok = true → bb.ok = true
  | 0 => by simp [dpow, dmul, oneDN, DN.cst]
  | j + 1 => by
    intro h
    simp only [dpow, dmul, Bool.and_eq_true] at h
    exact h.2

theorem dpow_ok' {bb : DN} (h : bb.ok = true) : ∀ j, (dpow bb j).ok = true
  | 0 => rfl
  | j + 1 => by simp only [dpow, dmul, Bool.and_eq_true]; exact ⟨dpow_ok' h j, h⟩

/-- The lower packing loop: the result `(jm, b)` has `b = bb^jm`, and `jm = 0` or `b.hi ≤ aa.lo`. -/
theorem jLow_spec (aa bb : DN) : ∀ (f j : ℕ) (b : DN), b = dpow bb j → (j = 0 ∨ b.v.hi ≤ aa.v.lo) →
    (jLow aa bb f j b).2 = dpow bb (jLow aa bb f j b).1 ∧
      ((jLow aa bb f j b).1 = 0 ∨ (jLow aa bb f j b).2.v.hi ≤ aa.v.lo)
  | 0, j, b, hb, h => by simp only [jLow]; exact ⟨hb, h⟩
  | f + 1, j, b, hb, h => by
    simp only [jLow]
    split_ifs with hc
    · exact jLow_spec aa bb f (j + 1) (dmul b bb) (by rw [hb]; rfl) (Or.inr hc)
    · exact ⟨hb, h⟩

/-- The upper packing loop: if it stopped by its test, `(bb^(jM+1)).lo ≥ aa.hi`. -/
theorem jHigh_spec (aa bb : DN) : ∀ (f j : ℕ) (b : DN), b = dpow bb j → (jHigh aa bb f j b).2 = true →
    aa.v.hi ≤ (dpow bb ((jHigh aa bb f j b).1 + 1)).v.lo ∧ j ≤ (jHigh aa bb f j b).1
  | 0, j, b, _, h => by simp [jHigh] at h
  | f + 1, j, b, hb, h => by
    simp only [jHigh] at h ⊢
    split_ifs with hc
    · rw [if_pos hc] at h
      have := jHigh_spec aa bb f (j + 1) (dmul b bb) (by rw [hb]; rfl) h
      exact ⟨this.1, by omega⟩
    · refine ⟨?_, le_rfl⟩
      rw [hb] at hc; simpa [dpow] using not_lt.mp hc

end Pack

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

section PackHull

variable {L X : Ival} (fl fq fa : ℝ → ℝ → ℝ)

/-- The minimum of `f_j = λ j + A/(λ+1)ʲ − 1` over `j = j0, …, j0 + k`. -/
noncomputable def minF (j0 : ℕ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun l x => fl l x * (j0 : ℝ) + fa l x / (fl l x + 1) ^ j0 - 1
  | k + 1 => fun l x => min (minF j0 k l x)
      (fl l x * ((j0 + k + 1 : ℕ) : ℝ) + fa l x / (fl l x + 1) ^ (j0 + k + 1) - 1)

/-- The maximum of `g_j = q j + 1 − (λ+1)ʲ/A` over `j = j0, …, j0 + k`. -/
noncomputable def maxG (j0 : ℕ) : ℕ → ℝ → ℝ → ℝ
  | 0 => fun l x => fq l x * (j0 : ℝ) + 1 - (fl l x + 1) ^ j0 / fa l x
  | k + 1 => fun l x => max (maxG j0 k l x)
      (fq l x * ((j0 + k + 1 : ℕ) : ℝ) + 1 - (fl l x + 1) ^ (j0 + k + 1) / fa l x)

variable {fl fq fa}

theorem de_packHV {lam q aa : DN} (hl : DE L X fl lam) (hq : DE L X fq q) (ha : DE L X fa aa)
    (hb : DE L X (fun l x => fl l x + 1) (daddI lam oneI)) (j : ℕ) :
    DE L X (fun l x => fl l x * (j : ℝ) + fa l x / (fl l x + 1) ^ j - 1) (packHV lam q aa (daddI lam oneI) j).1 ∧
      DE L X (fun l x => fq l x * (j : ℝ) + 1 - (fl l x + 1) ^ j / fa l x)
        (packHV lam q aa (daddI lam oneI) j).2 := by
  have hp := de_dpow hb j
  exact ⟨de_subI (de_add (de_mulI hl (mem_ptOne j)) (de_div ha hp)) mem_oneI,
    de_sub (de_addI (de_mulI hq (mem_ptOne j)) mem_oneI) (de_div hp ha)⟩

theorem de_packHull {lam q aa : DN} (hl : DE L X fl lam) (hq : DE L X fq q) (ha : DE L X fa aa)
    (hb : DE L X (fun l x => fl l x + 1) (daddI lam oneI)) (j0 : ℕ) :
    ∀ k, DE L X (minF fl fa j0 k) (packHull lam q aa (daddI lam oneI) j0 k).1 ∧
      DE L X (maxG fl fq fa j0 k) (packHull lam q aa (daddI lam oneI) j0 k).2
  | 0 => de_packHV hl hq ha hb j0
  | k + 1 => by
    obtain ⟨h1, h2⟩ := de_packHull hl hq ha hb j0 k
    obtain ⟨n1, n2⟩ := de_packHV hl hq ha hb (j0 + k + 1)
    exact ⟨de_dhull_min h1 n1 (fun _ _ _ _ => rfl), de_dhull_max h2 n2 (fun _ _ _ _ => rfl)⟩

theorem minF_le (l x : ℝ) (j0 : ℕ) : ∀ k, ∀ j, j0 ≤ j → j ≤ j0 + k →
    minF fl fa j0 k l x ≤ fl l x * (j : ℝ) + fa l x / (fl l x + 1) ^ j - 1
  | 0 => fun j h1 h2 => by
    obtain rfl : j = j0 := by omega
    exact le_rfl
  | k + 1 => fun j h1 h2 => by
    rcases Nat.lt_or_ge j (j0 + k + 1) with h | h
    · exact (min_le_left _ _).trans (minF_le l x j0 k j h1 (by omega))
    · obtain rfl : j = j0 + k + 1 := by omega
      exact min_le_right _ _

theorem minF_eq (l x : ℝ) (j0 : ℕ) : ∀ k, ∃ j, j0 ≤ j ∧ j ≤ j0 + k ∧
    minF fl fa j0 k l x = fl l x * (j : ℝ) + fa l x / (fl l x + 1) ^ j - 1
  | 0 => ⟨j0, le_rfl, by omega, rfl⟩
  | k + 1 => by
    obtain ⟨j, h1, h2, h3⟩ := minF_eq l x j0 k
    show ∃ j', _ ∧ _ ∧ min (minF fl fa j0 k l x) _ = _
    rcases min_choice (minF fl fa j0 k l x)
      (fl l x * ((j0 + k + 1 : ℕ) : ℝ) + fa l x / (fl l x + 1) ^ (j0 + k + 1) - 1) with h | h
    · exact ⟨j, h1, by omega, by rw [h, h3]⟩
    · exact ⟨j0 + k + 1, by omega, by omega, h⟩

theorem le_maxG (l x : ℝ) (j0 : ℕ) : ∀ k, ∀ j, j0 ≤ j → j ≤ j0 + k →
    fq l x * (j : ℝ) + 1 - (fl l x + 1) ^ j / fa l x ≤ maxG fl fq fa j0 k l x
  | 0 => fun j h1 h2 => by
    obtain rfl : j = j0 := by omega
    exact le_rfl
  | k + 1 => fun j h1 h2 => by
    rcases Nat.lt_or_ge j (j0 + k + 1) with h | h
    · exact (le_maxG l x j0 k j h1 (by omega)).trans (le_max_left _ _)
    · obtain rfl : j = j0 + k + 1 := by omega
      exact le_max_right _ _

theorem maxG_eq (l x : ℝ) (j0 : ℕ) : ∀ k, ∃ j, j0 ≤ j ∧ j ≤ j0 + k ∧
    maxG fl fq fa j0 k l x = fq l x * (j : ℝ) + 1 - (fl l x + 1) ^ j / fa l x
  | 0 => ⟨j0, le_rfl, by omega, rfl⟩
  | k + 1 => by
    obtain ⟨j, h1, h2, h3⟩ := maxG_eq l x j0 k
    show ∃ j', _ ∧ _ ∧ max (maxG fl fq fa j0 k l x) _ = _
    rcases max_choice (maxG fl fq fa j0 k l x)
      (fq l x * ((j0 + k + 1 : ℕ) : ℝ) + 1 - (fl l x + 1) ^ (j0 + k + 1) / fa l x) with h | h
    · exact ⟨j, h1, by omega, by rw [h, h3]⟩
    · exact ⟨j0 + k + 1, by omega, by omega, h⟩

end PackHull

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic Erdos993Lean.Analytic.O2
open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem fH_eq_form (l A : ℝ) (j : ℕ) : fH l A j = l * (j : ℝ) + A / (l + 1) ^ j - 1 := by
  unfold fH; rw [add_comm l 1]; ring

theorem gP_eq_form (l A : ℝ) (j : ℕ) : gP l A j = actQ l * (j : ℝ) + 1 - (l + 1) ^ j / A := by
  unfold gP; rw [add_comm l 1]; ring

/-- The range of the packing index on the box: `(1+λ)^jm ≤ A ≤ (1+λ)^(jM+1)` and `jm ≤ J ≤ jM + 1`, with the tie
`f_{jM} = f_{jM+1}` when `J = jM + 1`. -/
theorem packJ_range {l p : ℝ} (hl : 0 < l) (hp : 0 < p) (hpq : p < actQ l) {jm jM : ℕ}
    (h1 : (l + 1) ^ jm ≤ l * (1 - p) / p) (h2 : l * (1 - p) / p ≤ (l + 1) ^ (jM + 1)) :
    jm ≤ packJ l p ∧ packJ l p ≤ jM + 1 ∧
      (packJ l p = jM + 1 → l * (1 - p) / p = (l + 1) ^ (jM + 1)) := by
  obtain ⟨hA, hJ1, hJ2⟩ := packJ_facts hl hp hpq
  rw [add_comm 1 l] at hJ1 hJ2
  have hb : 1 < l + 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have : (l + 1) ^ (packJ l p + 1) ≤ (l + 1) ^ jm := pow_le_pow_right₀ hb.le (by omega)
    linarith
  · by_contra h
    have : (l + 1) ^ (jM + 1) < (l + 1) ^ packJ l p := pow_lt_pow_right₀ hb (by omega)
    linarith
  · intro h; rw [h] at hJ1; linarith

theorem de_packing {L X : Ival} {fl fq fa P : ℝ → ℝ → ℝ} {lam q aa : DN} (hl : DE L X fl lam)
    (hq : DE L X fq q) (ha : DE L X fa aa) (hb : DE L X (fun l x => fl l x + 1) (daddI lam oneI))
    (hbok : (daddI lam oneI).ok = true) (haok : aa.ok = true)
    (hbox : ∀ l x, L.Mem l → X.Mem x → 0 < fl l x ∧ 0 < P l x ∧ P l x < actQ (fl l x) ∧
      fa l x = fl l x * (1 - P l x) / P l x ∧ fq l x = actQ (fl l x)) :
    DE L X (fun l x => packH (fl l x) (P l x)) (packing lam q aa (daddI lam oneI)).1 ∧
      DE L X (fun l x => packPhi (fl l x) (P l x)) (packing lam q aa (daddI lam oneI)).2 := by
  set bb := daddI lam oneI with hbbdef
  set lo := jLow aa bb 64 0 oneDN with hlo
  set hi := jHigh aa bb 64 lo.1 lo.2 with hhi
  obtain ⟨hlo1, hlo2⟩ := jLow_spec aa bb 64 0 oneDN rfl (Or.inl rfl)
  have haE := ha haok
  have hpowE : ∀ j, DEnc L X (fun l x => (fl l x + 1) ^ j) (dpow bb j) := fun j => de_dpow hb j (dpow_ok' hbok j)
  have key : hi.2 = true → ∀ l x, L.Mem l → X.Mem x →
      lo.1 ≤ packJ (fl l x) (P l x) ∧ packJ (fl l x) (P l x) ≤ hi.1 + 1 ∧
        (packJ (fl l x) (P l x) = hi.1 + 1 → fa l x = (fl l x + 1) ^ (hi.1 + 1)) ∧ lo.1 ≤ hi.1 := by
    intro hstop l x hlm hxm
    obtain ⟨hl0, hp0, hpq, hA, -⟩ := hbox l x hlm hxm
    obtain ⟨hup, hle⟩ := jHigh_spec aa bb 64 lo.1 lo.2 hlo1 hstop
    have h1 : (fl l x + 1) ^ lo.1 ≤ fa l x := by
      rcases hlo2 with h0 | h0
      · rw [h0, pow_zero, hA]
        obtain ⟨hA1, -, -⟩ := packJ_facts hl0 hp0 hpq; linarith
      · have := (hpowE lo.1).le_hi hlm hxm
        rw [← hlo1] at this
        exact this.trans ((toR_le_toR.mpr h0).trans (haE.lo_le hlm hxm))
    have h2 : fa l x ≤ (fl l x + 1) ^ (hi.1 + 1) :=
      (haE.le_hi hlm hxm).trans ((toR_le_toR.mpr hup).trans ((hpowE (hi.1 + 1)).lo_le hlm hxm))
    rw [hA] at h1 h2 ⊢
    obtain ⟨r1, r2, r3⟩ := packJ_range hl0 hp0 hpq h1 h2
    exact ⟨r1, r2, r3, hle⟩
  have hEqH : hi.2 = true → ∀ l x, L.Mem l → X.Mem x →
      minF fl fa lo.1 (hi.1 - lo.1) l x = packH (fl l x) (P l x) := by
    intro hstop l x hlm hxm
    obtain ⟨hl0, hp0, hpq, hA, -⟩ := hbox l x hlm hxm
    obtain ⟨r1, r2, r3, hle⟩ := key hstop l x hlm hxm
    apply le_antisymm
    · rcases Nat.lt_or_ge (packJ (fl l x) (P l x)) (hi.1 + 1) with h | h
      · have := minF_le (fl := fl) (fa := fa) l x lo.1 (hi.1 - lo.1) (packJ (fl l x) (P l x)) r1 (by omega)
        rw [packH_eq hl0 hp0 hpq, fH_eq_form, ← hA]; exact this
      · have hJ : packJ (fl l x) (P l x) = hi.1 + 1 := by omega
        have htie := r3 hJ
        have := minF_le (fl := fl) (fa := fa) l x lo.1 (hi.1 - lo.1) hi.1 (by omega) (by omega)
        rw [packH_eq hl0 hp0 hpq, hJ, fH_eq_form, ← hA]
        refine this.trans (le_of_eq ?_)
        have hne : (fl l x + 1) ^ hi.1 ≠ 0 := by positivity
        rw [htie, pow_succ]; field_simp; push_cast; ring
    · obtain ⟨j, -, -, hj⟩ := minF_eq (fl := fl) (fa := fa) l x lo.1 (hi.1 - lo.1)
      rw [hj]
      have := packH_le hl0 hp0 hpq j
      rw [fH_eq_form, ← hA] at this; exact this
  have hEqP : hi.2 = true → ∀ l x, L.Mem l → X.Mem x →
      maxG fl fq fa lo.1 (hi.1 - lo.1) l x = packPhi (fl l x) (P l x) := by
    intro hstop l x hlm hxm
    obtain ⟨hl0, hp0, hpq, hA, hQ⟩ := hbox l x hlm hxm
    obtain ⟨r1, r2, r3, hle⟩ := key hstop l x hlm hxm
    apply le_antisymm
    · obtain ⟨j, -, -, hj⟩ := maxG_eq (fl := fl) (fq := fq) (fa := fa) l x lo.1 (hi.1 - lo.1)
      rw [hj]
      have := le_packPhi hl0 hp0 hpq j
      rw [gP_eq_form, ← hA, ← hQ] at this; exact this
    · rcases Nat.lt_or_ge (packJ (fl l x) (P l x)) (hi.1 + 1) with h | h
      · have := le_maxG (fl := fl) (fq := fq) (fa := fa) l x lo.1 (hi.1 - lo.1) (packJ (fl l x) (P l x)) r1
          (by omega)
        rw [packPhi_eq hl0 hp0 hpq, gP_eq_form, ← hA, ← hQ]; exact this
      · have hJ : packJ (fl l x) (P l x) = hi.1 + 1 := by omega
        have htie := r3 hJ
        have := le_maxG (fl := fl) (fq := fq) (fa := fa) l x lo.1 (hi.1 - lo.1) hi.1 (by omega) (by omega)
        rw [packPhi_eq hl0 hp0 hpq, hJ, gP_eq_form, ← hA, ← hQ]
        refine le_trans (le_of_eq ?_) this
        rw [htie, pow_succ]
        have hne : (fl l x + 1) ^ hi.1 ≠ 0 := by positivity
        have hl1 : fl l x + 1 ≠ 0 := by linarith
        rw [hQ]; unfold actQ; field_simp; push_cast; ring
  obtain ⟨hH, hP⟩ := de_packHull hl hq ha hb lo.1 (hi.1 - lo.1)
  constructor
  · intro hok
    simp only [packing, Bool.and_eq_true] at hok
    obtain ⟨hok1, hstop⟩ := hok
    have h := de_congr hH (hEqH hstop) hok1
    exact ⟨h.val, h.sl0, h.sl1⟩
  · intro hok
    simp only [packing, Bool.and_eq_true] at hok
    obtain ⟨hok1, hstop⟩ := hok
    have h := de_congr hP (hEqP hstop) hok1
    exact ⟨h.val, h.sl0, h.sl1⟩

end Erdos993Lean.Analytic.O2.Cert
