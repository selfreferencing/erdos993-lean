import Mathlib
import Erdos993Lean.Analytic.O2.Cert.DualSound

/-!
# O2 certificate checker (lane A18): the removable kernel

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A18.  For `x = p/q ≥ 7/8` the checker writes the own
Cauchy coefficients through the kernel `k(e, λ) = (log(1 + λe) − log(1 − e))/e` (`e = 1 − x`, `PRO_R2_PROOF.md` §8,
§9.1), so that `x = 1` needs no `0/0`.  Here `kR e λ = ∑ₙ cₙ(λ) eⁿ`, `cₙ(λ) = ((−1)ⁿ λⁿ⁺¹ + 1)/(n + 1)`.

* `hasSum_kR`, **`kR_mul`**: `e · k(e, λ) = log(1 + λe) − log(1 − e)` (from Mathlib's series of `−log(1 − x)`);
  `kR_zero`: `k(0, λ) = 1 + λ`;
* `kernel_val`: the value interval (32 terms and the geometric tail);
* `kernel_slope_e`: the `e`-slope (divided differences `∑ cₙ σₙ`, `σₙ = ∑_{i<n} e'^i e^{n−1−i}`; 16 terms and the
  geometric tail); `kernel_slope_l`: the `λ`-slope `1/ξ`, `ξ` between `1 + λe` and `1 + λ'e`;
* `sl_chain` (the chain rule for slopes) and **`de_kernel`**: the kernel dual number encloses `k(e, λ)`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-! ## The removable kernel `k(e, λ) = ∑ₙ cₙ(λ) eⁿ`, `cₙ(λ) = ((−1)ⁿ λⁿ⁺¹ + 1)/(n + 1)` -/

/-- The coefficients of the kernel series. -/
noncomputable def kc (l : ℝ) (n : ℕ) : ℝ := ((-1) ^ n * l ^ (n + 1) + 1) / (n + 1)

/-- The kernel `k(e, λ) = (log(1 + λe) − log(1 − e))/e`, by its power series (`k(0, λ) = 1 + λ`). -/
noncomputable def kR (e l : ℝ) : ℝ := ∑' n : ℕ, kc l n * e ^ n

theorem abs_kc_le {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : |kc l n| ≤ l ^ (n + 1) + 1 := by
  unfold kc
  have hn : (1 : ℝ) ≤ n + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n + 1), div_le_iff₀ (by linarith)]
  have h1 : |(-1 : ℝ) ^ n * l ^ (n + 1) + 1| ≤ l ^ (n + 1) + 1 := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    simp [abs_mul, abs_of_nonneg (pow_nonneg hl _)]
  have h2 : 0 ≤ l ^ (n + 1) + 1 := by positivity
  nlinarith

/-- The majorant `(λⁿ⁺¹ + 1) eⁿ` is summable. -/
theorem summable_major {e l : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hl : 0 ≤ l) (hle : l * e < 1) :
    Summable (fun n : ℕ => (l ^ (n + 1) + 1) * e ^ n) := by
  have h1 : Summable (fun n : ℕ => l * (l * e) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hle).mul_left l
  have h2 : Summable (fun n : ℕ => e ^ n) := summable_geometric_of_lt_one he0 he1
  refine (h1.add h2).congr (fun n => ?_)
  ring

theorem summable_kc {e l : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hl : 0 ≤ l) (hle : l * e < 1) :
    Summable (fun n : ℕ => kc l n * e ^ n) := by
  refine Summable.of_norm_bounded (summable_major he0 he1 hl hle) (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg he0 _)]
  exact mul_le_mul_of_nonneg_right (abs_kc_le hl n) (pow_nonneg he0 _)

theorem hasSum_kR {e l : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hl : 0 ≤ l) (hle : l * e < 1) :
    HasSum (fun n : ℕ => kc l n * e ^ n) (kR e l) := (summable_kc he0 he1 hl hle).hasSum

/-- `e k(e, λ) = log(1 + λe) − log(1 − e)`. -/
theorem kR_mul {e l : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hl : 0 ≤ l) (hle : l * e < 1) :
    e * kR e l = Real.log (1 + l * e) - Real.log (1 - e) := by
  have h1 := Real.hasSum_pow_div_log_of_abs_lt_one (show |e| < 1 by rw [abs_of_nonneg he0]; exact he1)
  have h2 := Real.hasSum_pow_div_log_of_abs_lt_one
    (show |-(l * e)| < 1 by rw [abs_neg, abs_of_nonneg (by positivity)]; exact hle)
  rw [sub_neg_eq_add] at h2
  have h3 := (hasSum_kR he0 he1 hl hle).mul_left e
  have h4 := h1.sub h2
  have e4 : (fun n : ℕ => e * (kc l n * e ^ n)) =
      (fun n : ℕ => e ^ (n + 1) / (n + 1) - (-(l * e)) ^ (n + 1) / (n + 1)) := by
    funext n; unfold kc
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring_nf
  rw [e4] at h3
  rw [h3.unique h4]; ring

/-- The tail of a series is bounded by the sum of a majorant of its terms. -/
theorem abs_tail_le {a b : ℕ → ℝ} {S B : ℝ} (hS : HasSum a S) (N : ℕ) (hb : ∀ n, |a (n + N)| ≤ b n)
    (hB : HasSum b B) : |S - ∑ n ∈ Finset.range N, a n| ≤ B := by
  have hsum := hS.summable
  have htail : HasSum (fun n => a (n + N)) (S - ∑ n ∈ Finset.range N, a n) :=
    (hasSum_nat_add_iff' N).mpr hS
  have hsn : Summable (fun n => |a (n + N)|) := hB.summable.of_nonneg_of_le (fun n => abs_nonneg _) hb
  rw [← htail.tsum_eq]
  have h1 : |∑' n, a (n + N)| ≤ ∑' n, |a (n + N)| := by
    have := norm_tsum_le_tsum_norm (f := fun n => a (n + N)) (by simpa [Real.norm_eq_abs] using hsn)
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  rw [← hB.tsum_eq]
  exact hsn.tsum_le_tsum hb hB.summable

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem mem_sign (n : ℕ) : ((if n % 2 = 0 then (1 : ℤ) else -1 : ℤ) : ℝ) = (-1) ^ n := by
  rcases Nat.even_or_odd n with h | h
  · rw [if_pos (Nat.even_iff.mp h), h.neg_one_pow]; simp
  · rw [if_neg (by rw [Nat.odd_iff] at h; omega), h.neg_one_pow]; simp

theorem mem_sign' (n : ℕ) : ((if (n + 1) % 2 = 1 then (-1 : ℤ) else 1 : ℤ) : ℝ) = (-1) ^ (n + 1) := by
  rcases Nat.even_or_odd (n + 1) with h | h
  · rw [if_neg (by rw [Nat.even_iff] at h; omega), h.neg_one_pow]; simp
  · rw [if_pos (Nat.odd_iff.mp h), h.neg_one_pow]; simp

theorem kvalLoop_mem {lv ev : Ival} {l e : ℝ} (hl : lv.Mem l) (he : ev.Mem e) (k : ℕ) :
    (kvalLoop lv ev k).1.Mem (∑ n ∈ Finset.range k, kc l n * e ^ n) ∧
      (kvalLoop lv ev k).2.1.Mem (l ^ (k + 1)) ∧ (kvalLoop lv ev k).2.2.Mem (e ^ k) := by
  induction k with
  | zero => exact ⟨by simpa using mem_zI, by simpa using hl, by simpa using mem_oneI⟩
  | succ n ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · show (add (kvalLoop lv ev n).1 (divNat (mul (add (mulInt (kvalLoop lv ev n).2.1
        (if n % 2 = 0 then 1 else -1)) oneI) (kvalLoop lv ev n).2.2) (n + 1))).Mem _
      rw [Finset.sum_range_succ]
      refine mem_add h1 ?_
      have hc := mem_add (mem_mulInt h2 (if n % 2 = 0 then 1 else -1)) mem_oneI
      rw [mem_sign] at hc
      have := mem_divNat (mem_mul hc h3) (Nat.succ_pos n)
      unfold kc
      convert this using 1
      all_goals (try push_cast); all_goals (try field_simp)
    · show (mul (kvalLoop lv ev n).2.1 lv).Mem _
      rw [pow_succ]; exact mem_mul h2 hl
    · show (mul (kvalLoop lv ev n).2.2 ev).Mem _
      rw [pow_succ]; exact mem_mul h3 he

theorem ipow_mem {A : Ival} {t : ℝ} (ht : A.Mem t) (k : ℕ) : (ipow A k).Mem (t ^ k) := by
  induction k with
  | zero => simpa using mem_oneI
  | succ n ih => rw [pow_succ]; exact mem_mul ih ht

theorem kpartLoop_ep (lv ev : Ival) (k : ℕ) : (kpartLoop lv ev k).2.2 = ipow ev k := by
  induction k with
  | zero => rfl
  | succ n ih => show mul (kpartLoop lv ev n).2.2 ev = mul (ipow ev n) ev; rw [ih]

/-- The head of the `e`-slope series: any `wₘ` in the interval power `e^(m−1)` gives
`∑_{m=1}^{K} cₘ m wₘ`. -/
theorem kpartLoop_mem {lv ev : Ival} {l : ℝ} (hl : lv.Mem l) (w : ℕ → ℝ) (hw : ∀ k, (ipow ev k).Mem (w k))
    (K : ℕ) :
    (kpartLoop lv ev K).1.Mem (∑ k ∈ Finset.range K, kc l (k + 1) * (k + 1) * w k) ∧
      (kpartLoop lv ev K).2.1.Mem (l ^ (K + 2)) := by
  induction K with
  | zero => exact ⟨by simpa using mem_zI, by simpa [pow_two] using mem_mul hl hl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · show (add (kpartLoop lv ev n).1 (divNat (mulNat (mul (add (mulInt (kpartLoop lv ev n).2.1
        (if (n + 1) % 2 = 1 then -1 else 1)) oneI) (kpartLoop lv ev n).2.2) (n + 1)) (n + 2))).Mem _
      rw [Finset.sum_range_succ]
      refine mem_add h1 ?_
      have hc := mem_add (mem_mulInt h2 (if (n + 1) % 2 = 1 then -1 else 1)) mem_oneI
      rw [mem_sign'] at hc
      have hep := kpartLoop_ep lv ev n ▸ hw n
      have := mem_divNat (mem_mulNat (mem_mul hc hep) (n + 1)) (Nat.succ_pos (n + 1))
      unfold kc
      convert this using 1
      all_goals (try push_cast); all_goals (try field_simp); all_goals (try ring)
    · show (mul (kpartLoop lv ev n).2.1 lv).Mem _
      rw [show n + 1 + 2 = (n + 2) + 1 by ring, pow_succ]; exact mem_mul h2 hl

/-- A product `∏` of numbers in `[lo, hi] ⊆ [0, ∞)` lies in the interval power. -/
theorem mem_ipow_of_between {A : Ival} (h0 : 0 ≤ A.lo) (k : ℕ) {t : ℝ}
    (h1 : toR A.lo ^ k ≤ t) (h2 : t ≤ toR A.hi ^ k) (hne : A.lo ≤ A.hi) : (ipow A k).Mem t := by
  have hlo : A.Mem (toR A.lo) := ⟨le_rfl, toR_le_toR.mpr hne⟩
  have hhi : A.Mem (toR A.hi) := ⟨toR_le_toR.mpr hne, le_rfl⟩
  exact Compute.Ival.Mem.between (ipow_mem hlo k) (ipow_mem hhi k)
    (by rw [min_eq_left (pow_le_pow_left₀ (toR_nonneg.mpr h0) (toR_le_toR.mpr hne) k)]; exact h1)
    (by rw [max_eq_right (pow_le_pow_left₀ (toR_nonneg.mpr h0) (toR_le_toR.mpr hne) k)]; exact h2)

/-- The divided-difference weights `σₙ = ∑_{i<n} bⁱ aⁿ⁻¹⁻ⁱ`. -/
noncomputable def sig (a b : ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, b ^ i * a ^ (n - 1 - i)

theorem sig_mul (a b : ℝ) (n : ℕ) : sig a b n * (b - a) = b ^ n - a ^ n := by
  unfold sig; exact Commute.geom_sum₂_mul (Commute.all b a) n

theorem sig_bounds {lo hi a b : ℝ} (h0 : 0 ≤ lo) (ha : lo ≤ a) (ha' : a ≤ hi) (hb : lo ≤ b) (hb' : b ≤ hi) (n : ℕ) :
    (n : ℝ) * lo ^ (n - 1) ≤ sig a b n ∧ sig a b n ≤ n * hi ^ (n - 1) := by
  unfold sig
  have hterm : ∀ i ∈ Finset.range n, lo ^ (n - 1) ≤ b ^ i * a ^ (n - 1 - i) ∧
      b ^ i * a ^ (n - 1 - i) ≤ hi ^ (n - 1) := by
    intro i hi'
    have hi'' : i ≤ n - 1 := by rw [Finset.mem_range] at hi'; omega
    have e : ∀ t : ℝ, t ^ (n - 1) = t ^ i * t ^ (n - 1 - i) := by
      intro t; rw [← pow_add]; congr 1; omega
    constructor
    · rw [e lo]
      exact mul_le_mul (pow_le_pow_left₀ h0 hb i) (pow_le_pow_left₀ h0 ha _) (by positivity)
        (pow_nonneg (h0.trans hb) _)
    · rw [e hi]
      exact mul_le_mul (pow_le_pow_left₀ (h0.trans hb) hb' i) (pow_le_pow_left₀ (h0.trans ha) ha' _)
        (pow_nonneg (h0.trans ha) _) (pow_nonneg ((h0.trans hb).trans hb') _)
  constructor
  · have := Finset.sum_le_sum (fun i hi => (hterm i hi).1)
    simpa using this
  · have := Finset.sum_le_sum (fun i hi => (hterm i hi).2)
    simpa using this

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

theorem abs_kc_mul_le {l : ℝ} (hl : 0 ≤ l) (n : ℕ) : |kc l n| * (n + 1) ≤ l ^ (n + 1) + 1 := by
  unfold kc
  have hn : (0 : ℝ) < n + 1 := by positivity
  rw [abs_div, abs_of_pos hn, div_mul_cancel₀ _ hn.ne']
  refine (abs_add_le _ _).trans (le_of_eq ?_)
  simp [abs_mul, abs_of_nonneg (pow_nonneg hl _)]

theorem kR_zero (l : ℝ) : kR 0 l = l + 1 := by
  unfold kR
  rw [tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  unfold kc; norm_num

/-- The geometric majorant of a kernel tail. -/
theorem hasSum_major_tail {l e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hl : 0 ≤ l) (hle : l * e < 1) (N : ℕ) :
    HasSum (fun n : ℕ => (l ^ (n + N + 1) + 1) * e ^ (n + N))
      (l ^ (N + 1) * e ^ N / (1 - l * e) + e ^ N / (1 - e)) := by
  have h1 := (hasSum_geometric_of_lt_one (by positivity) hle).mul_left (l ^ (N + 1) * e ^ N)
  have h2 := (hasSum_geometric_of_lt_one he0 he1).mul_left (e ^ N)
  convert h1.add h2 using 1
  · funext n; ring
  all_goals (try field_simp)

/-- The value of the kernel on the box. -/
theorem kernel_val {lv ev : Ival} {l e : ℝ} (hl : lv.Mem l) (he : ev.Mem e) (hl0 : 0 ≤ l) (he0 : 0 ≤ e)
    (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo) :
    (⟨(kvalLoop lv ev nK).1.lo - (add (div (mul (kvalLoop lv ev nK).2.1 (kvalLoop lv ev nK).2.2)
        (sub oneI (mul lv ev))) (div (kvalLoop lv ev nK).2.2 (sub oneI ev))).hi,
      (kvalLoop lv ev nK).1.hi + (add (div (mul (kvalLoop lv ev nK).2.1 (kvalLoop lv ev nK).2.2)
        (sub oneI (mul lv ev))) (div (kvalLoop lv ev nK).2.2 (sub oneI ev))).hi⟩ : Ival).Mem (kR e l) := by
  have hle := mem_sub mem_oneI (mem_mul hl he)
  have he1' := mem_sub mem_oneI he
  have hle1 : l * e < 1 := by have := (toR_pos.mpr h1).trans_le hle.1; linarith
  have he1 : e < 1 := by have := (toR_pos.mpr h2).trans_le he1'.1; linarith
  obtain ⟨hS, hL, hE⟩ := kvalLoop_mem hl he nK
  have hR := mem_add (mem_div (mem_mul hL hE) hle h1) (mem_div hE he1' h2)
  have hT := abs_tail_le (hasSum_kR he0 he1 hl0 hle1) nK
    (b := fun n => (l ^ (n + nK + 1) + 1) * e ^ (n + nK))
    (fun n => by
      rw [abs_mul, abs_of_nonneg (pow_nonneg he0 _)]
      exact mul_le_mul_of_nonneg_right (abs_kc_le hl0 _) (pow_nonneg he0 _))
    (hasSum_major_tail he0 he1 hl0 hle1 nK)
  rw [abs_le] at hT
  constructor
  · show toR ((kvalLoop lv ev nK).1.lo - _) ≤ kR e l
    rw [toR_sub]; linarith [hS.1, hR.2]
  · show kR e l ≤ toR ((kvalLoop lv ev nK).1.hi + _)
    rw [toR_add]; linarith [hS.2, hR.2]

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The `e`-slope interval of the kernel. -/
def kPart (lv ev : Ival) : Ival :=
  let ps := (kpartLoop lv ev mK).1
  let er := add (div (mul (mul lv lv) (ipow (mul lv ev) mK)) (sub oneI (mul lv ev)))
    (div (ipow ev mK) (sub oneI ev))
  ⟨ps.lo - er.hi, ps.hi + er.hi⟩

theorem kPart_mem_of_head {lv ev : Ival} {l H T : ℝ} (hl : lv.Mem l) (hlo : 0 ≤ ev.lo) (hne : ev.lo ≤ ev.hi)
    (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo) (hH : (kpartLoop lv ev mK).1.Mem H)
    (hT : |T| ≤ l * l * (l * toR ev.hi) ^ mK / (1 - l * toR ev.hi) + toR ev.hi ^ mK / (1 - toR ev.hi)) :
    (kPart lv ev).Mem (H + T) := by
  have hhi : ev.Mem (toR ev.hi) := ⟨toR_le_toR.mpr hne, le_rfl⟩
  have hle := mem_sub mem_oneI (mem_mul hl hhi)
  have hR := mem_add (mem_div (mem_mul (mem_mul hl hl) (ipow_mem (mem_mul hl hhi) mK)) hle h1)
    (mem_div (ipow_mem hhi mK) (mem_sub mem_oneI hhi) h2)
  rw [abs_le] at hT
  unfold kPart
  constructor
  · show toR (_ - _) ≤ H + T
    rw [toR_sub]; linarith [hH.1, hR.2]
  · show H + T ≤ toR (_ + _)
    rw [toR_add]; linarith [hH.2, hR.2]

/-- **The `e`-slope of the kernel**: for `e ≠ e'` in `ev ⊆ [0, 1)` and `λ ∈ lv`, a slope in `kPart`. -/
theorem kernel_slope_e {lv ev : Ival} {l e e' : ℝ} (hl : lv.Mem l) (he : ev.Mem e) (he' : ev.Mem e')
    (hl0 : 0 ≤ l) (hlo : 0 ≤ ev.lo) (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo)
    (hne : e ≠ e') : ∃ s, (kPart lv ev).Mem s ∧ kR e' l - kR e l = s * (e' - e) := by
  have hne' : ev.lo ≤ ev.hi := he.lo_le_hi
  have hhi : ev.Mem (toR ev.hi) := ⟨toR_le_toR.mpr hne', le_rfl⟩
  have hlo' : 0 ≤ toR ev.lo := toR_nonneg.mpr hlo
  have he0 : 0 ≤ e := hlo'.trans he.1
  have he0' : 0 ≤ e' := hlo'.trans he'.1
  have hhi1 : toR ev.hi < 1 := by
    have := (toR_pos.mpr h2).trans_le (mem_sub mem_oneI hhi).1; linarith
  have hlh1 : l * toR ev.hi < 1 := by
    have := (toR_pos.mpr h1).trans_le (mem_sub mem_oneI (mem_mul hl hhi)).1; linarith
  have hhi0 : 0 ≤ toR ev.hi := he0.trans he.2
  have hle1 : l * e < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left he.2 hl0) hlh1
  have hle1' : l * e' < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left he'.2 hl0) hlh1
  have he1 : e < 1 := lt_of_le_of_lt he.2 hhi1
  have he1' : e' < 1 := lt_of_le_of_lt he'.2 hhi1
  -- the divided differences
  have hD : HasSum (fun n : ℕ => kc l n * sig e e' n) ((kR e' l - kR e l) / (e' - e)) := by
    have hd := (hasSum_kR he0' he1' hl0 hle1').sub (hasSum_kR he0 he1 hl0 hle1)
    have hden : e' - e ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have := hd.div_const (e' - e)
    convert this using 1
    funext n
    rw [← mul_sub, ← sig_mul e e' n]; field_simp
  set s := (kR e' l - kR e l) / (e' - e) with hs
  refine ⟨s, ?_, by rw [hs]; field_simp [sub_ne_zero.mpr (Ne.symm hne)]⟩
  -- head and tail
  have hB : HasSum (fun n : ℕ => (l ^ (n + (mK + 1) + 1) + 1) * toR ev.hi ^ (n + mK))
      (l * l * (l * toR ev.hi) ^ mK / (1 - l * toR ev.hi) + toR ev.hi ^ mK / (1 - toR ev.hi)) := by
    have hA := (hasSum_geometric_of_lt_one (by positivity) hlh1).mul_left (l * l * (l * toR ev.hi) ^ mK)
    have hC := (hasSum_geometric_of_lt_one hhi0 hhi1).mul_left (toR ev.hi ^ mK)
    convert hA.add hC using 1
    · funext n; ring
    all_goals (try (have h1' : (1 - l * toR ev.hi) ≠ 0 := by linarith); try field_simp)
  have hT := abs_tail_le hD (mK + 1) (b := fun n => (l ^ (n + (mK + 1) + 1) + 1) * toR ev.hi ^ (n + mK))
    (fun n => by
      rw [abs_mul]
      have hs0 := sig_bounds hlo' he.1 he.2 he'.1 he'.2 (n + (mK + 1))
      rw [show n + (mK + 1) - 1 = n + mK by omega] at hs0
      have hlo0 : (0 : ℝ) ≤ ((n + (mK + 1) : ℕ) : ℝ) * toR ev.lo ^ (n + mK) := by positivity
      have hsig : |sig e e' (n + (mK + 1))| ≤ ((n + (mK + 1) : ℕ) : ℝ) * toR ev.hi ^ (n + mK) := by
        rw [abs_of_nonneg (hlo0.trans hs0.1)]; exact hs0.2
      have hk := abs_kc_mul_le hl0 (n + (mK + 1))
      have hp : (0 : ℝ) ≤ toR ev.hi ^ (n + mK) := pow_nonneg hhi0 _
      have hka := abs_nonneg (kc l (n + (mK + 1)))
      push_cast at hsig hk ⊢
      calc |kc l (n + (mK + 1))| * |sig e e' (n + (mK + 1))|
          ≤ |kc l (n + (mK + 1))| * (((n : ℝ) + (mK + 1)) * toR ev.hi ^ (n + mK)) :=
            mul_le_mul_of_nonneg_left hsig hka
        _ ≤ (|kc l (n + (mK + 1))| * ((n : ℝ) + (mK + 1) + 1)) * toR ev.hi ^ (n + mK) := by
            nlinarith
        _ ≤ (l ^ (n + (mK + 1) + 1) + 1) * toR ev.hi ^ (n + mK) :=
            mul_le_mul_of_nonneg_right (by linarith) hp)
    hB
  have hsplit : s = ∑ n ∈ Finset.range (mK + 1), kc l n * sig e e' n +
      (s - ∑ n ∈ Finset.range (mK + 1), kc l n * sig e e' n) := by ring
  rw [hsplit]
  refine kPart_mem_of_head hl hlo hne' h1 h2 ?_ hT
  -- the head
  rw [Finset.sum_range_succ']
  have h0 : sig e e' 0 = 0 := by simp [sig]
  rw [h0, mul_zero, add_zero]
  have hw : ∀ k, (ipow ev k).Mem (sig e e' (k + 1) / ((k : ℝ) + 1)) := fun k => by
    have hs0 := sig_bounds hlo' he.1 he.2 he'.1 he'.2 (k + 1)
    rw [show k + 1 - 1 = k by omega] at hs0
    push_cast at hs0
    have hk : (0 : ℝ) < k + 1 := by positivity
    refine mem_ipow_of_between hlo k ?_ ?_ hne'
    · rw [le_div_iff₀ hk, mul_comm]; exact hs0.1
    · rw [div_le_iff₀ hk, mul_comm]; exact hs0.2
  have := (kpartLoop_mem hl (fun k => sig e e' (k + 1) / ((k : ℝ) + 1)) hw mK).1
  convert this using 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The `λ`-slope of the kernel: `1/ξ` with `ξ` between `1 + λe` and `1 + λ'e`. -/
theorem kernel_slope_l {lv ev : Ival} {l l' e : ℝ} (hl : lv.Mem l) (hl' : lv.Mem l') (he : ev.Mem e)
    (hl0 : 0 ≤ toR lv.lo) (he0 : 0 ≤ e) (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo)
    (h3 : 0 < (add oneI (mul lv ev)).lo) :
    ∃ s, (div oneI (add oneI (mul lv ev))).Mem s ∧ kR e l' - kR e l = s * (l' - l) := by
  have hle := mem_sub mem_oneI (mem_mul hl he)
  have hle' := mem_sub mem_oneI (mem_mul hl' he)
  have hlb : 0 ≤ l := hl0.trans hl.1
  have hlb' : 0 ≤ l' := hl0.trans hl'.1
  have he1 : e < 1 := by have := (toR_pos.mpr h2).trans_le (mem_sub mem_oneI he).1; linarith
  have hle1 : l * e < 1 := by have := (toR_pos.mpr h1).trans_le hle.1; linarith
  have hle1' : l' * e < 1 := by have := (toR_pos.mpr h1).trans_le hle'.1; linarith
  rcases he0.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨1, ?_, by rw [kR_zero, kR_zero]; ring⟩
    have := mem_div mem_oneI (mem_add mem_oneI (mem_mul hl he)) h3
    simpa using this
  · have hA : 0 < 1 + l * e := by positivity
    have hA' : 0 < 1 + l' * e := by positivity
    obtain ⟨ξ, hξ1, hξ2, hξ⟩ := log_sub_eq hA hA'
    have hξ0 : 0 < ξ := lt_of_lt_of_le (lt_min hA hA') hξ1
    -- ξ = 1 + θ e with θ between l and l'
    have hθ : (add oneI (mul lv ev)).Mem ξ := by
      set θ := (ξ - 1) / e with hθdef
      have hξθ : ξ = 1 + θ * e := by rw [hθdef]; field_simp; ring
      have hθl : lv.Mem θ := by
        refine Compute.Ival.Mem.between hl hl' ?_ ?_
        · rw [hθdef, le_div_iff₀ hpos]
          rcases le_total l l' with h | h
          · rw [min_eq_left h]; rw [min_eq_left (by nlinarith)] at hξ1; linarith
          · rw [min_eq_right h]; rw [min_eq_right (by nlinarith)] at hξ1; linarith
        · rw [hθdef, div_le_iff₀ hpos]
          rcases le_total l l' with h | h
          · rw [max_eq_right h]; rw [max_eq_right (by nlinarith)] at hξ2; linarith
          · rw [max_eq_left h]; rw [max_eq_left (by nlinarith)] at hξ2; linarith
      rw [hξθ]; exact mem_add mem_oneI (mem_mul hθl he)
    refine ⟨1 / ξ, mem_div mem_oneI hθ h3, ?_⟩
    have k1 := kR_mul he0 he1 hlb hle1
    have k2 := kR_mul he0 he1 hlb' hle1'
    have e1 : kR e l' - kR e l = (Real.log (1 + l' * e) - Real.log (1 + l * e)) / e := by
      rw [eq_div_iff hpos.ne']; linear_combination k2 - k1
    rw [e1, hξ]; field_simp; ring

/-- `kPart` contains the slope-series head at `w = eᵏ` (so it is nonempty). -/
theorem kPart_nonempty {lv ev : Ival} {l e : ℝ} (hl : lv.Mem l) (he : ev.Mem e) (hl0 : 0 ≤ l)
    (hlo : 0 ≤ ev.lo) (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo) :
    ∃ s, (kPart lv ev).Mem s := by
  have hH := (kpartLoop_mem hl (fun k => e ^ k) (fun k => ipow_mem he k) mK).1
  have hne : ev.lo ≤ ev.hi := he.lo_le_hi
  have hhi : ev.Mem (toR ev.hi) := ⟨toR_le_toR.mpr hne, le_rfl⟩
  have hhi1 : toR ev.hi < 1 := by
    have := (toR_pos.mpr h2).trans_le (mem_sub mem_oneI hhi).1; linarith
  have hlh1 : l * toR ev.hi < 1 := by
    have := (toR_pos.mpr h1).trans_le (mem_sub mem_oneI (mem_mul hl hhi)).1; linarith
  have hhi0 : 0 ≤ toR ev.hi := (toR_nonneg.mpr hlo).trans hhi.1
  refine ⟨_ + 0, kPart_mem_of_head hl hlo hne h1 h2 hH ?_⟩
  rw [abs_zero]
  have : 0 < 1 - l * toR ev.hi := by linarith
  have : 0 < 1 - toR ev.hi := by linarith
  positivity

end Erdos993Lean.Analytic.O2.Cert

namespace Erdos993Lean.Analytic.O2.Cert

open Erdos993Lean.Analytic.TailCert Erdos993Lean.Analytic.TailCert.Compute
open Erdos993Lean.Analytic.O2.Cert.Compute

/-- The chain rule for slopes of `F(U, V)`. -/
theorem sl_chain {F : ℝ → ℝ → ℝ} {U V : ℝ → ℝ} {P Q IU IV S : Ival} (hU : Sl IU S U) (hV : Sl IV S V)
    (hFu : ∀ a b, S.Mem a → S.Mem b → ∃ s, P.Mem s ∧ F (U b) (V b) - F (U a) (V b) = s * (U b - U a))
    (hFv : ∀ a b, S.Mem a → S.Mem b → ∃ s, Q.Mem s ∧ F (U a) (V b) - F (U a) (V a) = s * (V b - V a)) :
    Sl (add (mul P IU) (mul Q IV)) S (fun t => F (U t) (V t)) := by
  intro a b ha hb hab
  obtain ⟨sU, hsU, eU⟩ := hU a b ha hb hab
  obtain ⟨sV, hsV, eV⟩ := hV a b ha hb hab
  obtain ⟨s1, hs1, e1⟩ := hFu a b ha hb
  obtain ⟨s2, hs2, e2⟩ := hFv a b ha hb
  refine ⟨s1 * sU + s2 * sV, mem_add (mem_mul hs1 hsU) (mem_mul hs2 hsV), ?_⟩
  linear_combination e1 + e2 + s1 * eU + s2 * eV

/-- The `e`-slope of the kernel between any two points (a member of `kPart` also when `e = e'`). -/
theorem kernel_slope_e' {lv ev : Ival} {l e e' : ℝ} (hl : lv.Mem l) (he : ev.Mem e) (he' : ev.Mem e')
    (hl0 : 0 ≤ l) (hlo : 0 ≤ ev.lo) (h1 : 0 < (sub oneI (mul lv ev)).lo) (h2 : 0 < (sub oneI ev).lo) :
    ∃ s, (kPart lv ev).Mem s ∧ kR e' l - kR e l = s * (e' - e) := by
  by_cases h : e = e'
  · subst h
    obtain ⟨s, hs⟩ := kPart_nonempty hl he hl0 hlo h1 h2
    exact ⟨s, hs, by ring⟩
  · exact kernel_slope_e hl he he' hl0 hlo h1 h2 h

/-- **The kernel dual number encloses `k(e, λ)`.** -/
theorem de_kernel {L X : Ival} {fe fl : ℝ → ℝ → ℝ} {e lam : DN} (he : DE L X fe e) (hl : DE L X fl lam) :
    DE L X (fun l x => kR (fe l x) (fl l x)) (kernel e lam) := by
  intro hok
  simp only [kernel, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hoke, hokl⟩, hlo⟩, hlv⟩, h1⟩, h2⟩, h3⟩ := hok
  have he := he hoke
  have hl := hl hokl
  have hlv0 : 0 ≤ toR lam.v.lo := (toR_pos.mpr hlv).le
  have hlpos : ∀ l x, L.Mem l → X.Mem x → 0 ≤ fl l x := fun l x hl' hx => hlv0.trans (hl.val l x hl' hx).1
  have hepos : ∀ l x, L.Mem l → X.Mem x → 0 ≤ fe l x :=
    fun l x hl' hx => (toR_nonneg.mpr hlo).trans (he.val l x hl' hx).1
  refine ⟨fun l x hl' hx => kernel_val (hl.val l x hl' hx) (he.val l x hl' hx) (hlpos l x hl' hx)
      (hepos l x hl' hx) h1 h2, fun x hx => ?_, fun l hl' => ?_⟩
  · exact sl_chain (F := fun a b => kR a b) (he.sl0 x hx) (hl.sl0 x hx)
      (fun a b ha hb => kernel_slope_e' (hl.val b x hb hx) (he.val a x ha hx) (he.val b x hb hx)
        (hlpos b x hb hx) hlo h1 h2)
      (fun a b ha hb => kernel_slope_l (hl.val a x ha hx) (hl.val b x hb hx) (he.val a x ha hx) hlv0
        (hepos a x ha hx) h1 h2 h3)
  · exact sl_chain (F := fun a b => kR a b) (he.sl1 l hl') (hl.sl1 l hl')
      (fun a b ha hb => kernel_slope_e' (hl.val l b hl' hb) (he.val l a hl' ha) (he.val l b hl' hb)
        (hlpos l b hl' hb) hlo h1 h2)
      (fun a b ha hb => kernel_slope_l (hl.val l a hl' ha) (hl.val l b hl' hb) (he.val l a hl' ha) hlv0
        (hepos l a hl' ha) h1 h2 h3)

end Erdos993Lean.Analytic.O2.Cert
