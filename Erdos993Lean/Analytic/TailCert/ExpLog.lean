import Mathlib
import Erdos993Lean.Analytic.TailCert.IvalSound

/-!
# The enclosures of `exp`, `log` and `√`: soundness (lane A10)

Campaign `ProofRuns/2026-09-28_analytic_large_n`, lane A10.  Soundness of `expPt`, `logPt`, `sqrtPt`
(`Erdos993Lean/Analytic/TailCert/Compute/Ival.lean`).

* `mem_expPt n : (expPt n).Mem (exp (toR n))`: the argument is halved `K` times into `[-1/2, 1/2]`
  (`abs_toR_le_of_expShift`), the Taylor loop encloses the partial sum (`expLoop_mem`), Mathlib's
  `Real.exp_bound` bounds the remainder by `rExp` (`rExp_bound`), and `K` squarings give
  `exp(2^K y)` (`sqrIter_mem`);  `mem_expI` (monotone extension).
* `mem_logPt (0 < n) : (logPt n).Mem (log (toR n))`: `n = 2^b m`, `m ∈ [1, 2)`,
  `u = (m − 1)/(m + 1) ∈ [0, 1/3]`, `log m = log(1 + u) − log(1 − u)` (Mathlib's
  `Real.hasSum_log_sub_log_of_abs_lt_one`); the partial sum is a lower bound and the tail is at most
  the geometric bound `2 u^(2N+1)/((2N+1)(1 − u²))` (`atanh_tail`, `mem_atanh2`); `log 2 ∈ log2I`;
  `logI_lo_le`, `le_logI_hi`, `mem_logI` (monotone extension).
* `mem_sqrtPt (0 ≤ n)`: the Newton candidate is checked (`s² ≤ N ≤ (s+1)²`); `mem_sqrtI`.

All results use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Erdos993Lean.Analytic.TailCert

open Compute

/-! ## The exponential -/

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fact, Nat.factorial, ih]

/-- The Taylor loop: `T_i ∋ y^i/i!` and `S_i ∋ ∑_{k ≤ i} y^k/k!`. -/
theorem expLoop_mem {Y : Ival} {y : ℝ} (hY : Y.Mem y) (i : ℕ) :
    (expLoop Y i).1.Mem (y ^ i / i.factorial) ∧
      (expLoop Y i).2.Mem (∑ k ∈ Finset.range (i + 1), y ^ k / k.factorial) := by
  induction i with
  | zero =>
    simp only [expLoop, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, zero_add,
      Finset.sum_range_one]
    rw [← toR_one]
    exact ⟨mem_pt _, mem_pt _⟩
  | succ i ih =>
    have hT := mem_divNat (mem_mul ih.1 hY) (Nat.succ_pos i)
    have heq : y ^ i / i.factorial * y / ((i + 1 : ℕ) : ℝ) = y ^ (i + 1) / (i + 1).factorial := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [heq] at hT
    refine ⟨hT, ?_⟩
    have hS := mem_add ih.2 hT
    rw [Finset.sum_range_succ]
    exact hS

theorem rExp_bound : ((1 : ℝ) / 2) ^ nExp * ((nExp + 1 : ℕ) / ((nExp.factorial : ℕ) * nExp : ℝ)) ≤
    toR rExp := by
  have hd : (0 : ℤ) < ((2 ^ nExp * fact nExp * nExp : ℕ) : ℤ) := by decide
  have h := le_cdiv (((nExp + 1 : ℕ) : ℤ) * one) hd
  unfold rExp toR
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right h two_pow_prec_pos.le)
  rw [fact_eq, one_eq, div_pow, one_pow]
  push_cast
  field_simp

theorem abs_toR_le_of_expShift (n : ℤ) :
    |toR n| ≤ 2 ^ (expShift n) / 2 := by
  have h1 : n.natAbs < 2 ^ (n.natAbs.log2 + 1) := Nat.lt_log2_self
  have h2 : n.natAbs.log2 + 1 ≤ prec - 1 + expShift n := by
    unfold expShift; unfold prec; omega
  have h3 : (n.natAbs : ℝ) ≤ 2 ^ (prec - 1 + expShift n) := by
    have : n.natAbs ≤ 2 ^ (prec - 1 + expShift n) :=
      h1.le.trans (Nat.pow_le_pow_right (by norm_num) h2)
    exact_mod_cast this
  have habs : |(n : ℝ)| = (n.natAbs : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  unfold toR
  rw [abs_div, abs_of_pos two_pow_prec_pos, div_le_div_iff₀ two_pow_prec_pos (by norm_num), habs]
  calc (n.natAbs : ℝ) * 2 ≤ 2 ^ (prec - 1 + expShift n) * 2 := by nlinarith
    _ = 2 ^ expShift n * 2 ^ prec := by
        rw [← pow_succ, ← pow_add]
        congr 1
        unfold prec
        omega

/-- `K` squarings: `E ∋ e^w`, `0 ≤ E.lo` give `sqrIter K E ∋ e^{2^K w}`. -/
theorem sqrIter_mem : ∀ (K : ℕ) {E : Ival} {w : ℝ}, 0 ≤ E.lo → E.Mem (Real.exp w) →
    (sqrIter K E).Mem (Real.exp (w * 2 ^ K))
  | 0, E, w, _, hE => by simpa [sqrIter] using hE
  | K + 1, E, w, h0, hE => by
    have hsq := mem_sqr hE h0
    have hsq0 : 0 ≤ (sqr E).lo := by
      unfold sqr fdivP
      rw [Int.shiftRight_eq_div_pow]
      exact Int.ediv_nonneg (mul_self_nonneg _) (by positivity)
    rw [← Real.exp_nat_mul] at hsq
    have := sqrIter_mem K hsq0 (w := (2 : ℕ) * w) (by simpa using hsq)
    simp only [sqrIter]
    convert this using 2
    push_cast
    ring

/-- **The enclosure of `exp`**: `exp (n / 2^prec) ∈ expPt n`. -/
theorem mem_expPt (n : ℤ) : (expPt n).Mem (Real.exp (toR n)) := by
  set K := expShift n with hK
  set y : ℝ := toR n / 2 ^ K with hy
  have hpowK : (0 : ℝ) < 2 ^ K := by positivity
  -- the reduced argument
  have hY : (⟨n >>> K, -((-n) >>> K)⟩ : Ival).Mem y := by
    constructor
    · show toR (n >>> K) ≤ y
      rw [Int.shiftRight_eq_div_pow, hy]
      unfold toR
      rw [div_div, mul_comm, ← div_div]
      refine div_le_div_of_nonneg_right ?_ two_pow_prec_pos.le
      have := fdiv_le n (b := ((2 ^ K : ℕ) : ℤ)) (by positivity)
      unfold fdiv at this
      simpa using this
    · show y ≤ toR (-((-n) >>> K))
      rw [Int.shiftRight_eq_div_pow, hy]
      unfold toR
      rw [div_div, mul_comm, ← div_div]
      refine div_le_div_of_nonneg_right ?_ two_pow_prec_pos.le
      have := le_cdiv n (b := ((2 ^ K : ℕ) : ℤ)) (by positivity)
      unfold cdiv at this
      simpa using this
  have hyabs : |y| ≤ 1 / 2 := by
    rw [hy, abs_div, abs_of_pos hpowK, div_le_iff₀ hpowK]
    have := abs_toR_le_of_expShift n
    rw [← hK] at this
    linarith
  -- the Taylor polynomial and the remainder
  have hS := (expLoop_mem hY (nExp - 1)).2
  rw [show nExp - 1 + 1 = nExp by rfl] at hS
  have hrem : |Real.exp y - ∑ k ∈ Finset.range nExp, y ^ k / k.factorial| ≤ toR rExp := by
    have hb := Real.exp_bound (x := y) (by linarith [hyabs]) (n := nExp) (by decide)
    refine hb.trans (le_trans ?_ rExp_bound)
    have hpow : |y| ^ nExp ≤ (1 / 2) ^ nExp := pow_le_pow_left₀ (abs_nonneg y) hyabs nExp
    refine mul_le_mul hpow ?_ (by positivity) (by positivity)
    push_cast
    exact le_rfl
  have hE0 : (⟨max ((expLoop ⟨n >>> K, -((-n) >>> K)⟩ (nExp - 1)).2.lo - rExp) 0,
      (expLoop ⟨n >>> K, -((-n) >>> K)⟩ (nExp - 1)).2.hi + rExp⟩ : Ival).Mem (Real.exp y) := by
    constructor
    · show toR (max _ 0) ≤ Real.exp y
      rw [toR_max, toR_zero, toR_sub]
      refine max_le ?_ (Real.exp_pos y).le
      have := (abs_le.mp hrem).1
      linarith [hS.1]
    · show Real.exp y ≤ toR (_ + rExp)
      rw [toR_add]
      have := (abs_le.mp hrem).2
      linarith [hS.2]
  have h0 : 0 ≤ (⟨max ((expLoop ⟨n >>> K, -((-n) >>> K)⟩ (nExp - 1)).2.lo - rExp) 0,
      (expLoop ⟨n >>> K, -((-n) >>> K)⟩ (nExp - 1)).2.hi + rExp⟩ : Ival).lo := le_max_right _ _
  have := sqrIter_mem K h0 hE0
  have hyK : y * 2 ^ K = toR n := by rw [hy]; field_simp
  rw [hyK] at this
  exact this

/-- `exp x ∈ expI A` for `x ∈ A`. -/
theorem mem_expI {A : Ival} {x : ℝ} (hA : A.Mem x) : (expI A).Mem (Real.exp x) :=
  ⟨(mem_expPt A.lo).1.trans (Real.exp_le_exp.mpr hA.1),
    (Real.exp_le_exp.mpr hA.2).trans (mem_expPt A.hi).2⟩

/-! ## The logarithm -/

/-- The `atanh` loop: `T_k ∋ u^(2k+1)` and `S_k ∋ ∑_{i<k} 2 u^(2i+1)/(2i+1)`. -/
theorem atanhLoop_mem {U U2 : Ival} {u : ℝ} (hU : U.Mem u) (hU2 : U2.Mem (u * u)) (k : ℕ) :
    (atanhLoop U U2 k).1.Mem (u ^ (2 * k + 1)) ∧
      (atanhLoop U U2 k).2.Mem (∑ i ∈ Finset.range k, 2 * (1 / (2 * (i : ℝ) + 1)) * u ^ (2 * i + 1)) := by
  induction k with
  | zero =>
    simp only [atanhLoop, mul_zero, zero_add, pow_one, Finset.range_zero, Finset.sum_empty]
    exact ⟨hU, by rw [← toR_zero]; exact mem_pt _⟩
  | succ k ih =>
    refine ⟨?_, ?_⟩
    · have := mem_mul ih.1 hU2
      have heq : u ^ (2 * k + 1) * (u * u) = u ^ (2 * (k + 1) + 1) := by ring
      rw [heq] at this
      exact this
    · have hT := mem_divNat (mem_mulNat ih.1 2) (k := 2 * k + 1) (by omega)
      have hS := mem_add ih.2 hT
      rw [Finset.sum_range_succ]
      convert hS using 2
      push_cast
      field_simp

theorem rLog_bound : 2 * (1 / 3 : ℝ) ^ (2 * nLog + 1) / ((2 * nLog + 1) * (1 - (1 / 3) ^ 2)) ≤
    toR rLog := by
  have hd : (0 : ℤ) < ((3 ^ (2 * nLog + 1) * (2 * nLog + 1) * 8 : ℕ) : ℤ) := by decide
  have h := le_cdiv (18 * one) hd
  unfold rLog toR
  refine le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right h two_pow_prec_pos.le)
  rw [one_eq, div_pow, one_pow]
  push_cast
  field_simp
  ring

/-- The tail of the `atanh` series: `∑_{k ≥ N} 2u^(2k+1)/(2k+1) ≤ 2 u^(2N+1)/((2N+1)(1 − u²))`. -/
theorem atanh_tail {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) (N : ℕ) :
    Real.log (1 + u) - Real.log (1 - u) ≤
      ∑ i ∈ Finset.range N, 2 * (1 / (2 * (i : ℝ) + 1)) * u ^ (2 * i + 1) +
        2 * u ^ (2 * N + 1) / ((2 * N + 1) * (1 - u ^ 2)) := by
  have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hu1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have htail := (hasSum_nat_add_iff' N).mpr hS
  set f : ℕ → ℝ := fun k => 2 * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1) with hf
  have hu2 : u ^ 2 < 1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one (sq_nonneg u) hu2).mul_left
    (2 * u ^ (2 * N + 1) / (2 * N + 1))
  have hle : ∀ k : ℕ, f (k + N) ≤ 2 * u ^ (2 * N + 1) / (2 * N + 1) * (u ^ 2) ^ k := by
    intro k
    simp only [hf]
    have hk : (2 * (N : ℝ) + 1) ≤ 2 * ((k + N : ℕ) : ℝ) + 1 := by push_cast; linarith [k.cast_nonneg (α := ℝ)]
    have hpos : (0 : ℝ) < 2 * N + 1 := by positivity
    have hpow : u ^ (2 * (k + N) + 1) = u ^ (2 * N + 1) * (u ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; congr 1; ring
    rw [hpow]
    have hu' : 0 ≤ u ^ (2 * N + 1) * (u ^ 2) ^ k := by positivity
    calc 2 * (1 / (2 * ((k + N : ℕ) : ℝ) + 1)) * (u ^ (2 * N + 1) * (u ^ 2) ^ k)
        ≤ 2 * (1 / (2 * (N : ℝ) + 1)) * (u ^ (2 * N + 1) * (u ^ 2) ^ k) := by
          gcongr
      _ = 2 * u ^ (2 * N + 1) / (2 * N + 1) * (u ^ 2) ^ k := by ring
  have := hasSum_le hle htail hgeo
  have hsub : 1 - u ^ 2 ≠ 0 := by linarith
  have heq : 2 * u ^ (2 * N + 1) / (2 * N + 1) * (1 - u ^ 2)⁻¹ =
      2 * u ^ (2 * N + 1) / ((2 * N + 1) * (1 - u ^ 2)) := by
    field_simp
  rw [heq] at this
  linarith

/-- **The `atanh` enclosure**: `log((1 + u)/(1 − u)) ∈ atanh2 U` for `u ∈ U`, `0 ≤ u ≤ 1/3`. -/
theorem mem_atanh2 {U : Ival} {u : ℝ} (hU : U.Mem u) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 3) :
    (atanh2 U).Mem (Real.log ((1 + u) / (1 - u))) := by
  have hloop := (atanhLoop_mem hU (mem_mul hU hU) nLog).2
  have hlt : u < 1 := by linarith
  have hlog : Real.log ((1 + u) / (1 - u)) = Real.log (1 + u) - Real.log (1 - u) :=
    Real.log_div (by linarith) (by linarith)
  have habs : |u| < 1 := by rw [abs_of_nonneg hu0]; exact hlt
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hlow : ∑ i ∈ Finset.range nLog, 2 * (1 / (2 * (i : ℝ) + 1)) * u ^ (2 * i + 1) ≤
      Real.log (1 + u) - Real.log (1 - u) :=
    sum_le_hasSum _ (fun i _ => by positivity) hS
  have hup := atanh_tail hu0 hlt nLog
  have htail : 2 * u ^ (2 * nLog + 1) / ((2 * nLog + 1) * (1 - u ^ 2)) ≤ toR rLog := by
    refine le_trans ?_ rLog_bound
    have h1 : u ^ (2 * nLog + 1) ≤ (1 / 3) ^ (2 * nLog + 1) := pow_le_pow_left₀ hu0 hu1 _
    have h2 : (1 - (1 / 3 : ℝ) ^ 2) ≤ 1 - u ^ 2 := by nlinarith
    have hpos : (0 : ℝ) < (2 * nLog + 1) * (1 - (1 / 3) ^ 2) := by norm_num [nLog]
    rw [div_le_div_iff₀ (by nlinarith) hpos]
    have h3 : (0 : ℝ) < 2 * nLog + 1 := by positivity
    nlinarith [mul_le_mul h1 (mul_le_mul_of_nonneg_left h2 h3.le) (by positivity) (by positivity)]
  rw [hlog]
  unfold atanh2
  simp only
  constructor
  · exact hloop.1.trans hlow
  · show _ ≤ toR (_ + rLog)
    rw [toR_add]
    linarith [hloop.2]

theorem mem_log2I : log2I.Mem (Real.log 2) := by
  have h := mem_atanh2 (mem_ofRat (1 / 3)) (by norm_num) (by norm_num)
  have h2 : (1 + ((1 / 3 : ℚ) : ℝ)) / (1 - ((1 / 3 : ℚ) : ℝ)) = 2 := by norm_num
  rw [h2] at h
  exact h

/-- **The enclosure of `log`**: `log (n / 2^prec) ∈ logPt n` for `n > 0`. -/
theorem mem_logPt {n : ℤ} (hn : 0 < n) : (logPt n).Mem (Real.log (toR n)) := by
  set b := Nat.log2 n.toNat with hb
  have hnat : n.toNat ≠ 0 := by omega
  have hD1 : 2 ^ b ≤ n.toNat := Nat.log2_self_le hnat
  have hD2 : n.toNat < 2 ^ (b + 1) := Nat.lt_log2_self
  have hn' : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn.le
  set D : ℤ := ((1 <<< b : ℕ) : ℤ) with hDdef
  have hD : D = 2 ^ b := by rw [hDdef, Nat.one_shiftLeft]; push_cast; rfl
  have hDn : D ≤ n := by rw [hD, ← hn']; exact_mod_cast hD1
  have hnD : n < 2 * D := by
    rw [hD, ← hn']
    have : n.toNat < 2 * 2 ^ b := by rw [← pow_succ']; exact hD2
    exact_mod_cast this
  have hDpos : (0 : ℤ) < D := by rw [hD]; positivity
  -- the reduced variable
  set u : ℝ := ((n - D : ℤ) : ℝ) / ((n + D : ℤ) : ℝ) with hu
  have hnDpos : (0 : ℤ) < n + D := by omega
  have hnDR : (0 : ℝ) < ((n + D : ℤ) : ℝ) := by exact_mod_cast hnDpos
  have hU : (⟨fdiv ((n - D) * one) (n + D), cdiv ((n - D) * one) (n + D)⟩ : Ival).Mem u := by
    have h1 := toR_fdiv_le (n - D) (n + D) hnDpos
    have h2 := le_toR_cdiv (n - D) (n + D) hnDpos
    have hq : toR (n - D) / toR (n + D) = u := by
      rw [hu]; unfold toR; field_simp
    rw [hq] at h1 h2
    exact ⟨h1, h2⟩
  have hu0 : 0 ≤ u := by
    rw [hu]; exact div_nonneg (by exact_mod_cast (by omega : (0 : ℤ) ≤ n - D)) hnDR.le
  have hu1 : u ≤ 1 / 3 := by
    rw [hu, div_le_iff₀ hnDR]
    have : (3 : ℤ) * (n - D) ≤ n + D := by omega
    have : (3 : ℝ) * ((n - D : ℤ) : ℝ) ≤ ((n + D : ℤ) : ℝ) := by exact_mod_cast this
    linarith
  have hA := mem_atanh2 hU hu0 hu1
  -- `(1 + u)/(1 − u) = n/D`
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hratio : (1 + u) / (1 - u) = (n : ℝ) / D := by
    rw [hu]
    push_cast
    have h1 : (n : ℝ) + D ≠ 0 := by push_cast at hnDR; linarith
    have h2 : (n : ℝ) + D - (n - D) ≠ 0 := by linarith
    field_simp
    ring
  rw [hratio] at hA
  have hL := mem_mulInt mem_log2I ((b : ℤ) - (prec : ℤ))
  have hsum := mem_add hL hA
  -- `log (n / 2^prec) = (b − prec) log 2 + log (n / D)`
  have hlog : Real.log (toR n) = Real.log 2 * (((b : ℤ) - (prec : ℤ) : ℤ) : ℝ) +
      Real.log ((n : ℝ) / D) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : toR n = (2 : ℝ) ^ b / 2 ^ prec * ((n : ℝ) / D) := by
      unfold toR; rw [hD]; push_cast; field_simp
    rw [hsplit, Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity)
      (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  rw [hlog]
  exact hsum

/-- `toR (logI A).lo ≤ log x` for `x ∈ A`, `0 < A.lo`. -/
theorem logI_lo_le {A : Ival} {x : ℝ} (hA : A.Mem x) (hpos : 0 < A.lo) :
    toR (logI A).lo ≤ Real.log x :=
  (mem_logPt hpos).1.trans (Real.log_le_log (toR_pos.mpr hpos) hA.1)

/-- `log x ≤ toR (logI A).hi` for `x ∈ A`, `0 < x`. -/
theorem le_logI_hi {A : Ival} {x : ℝ} (hA : A.Mem x) (hx : 0 < x) :
    Real.log x ≤ toR (logI A).hi :=
  (Real.log_le_log hx hA.2).trans (mem_logPt (toR_pos.mp (hx.trans_le hA.2))).2

theorem mem_logI {A : Ival} {x : ℝ} (hA : A.Mem x) (hpos : 0 < A.lo) : (logI A).Mem (Real.log x) :=
  ⟨logI_lo_le hA hpos, le_logI_hi hA ((toR_pos.mpr hpos).trans_le hA.1)⟩

/-! ## The square root -/

theorem one_toNat : one.toNat = 2 ^ prec := by decide

/-- **The enclosure of `√`**: `√(n / 2^prec) ∈ sqrtPt n` for `n ≥ 0`. -/
theorem mem_sqrtPt {n : ℤ} (hn : 0 ≤ n) : (sqrtPt n).Mem (Real.sqrt (toR n)) := by
  unfold sqrtPt
  set N := n.toNat * one.toNat with hN
  set s := isqrtNewton 400 N N
  have hn' : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn
  have hNR : (N : ℝ) / 2 ^ prec / 2 ^ prec = toR n := by
    rw [hN, one_toNat]; unfold toR; push_cast
    rw [show ((n.toNat : ℕ) : ℝ) = (n : ℝ) by exact_mod_cast hn']
    field_simp
  have hP := two_pow_prec_pos
  constructor
  · show toR (if s * s ≤ N then (s : ℤ) else 0) ≤ _
    split_ifs with h
    · apply Real.le_sqrt_of_sq_le
      rw [← hNR]
      unfold toR
      have : ((s * s : ℕ) : ℝ) ≤ N := by exact_mod_cast h
      push_cast at this
      rw [div_pow, div_div, le_div_iff₀ (by positivity)]
      calc (s : ℝ) ^ 2 / (2 ^ prec) ^ 2 * (2 ^ prec * 2 ^ prec) = (s : ℝ) * s := by
            field_simp
        _ ≤ N := this
    · rw [toR_zero]; exact Real.sqrt_nonneg _
  · show _ ≤ toR (if N ≤ (s + 1) * (s + 1) then ((s + 1 : ℕ) : ℤ) else ((N + 1 : ℕ) : ℤ))
    split_ifs with h
    · apply Real.sqrt_le_iff.mpr
      refine ⟨by unfold toR; positivity, ?_⟩
      rw [← hNR]
      unfold toR
      have : (N : ℝ) ≤ ((s + 1) * (s + 1) : ℕ) := by exact_mod_cast h
      push_cast at this ⊢
      rw [div_pow, div_div, div_le_iff₀ (by positivity)]
      calc (N : ℝ) ≤ ((s : ℝ) + 1) * ((s : ℝ) + 1) := this
        _ = ((s : ℝ) + 1) ^ 2 / (2 ^ prec) ^ 2 * (2 ^ prec * 2 ^ prec) := by field_simp
    · apply Real.sqrt_le_iff.mpr
      refine ⟨by unfold toR; positivity, ?_⟩
      rw [← hNR]
      unfold toR
      push_cast
      rw [div_pow, div_div, div_le_iff₀ (by positivity)]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have h1 : (1 : ℝ) ≤ 2 ^ prec := one_le_pow₀ (by norm_num)
      calc (N : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
        _ = ((N : ℝ) + 1) ^ 2 / (2 ^ prec) ^ 2 * (2 ^ prec * 2 ^ prec) := by field_simp

theorem mem_sqrtI {A : Ival} {x : ℝ} (hA : A.Mem x) (h0 : 0 ≤ A.lo) : (sqrtI A).Mem (Real.sqrt x) :=
  ⟨(mem_sqrtPt h0).1.trans (Real.sqrt_le_sqrt hA.1),
    (Real.sqrt_le_sqrt hA.2).trans (mem_sqrtPt (h0.trans hA.lo_le_hi)).2⟩

end Erdos993Lean.Analytic.TailCert
