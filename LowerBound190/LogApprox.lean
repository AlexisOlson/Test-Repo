import LowerBound190.Certificate
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace stoch_to_det.LowerBound190.LogApprox

open Finset
open scoped BigOperators
open Certificate

noncomputable def logTaylorReal (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ (j + 1) * x ^ j / j

lemma coe_logTaylorReal (n : ℕ) (x : ℝ) :
    (logTaylorReal n x : ℂ) = Complex.logTaylor n (x : ℂ) := by
  simp [logTaylorReal, Complex.logTaylor]

lemma abs_log_one_add_sub_logTaylorReal_le (n : ℕ) {x : ℝ}
    (hx : |x| < 1) :
    |Real.log (1 + x) - logTaylorReal (n + 1) x| ≤
      |x| ^ (n + 1) * (1 - |x|)⁻¹ / (n + 1) := by
  have hz : ‖(x : ℂ)‖ < 1 := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using hx
  have h := Complex.norm_log_sub_logTaylor_le n hz
  have hxneg : -1 < x := (abs_lt.mp hx).1
  have hlog : Complex.log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
    rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log (by linarith)).symm
  rw [hlog, ← coe_logTaylorReal] at h
  have h' :
      ‖(Real.log (1 + x) : ℂ) - (logTaylorReal (n + 1) x : ℂ)‖ ≤
        |x| ^ (n + 1) * (1 - |x|)⁻¹ / (n + 1) := by
    simpa [Complex.norm_real, Real.norm_eq_abs] using h
  have hcoe :
      ((Real.log (1 + x) - logTaylorReal (n + 1) x : ℝ) : ℂ) =
        (Real.log (1 + x) : ℂ) - (logTaylorReal (n + 1) x : ℂ) := by
    norm_num
  rw [← hcoe, Complex.norm_real, Real.norm_eq_abs] at h'
  exact h'

lemma logTaylorQ_cast (x : ℚ) :
    (logTaylorQ x : ℝ) = logTaylorReal 25 (x : ℝ) := by
  simp [logTaylorQ, logTaylorReal]

lemma logTaylorQ_error {x : ℚ} (hx : |x| ≤ 1 / 3) :
    |Real.log (1 + (x : ℝ)) - (logTaylorQ x : ℝ)| ≤ (1 : ℝ) / 1000000000000 := by
  have hxR : |(x : ℝ)| ≤ (1 : ℝ) / 3 := by
    exact_mod_cast hx
  have hxlt : |(x : ℝ)| < 1 := lt_of_le_of_lt hxR (by norm_num)
  have h := abs_log_one_add_sub_logTaylorReal_le 24 hxlt
  rw [← logTaylorQ_cast] at h
  have hden : (2 : ℝ) / 3 ≤ 1 - |(x : ℝ)| := by linarith
  have hdenpos : 0 < 1 - |(x : ℝ)| := lt_of_lt_of_le (by norm_num) hden
  have hinv : (1 - |(x : ℝ)|)⁻¹ ≤ (3 : ℝ) / 2 := by
    rw [inv_le_iff₀ hdenpos]
    nlinarith
  have hpow : |(x : ℝ)| ^ 25 ≤ ((1 : ℝ) / 3) ^ 25 := by
    gcongr
  calc
    |Real.log (1 + (x : ℝ)) - (logTaylorQ x : ℝ)| ≤
        |(x : ℝ)| ^ 25 * (1 - |(x : ℝ)|)⁻¹ / 25 := h
    _ ≤ ((1 : ℝ) / 3) ^ 25 * ((3 : ℝ) / 2) / 25 := by gcongr
    _ ≤ (1 : ℝ) / 1000000000000 := by norm_num

lemma logRatioQ_error {x : ℚ} (hx : |x| ≤ 1 / 3) :
    |(Real.log (1 + (x : ℝ)) - Real.log (1 - (x : ℝ))) -
        (logRatioQ x : ℝ)| ≤ (1 : ℝ) / 100000000000 := by
  have hp := logTaylorQ_error hx
  have hm := logTaylorQ_error (x := -x) (by simpa using hx)
  have hcast :
      (logRatioQ x : ℝ) = (logTaylorQ x : ℝ) - (logTaylorQ (-x) : ℝ) := by
    norm_num [logRatioQ]
  rw [hcast]
  calc
    |(Real.log (1 + (x : ℝ)) - Real.log (1 - (x : ℝ))) -
        ((logTaylorQ x : ℝ) - (logTaylorQ (-x) : ℝ))| =
      |(Real.log (1 + (x : ℝ)) - (logTaylorQ x : ℝ)) -
        (Real.log (1 + (-x : ℝ)) - (logTaylorQ (-x) : ℝ))| := by
          congr 1
          push_cast
          ring
    _ ≤ |Real.log (1 + (x : ℝ)) - (logTaylorQ x : ℝ)| +
        |Real.log (1 + (-x : ℝ)) - (logTaylorQ (-x) : ℝ)| := abs_sub _ _
    _ ≤ (1 : ℝ) / 100000000000 := by linarith

end stoch_to_det.LowerBound190.LogApprox
