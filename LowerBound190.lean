import stoch_to_det.Envelope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace stoch_to_det.LowerBound190

open Finset

noncomputable def logTaylorR (n : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (-1 : ℝ) ^ (j + 1) * x ^ j / j

lemma coe_logTaylorR (n : ℕ) (x : ℝ) :
    (logTaylorR n x : ℂ) = Complex.logTaylor n (x : ℂ) := by
  simp [logTaylorR, Complex.logTaylor]

lemma abs_log_one_add_sub_logTaylorR_le (n : ℕ) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    |Real.log (1 + x) - logTaylorR (n + 1) x| ≤
      x ^ (n + 1) * (1 - x)⁻¹ / (n + 1) := by
  have hz : ‖(x : ℂ)‖ < 1 := by
    simpa [abs_of_nonneg hx0] using hx1
  have h := Complex.norm_log_sub_logTaylor_le n hz
  have hlog : Complex.log (1 + (x : ℂ)) = (Real.log (1 + x) : ℂ) := by
    rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by norm_num]
    exact (Complex.ofReal_log (by linarith)).symm
  rw [hlog, ← coe_logTaylorR] at h
  have h' :
      ‖((Real.log (1 + x) - logTaylorR (n + 1) x : ℝ) : ℂ)‖ ≤
        x ^ (n + 1) * (1 - x)⁻¹ / (n + 1) := by
    simpa using h
  simpa [Real.norm_eq_abs] using h'

example :
    |Real.log (3 / 2) - logTaylorR 31 (1 / 2)| ≤ (1 : ℝ) / 1000000000 := by
  have h := abs_log_one_add_sub_logTaylorR_le 30
    (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
  norm_num [logTaylorR] at h ⊢
  linarith

end stoch_to_det.LowerBound190
