import LowerBound190.ExactCertificate
import stoch_to_det.Envelope

namespace stoch_to_det.LowerBound190

open Finset
open scoped BigOperators
open Certificate ExactCertificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ExactCertificate.LogRat

/-- The real logarithm represented by a positive exact rational. -/
noncomputable def logValue (a : LogRat) : ℝ :=
  Real.log (a.val : ℝ)

lemma cast_pos (a : LogRat) : (0 : ℝ) < (a.val : ℝ) := by
  exact_mod_cast a.pos

@[simp] lemma logValue_one : logValue one = 0 := by
  simp [logValue, one]

@[simp] lemma logValue_mul (a b : LogRat) :
    logValue (mul a b) = logValue a + logValue b := by
  simp [logValue, mul, Real.log_mul, (cast_pos a).ne', (cast_pos b).ne']

@[simp] lemma logValue_inv (a : LogRat) :
    logValue (inv a) = -logValue a := by
  have ha : a.val ≠ 0 := ne_of_gt a.pos
  simp [logValue, inv, ha, Real.log_inv]

@[simp] lemma logValue_pow (a : LogRat) (n : ℕ) :
    logValue (pow a n) = n * logValue a := by
  simp [logValue, pow, Real.log_pow]

lemma logValue_prod {α : Type} [Fintype α] (f : α → LogRat) :
    logValue (prod f) = ∑ i, logValue (f i) := by
  change Real.log ((↑(∏ i, (f i).val) : ℝ)) =
    ∑ i, Real.log ((f i).val : ℝ)
  have hcast :
      (↑(∏ i, (f i).val) : ℝ) = ∏ i, ((f i).val : ℝ) := by
    norm_num
  rw [hcast, Real.log_prod]
  intro i _
  exact (cast_pos (f i)).ne'

end ExactCertificate.LogRat

namespace ExactLogs

/-- `n log n`, with Lean's harmless convention `log 0 = 0`. -/
noncomputable def ellR (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ)

noncomputable def entropyR {α : Type} [Fintype α] (c : α → ℕ) : ℝ :=
  ellR (∑ i, c i) - ∑ i, ellR (c i)

noncomputable def phiR (c : Cell → ℕ) : ℝ :=
  3 * entropyR c - 2 * entropyR (rowCounts c) - 2 * entropyR (colCounts c)

noncomputable def psiR (c : Cell → ℕ) : ℝ :=
  2 * entropyR c - entropyR (rowCounts c) - entropyR (colCounts c)

lemma sum_rowCounts (c : Cell → ℕ) :
    ∑ x, rowCounts c x = totalCount c := by
  simp only [rowCounts, totalCount]
  rw [Fintype.sum_prod_type]

lemma sum_colCounts (c : Cell → ℕ) :
    ∑ y, colCounts c y = totalCount c := by
  simp only [colCounts, totalCount]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

lemma log_selfPow (n : ℕ) :
    Real.log (selfPow n : ℝ) = ellR n := by
  simp [selfPow, ellR, Real.log_pow]

lemma log_natProd {α : Type} [Fintype α] (f : α → ℕ)
    (hf : ∀ i, 0 < f i) :
    Real.log ((∏ i, f i : ℕ) : ℝ) =
      ∑ i, Real.log (f i : ℝ) := by
  have hcast :
      ((∏ i, f i : ℕ) : ℝ) = ∏ i, (f i : ℝ) := by
    norm_num
  rw [hcast, Real.log_prod]
  intro i _
  exact_mod_cast (hf i).ne'

lemma log_cellProdNat (c : Cell → ℕ) :
    Real.log (cellProdNat c : ℝ) = ∑ z, ellR (c z) := by
  unfold cellProdNat
  rw [log_natProd (fun z => selfPow (c z)) (fun z => selfPow_pos (c z))]
  apply Finset.sum_congr rfl
  intro z _
  exact log_selfPow (c z)

lemma log_rowProdNat (c : Cell → ℕ) :
    Real.log (rowProdNat c : ℝ) = ∑ x, ellR (rowCounts c x) := by
  unfold rowProdNat
  rw [log_natProd (fun x => selfPow (rowCounts c x))
    (fun x => selfPow_pos (rowCounts c x))]
  apply Finset.sum_congr rfl
  intro x _
  exact log_selfPow (rowCounts c x)

lemma log_colProdNat (c : Cell → ℕ) :
    Real.log (colProdNat c : ℝ) = ∑ y, ellR (colCounts c y) := by
  unfold colProdNat
  rw [log_natProd (fun y => selfPow (colCounts c y))
    (fun y => selfPow_pos (colCounts c y))]
  apply Finset.sum_congr rfl
  intro y _
  exact log_selfPow (colCounts c y)

lemma logValue_phiRat (c : Cell → ℕ) :
    LogRat.logValue (phiRat c) = phiR c := by
  have hr : (rowProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (rowProdNat_pos c).ne'
  have hc : (colProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (colProdNat_pos c).ne'
  have ht : (selfPow (totalCount c) : ℝ) ≠ 0 := by
    exact_mod_cast (selfPow_pos (totalCount c)).ne'
  have hz : (cellProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (cellProdNat_pos c).ne'
  calc
    LogRat.logValue (phiRat c) =
        2 * Real.log (rowProdNat c : ℝ) +
        2 * Real.log (colProdNat c : ℝ) -
        Real.log (selfPow (totalCount c) : ℝ) -
        3 * Real.log (cellProdNat c : ℝ) := by
      simp [LogRat.logValue, phiRat, Real.log_div, Real.log_mul,
        Real.log_pow, hr, hc, ht, hz]
      ring
    _ = phiR c := by
      rw [log_rowProdNat, log_colProdNat, log_selfPow, log_cellProdNat]
      simp only [phiR, entropyR]
      rw [sum_rowCounts, sum_colCounts]
      ring

lemma logValue_psiRat (c : Cell → ℕ) :
    LogRat.logValue (psiRat c) = psiR c := by
  have hr : (rowProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (rowProdNat_pos c).ne'
  have hc : (colProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (colProdNat_pos c).ne'
  have hz : (cellProdNat c : ℝ) ≠ 0 := by
    exact_mod_cast (cellProdNat_pos c).ne'
  calc
    LogRat.logValue (psiRat c) =
        Real.log (rowProdNat c : ℝ) +
        Real.log (colProdNat c : ℝ) -
        2 * Real.log (cellProdNat c : ℝ) := by
      simp [LogRat.logValue, psiRat, Real.log_div, Real.log_mul,
        Real.log_pow, hr, hc, hz]
    _ = psiR c := by
      rw [log_rowProdNat, log_colProdNat, log_cellProdNat]
      simp only [psiR, entropyR]
      rw [sum_rowCounts, sum_colCounts]
      ring

noncomputable def weightR (z : Cell) : ℝ :=
  LogRat.logValue (weightRat z)

lemma logValue_dualRat (s : Cell → Bool) :
    LogRat.logValue (dualRat s) =
      ∑ z, if s z = true then weightR z else 0 := by
  rw [dualRat, LogRat.logValue_prod]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : s z = true
  · simp [hz, weightR]
  · have hz' : s z = false := Bool.eq_false_of_not_eq_true hz
    simp [hz', LogRat.logValue_one]

lemma subset_log_certificate (s : Cell → Bool) :
    phiR (restrict pCount s) ≤
      ∑ z, if s z = true then weightR z else 0 := by
  have hq := subset_product_certificate s
  have hreal :
      ((phiRat (restrict pCount s)).val : ℝ) ≤
        ((dualRat s).val : ℝ) := by
    exact_mod_cast hq
  calc
    phiR (restrict pCount s) =
        LogRat.logValue (phiRat (restrict pCount s)) :=
      (logValue_phiRat _).symm
    _ ≤ LogRat.logValue (dualRat s) :=
      Real.log_le_log (LogRat.cast_pos _) hreal
    _ = ∑ z, if s z = true then weightR z else 0 :=
      logValue_dualRat s

lemma logValue_stochasticRat :
    LogRat.logValue stochasticRat =
      psiR pCount - phiR q0Count - phiR q1Count := by
  simp [stochasticRat, logValue_phiRat, logValue_psiRat]
  ring

lemma logValue_deterministicRat :
    LogRat.logValue deterministicRat =
      psiR pCount - ∑ z, weightR z := by
  simp [deterministicRat, logValue_psiRat, logValue_dualRat, weightR]

/-- The exact power comparison is the desired strict `1.9` logarithmic gap. -/
theorem final_log_certificate :
    (19 / 10 : ℝ) * LogRat.logValue stochasticRat <
      LogRat.logValue deterministicRat := by
  have hreal :
      ((stochasticRat.val : ℝ) ^ 19) <
        ((deterministicRat.val : ℝ) ^ 10) := by
    exact_mod_cast final_product_certificate
  have hlog := Real.log_lt_log
    (pow_pos (LogRat.cast_pos stochasticRat) 19) hreal
  have hlog' :
      (19 : ℝ) * LogRat.logValue stochasticRat <
        (10 : ℝ) * LogRat.logValue deterministicRat := by
    simpa [LogRat.logValue, Real.log_pow] using hlog
  linarith

end ExactLogs
end stoch_to_det.LowerBound190
