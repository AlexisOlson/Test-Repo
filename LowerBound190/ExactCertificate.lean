import LowerBound190.Certificate

namespace stoch_to_det.LowerBound190.ExactCertificate

open Finset
open scoped BigOperators
open Certificate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- A positive rational number whose real logarithm represents one exact
entropy expression.  Rational arithmetic cancels common factors eagerly. -/
structure LogRat where
  val : ℚ
  pos : 0 < val

namespace LogRat

/-- The multiplicative identity. -/
def one : LogRat where
  val := 1
  pos := by norm_num

/-- Multiplication. -/
def mul (a b : LogRat) : LogRat where
  val := a.val * b.val
  pos := mul_pos a.pos b.pos

/-- Multiplicative inverse. -/
def inv (a : LogRat) : LogRat where
  val := a.val⁻¹
  pos := inv_pos.mpr a.pos

/-- Natural power. -/
def pow (a : LogRat) (n : ℕ) : LogRat where
  val := a.val ^ n
  pos := pow_pos a.pos n

/-- Product over a finite type. -/
def prod {α : Type} [Fintype α] (f : α → LogRat) : LogRat where
  val := ∏ i, (f i).val
  pos := by
    apply Finset.prod_pos
    intro i _
    exact (f i).pos

end LogRat

/-- The convention `0^0 = 1` makes this positive for every count. -/
def selfPow (n : ℕ) : ℕ := n ^ n

lemma selfPow_pos (n : ℕ) : 0 < selfPow n := by
  by_cases h : n = 0
  · simp [selfPow, h]
  · exact pow_pos (Nat.pos_of_ne_zero h) n

/-- Total count in a `3 × 3` table. -/
def totalCount (c : Cell → ℕ) : ℕ := ∑ z, c z

/-- Product of `n^n` over the nine cells. -/
def cellProdNat (c : Cell → ℕ) : ℕ := ∏ z, selfPow (c z)

/-- Product of `n^n` over the three row totals. -/
def rowProdNat (c : Cell → ℕ) : ℕ := ∏ x, selfPow (rowCounts c x)

/-- Product of `n^n` over the three column totals. -/
def colProdNat (c : Cell → ℕ) : ℕ := ∏ y, selfPow (colCounts c y)

lemma cellProdNat_pos (c : Cell → ℕ) : 0 < cellProdNat c := by
  apply Finset.prod_pos
  intro z _
  exact selfPow_pos (c z)

lemma rowProdNat_pos (c : Cell → ℕ) : 0 < rowProdNat c := by
  apply Finset.prod_pos
  intro x _
  exact selfPow_pos (rowCounts c x)

lemma colProdNat_pos (c : Cell → ℕ) : 0 < colProdNat c := by
  apply Finset.prod_pos
  intro y _
  exact selfPow_pos (colCounts c y)

/-- Exact positive rational whose logarithm is the count-normalized `Φ`. -/
def phiRat (c : Cell → ℕ) : LogRat where
  val :=
    ((rowProdNat c : ℚ) ^ 2 * (colProdNat c : ℚ) ^ 2) /
      ((selfPow (totalCount c) : ℚ) * (cellProdNat c : ℚ) ^ 3)
  pos := by
    have hr : (0 : ℚ) < rowProdNat c := by exact_mod_cast rowProdNat_pos c
    have hc : (0 : ℚ) < colProdNat c := by exact_mod_cast colProdNat_pos c
    have ht : (0 : ℚ) < selfPow (totalCount c) := by
      exact_mod_cast selfPow_pos (totalCount c)
    have hz : (0 : ℚ) < cellProdNat c := by exact_mod_cast cellProdNat_pos c
    positivity

/-- Exact positive rational whose logarithm is the count-normalized `Ψ`. -/
def psiRat (c : Cell → ℕ) : LogRat where
  val :=
    ((rowProdNat c : ℚ) * (colProdNat c : ℚ)) /
      (cellProdNat c : ℚ) ^ 2
  pos := by
    have hr : (0 : ℚ) < rowProdNat c := by exact_mod_cast rowProdNat_pos c
    have hc : (0 : ℚ) < colProdNat c := by exact_mod_cast colProdNat_pos c
    have hz : (0 : ℚ) < cellProdNat c := by exact_mod_cast cellProdNat_pos c
    positivity

/-- The nine active subsets defining the dual supporting hyperplane. -/
def activePhiRat (i : Fin 9) : LogRat :=
  phiRat (restrict pCount (mask (activeMask i)))

/-- Cell weights obtained by solving the nine active-subset equations,
represented multiplicatively because logarithms turn products into sums. -/
def weightRatVec : Fin 9 → LogRat :=
  let b0 := activePhiRat 0
  let b1 := activePhiRat 1
  let b2 := activePhiRat 2
  let b3 := activePhiRat 3
  let b4 := activePhiRat 4
  let b5 := activePhiRat 5
  let b6 := activePhiRat 6
  let b7 := activePhiRat 7
  let b8 := activePhiRat 8
  ![
    LogRat.mul (LogRat.mul b0 (LogRat.inv b2)) b4,
    LogRat.mul
      (LogRat.mul (LogRat.mul b2 (LogRat.inv b4)) (LogRat.inv b5)) b8,
    LogRat.mul b5 (LogRat.inv b8),
    LogRat.mul b6 (LogRat.inv b8),
    LogRat.mul
      (LogRat.mul (LogRat.mul b3 b4) (LogRat.inv b6)) (LogRat.inv b7),
    LogRat.mul
      (LogRat.mul
        (LogRat.mul (LogRat.mul b1 (LogRat.inv b3)) (LogRat.inv b4)) b7) b8,
    LogRat.mul
      (LogRat.mul (LogRat.mul (LogRat.inv b0) b3) (LogRat.inv b6)) b8,
    LogRat.mul
      (LogRat.mul (LogRat.mul (LogRat.inv b3) b5) b6) (LogRat.inv b8),
    LogRat.mul
      (LogRat.mul (LogRat.mul (LogRat.inv b1) b3) b4) (LogRat.inv b5)
  ]

/-- Dual cell weight. -/
def weightRat (z : Cell) : LogRat := weightRatVec (cellIndex z)

/-- Product of dual weights over a subset. -/
def dualRat (s : Cell → Bool) : LogRat :=
  LogRat.prod fun z => if s z = true then weightRat z else LogRat.one

/-- Every one of the 512 cell subsets lies below the dual supporting
hyperplane.  This is an exact rational comparison. -/
theorem subset_product_certificate :
    ∀ m : Fin 512,
      (phiRat (restrict pCount (mask m.val))).val ≤ (dualRat (mask m.val)).val := by
  native_decide

/-- Exact rational whose logarithm is `20000 · log(2) · S_p(V)` for the
binary stochastic witness. -/
def stochasticRat : LogRat :=
  LogRat.mul
    (LogRat.mul (psiRat pCount) (LogRat.inv (phiRat q0Count)))
    (LogRat.inv (phiRat q1Count))

/-- Exact rational whose logarithm is the certified deterministic lower bound. -/
def deterministicRat : LogRat :=
  LogRat.mul (psiRat pCount)
    (LogRat.inv (dualRat fun _ => true))

/-- `10 log deterministicRat > 19 log stochasticRat`, reduced to one strict
comparison of exact rationals. -/
theorem final_product_certificate :
    stochasticRat.val ^ 19 < deterministicRat.val ^ 10 := by
  native_decide

end stoch_to_det.LowerBound190.ExactCertificate
