import LowerBound190.Certificate

namespace stoch_to_det.LowerBound190.ExactCertificate

open Finset
open scoped BigOperators
open Certificate

/-- A positive rational number, represented without quotienting.  Its logarithm
is `log num - log den`.  Proof fields erase under `native_decide`. -/
structure LogPair where
  num : ℕ
  den : ℕ
  num_pos : 0 < num
  den_pos : 0 < den

namespace LogPair

/-- The multiplicative identity. -/
def one : LogPair where
  num := 1
  den := 1
  num_pos := by decide
  den_pos := by decide

/-- Multiplication of represented positive rationals. -/
def mul (a b : LogPair) : LogPair where
  num := a.num * b.num
  den := a.den * b.den
  num_pos := Nat.mul_pos a.num_pos b.num_pos
  den_pos := Nat.mul_pos a.den_pos b.den_pos

/-- Multiplicative inverse. -/
def inv (a : LogPair) : LogPair where
  num := a.den
  den := a.num
  num_pos := a.den_pos
  den_pos := a.num_pos

/-- A natural power. -/
def pow (a : LogPair) (n : ℕ) : LogPair where
  num := a.num ^ n
  den := a.den ^ n
  num_pos := pow_pos a.num_pos n
  den_pos := pow_pos a.den_pos n

/-- Product over a finite type. -/
def prod {α : Type} [Fintype α] (f : α → LogPair) : LogPair where
  num := ∏ i, (f i).num
  den := ∏ i, (f i).den
  num_pos := by
    apply Finset.prod_pos
    intro i _
    exact (f i).num_pos
  den_pos := by
    apply Finset.prod_pos
    intro i _
    exact (f i).den_pos

end LogPair

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

/-- Exact monomial whose logarithm is the count-normalized `Φ` functional. -/
def phiPair (c : Cell → ℕ) : LogPair where
  num := rowProdNat c ^ 2 * colProdNat c ^ 2
  den := selfPow (totalCount c) * cellProdNat c ^ 3
  num_pos := Nat.mul_pos
    (pow_pos (rowProdNat_pos c) 2)
    (pow_pos (colProdNat_pos c) 2)
  den_pos := Nat.mul_pos
    (selfPow_pos (totalCount c))
    (pow_pos (cellProdNat_pos c) 3)

/-- Exact monomial whose logarithm is the count-normalized `Ψ` functional. -/
def psiPair (c : Cell → ℕ) : LogPair where
  num := rowProdNat c * colProdNat c
  den := cellProdNat c ^ 2
  num_pos := Nat.mul_pos (rowProdNat_pos c) (colProdNat_pos c)
  den_pos := pow_pos (cellProdNat_pos c) 2

/-- The nine active subsets defining the dual supporting hyperplane. -/
def activePhiPair (i : Fin 9) : LogPair :=
  phiPair (restrict pCount (mask (activeMask i)))

/-- Cell weights obtained by solving the nine active-subset equations,
represented multiplicatively because logarithms turn products into sums. -/
def weightPairVec : Fin 9 → LogPair :=
  let b0 := activePhiPair 0
  let b1 := activePhiPair 1
  let b2 := activePhiPair 2
  let b3 := activePhiPair 3
  let b4 := activePhiPair 4
  let b5 := activePhiPair 5
  let b6 := activePhiPair 6
  let b7 := activePhiPair 7
  let b8 := activePhiPair 8
  ![
    LogPair.mul (LogPair.mul b0 (LogPair.inv b2)) b4,
    LogPair.mul
      (LogPair.mul (LogPair.mul b2 (LogPair.inv b4)) (LogPair.inv b5)) b8,
    LogPair.mul b5 (LogPair.inv b8),
    LogPair.mul b6 (LogPair.inv b8),
    LogPair.mul
      (LogPair.mul (LogPair.mul b3 b4) (LogPair.inv b6)) (LogPair.inv b7),
    LogPair.mul
      (LogPair.mul
        (LogPair.mul (LogPair.mul b1 (LogPair.inv b3)) (LogPair.inv b4)) b7) b8,
    LogPair.mul
      (LogPair.mul (LogPair.mul (LogPair.inv b0) b3) (LogPair.inv b6)) b8,
    LogPair.mul
      (LogPair.mul (LogPair.mul (LogPair.inv b3) b5) b6) (LogPair.inv b8),
    LogPair.mul
      (LogPair.mul (LogPair.mul (LogPair.inv b1) b3) b4) (LogPair.inv b5)
  ]

/-- Dual cell weight. -/
def weightPair (z : Cell) : LogPair := weightPairVec (cellIndex z)

/-- Product of dual weights over a subset. -/
def dualPair (s : Cell → Bool) : LogPair :=
  LogPair.prod fun z => if s z = true then weightPair z else LogPair.one

/-- Every one of the 512 cell subsets lies below the dual supporting
hyperplane.  This is an exact integer cross-product check. -/
set_option maxHeartbeats 0 maxRecDepth 100000 in
theorem subset_product_certificate :
    ∀ m : Fin 512,
      (phiPair (restrict pCount (mask m.val))).num * (dualPair (mask m.val)).den ≤
        (phiPair (restrict pCount (mask m.val))).den * (dualPair (mask m.val)).num := by
  native_decide

/-- Exact monomial for `20000 · log(2) · S_p(V)` of the binary witness. -/
def stochasticPair : LogPair :=
  LogPair.mul
    (LogPair.mul (psiPair pCount) (LogPair.inv (phiPair q0Count)))
    (LogPair.inv (phiPair q1Count))

/-- Exact monomial for the certified deterministic lower bound. -/
def deterministicPair : LogPair :=
  LogPair.mul (psiPair pCount)
    (LogPair.inv (dualPair fun _ => true))

/-- `10 log deterministicPair > 19 log stochasticPair`, reduced to a strict
comparison of two natural numbers. -/
set_option maxHeartbeats 0 maxRecDepth 100000 in
theorem final_product_certificate :
    stochasticPair.num ^ 19 * deterministicPair.den ^ 10 <
      stochasticPair.den ^ 19 * deterministicPair.num ^ 10 := by
  native_decide

end stoch_to_det.LowerBound190.ExactCertificate
