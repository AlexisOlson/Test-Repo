import Mathlib

namespace stoch_to_det.LowerBound190.Certificate

open Finset
open scoped BigOperators

abbrev Cell := Fin 3 × Fin 3

/-- Row-major index of a cell in the `3 × 3` grid. -/
def cellIndex (z : Cell) : Fin 9 :=
  ⟨3 * z.1.val + z.2.val, by omega⟩

def pVec : Fin 9 → ℕ :=
  ![6453, 671, 224, 354, 2032, 6403, 2066, 1116, 681]

def q0Vec : Fin 9 → ℕ :=
  ![6320, 551, 113, 178, 180, 136, 1888, 561, 126]

def q1Vec : Fin 9 → ℕ :=
  ![133, 120, 111, 176, 1852, 6267, 178, 555, 555]

def pCount (z : Cell) : ℕ := pVec (cellIndex z)
def q0Count (z : Cell) : ℕ := q0Vec (cellIndex z)
def q1Count (z : Cell) : ℕ := q1Vec (cellIndex z)

/-- The subset of cells represented by the low nine bits of `m`. -/
def mask (m : ℕ) (z : Cell) : Bool :=
  m.testBit (cellIndex z).val

def restrict (c : Cell → ℕ) (s : Cell → Bool) (z : Cell) : ℕ :=
  if s z = true then c z else 0

def rowCounts (c : Cell → ℕ) (x : Fin 3) : ℕ :=
  ∑ y : Fin 3, c (x, y)

def colCounts (c : Cell → ℕ) (y : Fin 3) : ℕ :=
  ∑ x : Fin 3, c (x, y)

/-- A 25-term rational Taylor approximation to `log (1+x)`. -/
def logTaylorQ (x : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 25, (-1 : ℚ) ^ (j + 1) * x ^ j / j

/-- Rational approximation to `log ((1+x)/(1-x))`. -/
def logRatioQ (x : ℚ) : ℚ :=
  logTaylorQ x - logTaylorQ (-x)

/-- Range-reduction parameter around the largest power of two below `n`. -/
def centerQ (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    let b := 2 ^ Nat.log 2 n
    ((n : ℚ) - (b : ℚ)) / ((n : ℚ) + (b : ℚ))

/-- Certified approximation used later for `Real.log n`. -/
def logNatQ (n : ℕ) : ℚ :=
  if n = 0 then 0 else
    (Nat.log 2 n : ℚ) * logRatioQ (1 / 3) + logRatioQ (centerQ n)

def ellQ (n : ℕ) : ℚ := (n : ℚ) * logNatQ n

def entropyQ {α : Type} [Fintype α] (c : α → ℕ) : ℚ :=
  ellQ (∑ i, c i) - ∑ i, ellQ (c i)

def phiQ (c : Cell → ℕ) : ℚ :=
  3 * entropyQ c - 2 * entropyQ (rowCounts c) - 2 * entropyQ (colCounts c)

def psiQ (c : Cell → ℕ) : ℚ :=
  2 * entropyQ c - entropyQ (rowCounts c) - entropyQ (colCounts c)

def activeMask : Fin 9 → ℕ :=
  ![7, 56, 438, 79, 432, 199, 203, 292, 195]

def activePhi (i : Fin 9) : ℚ :=
  phiQ (restrict pCount (mask (activeMask i)))

/-- Cell weights obtained by inverting the nine active-subset incidence equations. -/
def weightVec : Fin 9 → ℚ :=
  let b0 := activePhi 0
  let b1 := activePhi 1
  let b2 := activePhi 2
  let b3 := activePhi 3
  let b4 := activePhi 4
  let b5 := activePhi 5
  let b6 := activePhi 6
  let b7 := activePhi 7
  let b8 := activePhi 8
  ![
    b0 - b2 + b4,
    b2 - b4 - b5 + b8,
    b5 - b8,
    b6 - b8,
    b3 + b4 - b6 - b7,
    b1 - b3 - b4 + b7 + b8,
    -b0 + b3 - b6 + b8,
    -b3 + b5 + b6 - b8,
    -b1 + b3 + b4 - b5
  ]

def weightQ (z : Cell) : ℚ := weightVec (cellIndex z)

def dualQ (s : Cell → Bool) : ℚ :=
  ∑ z, if s z = true then weightQ z else 0

def ExceptionalMask (m : Fin 512) : Prop :=
  m.val = 0 ∨ m.val = 7 ∨ m.val = 56 ∨ m.val = 438 ∨
  m.val = 79 ∨ m.val = 432 ∨ m.val = 199 ∨ m.val = 203 ∨
  m.val = 292 ∨ m.val = 195

instance instDecidableExceptionalMask (m : Fin 512) : Decidable (ExceptionalMask m) := by
  unfold ExceptionalMask
  infer_instance

/-- The exhaustive 512-subset part of the dual certificate. -/
theorem subset_marginQ :
    ∀ m : Fin 512,
      ExceptionalMask m ∨
        phiQ (restrict pCount (mask m.val)) + 1 / 2 ≤ dualQ (mask m.val) := by
  native_decide

def stochasticQ : ℚ :=
  psiQ pCount - phiQ q0Count - phiQ q1Count

def deterministicLowerQ : ℚ :=
  psiQ pCount - ∑ z, weightQ z

/-- The rational certificate retains three full count-nats of slack over `1.9`. -/
theorem final_marginQ :
    (19 / 10 : ℚ) * stochasticQ + 3 ≤ deterministicLowerQ := by
  native_decide

end stoch_to_det.LowerBound190.Certificate
