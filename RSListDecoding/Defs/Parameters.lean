import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Integer parameters in the combinatorial theorem

These are the rounded parameters used in the manuscript, with `K` serving as
the ambient interpolation dimension.  Separating `K` from the requested code
dimension `k ≤ K` makes the lower-rate result a subcode consequence.
-/

namespace RSListDecoding

/-- Maximum Hasse-derivative order `d = ceil(ε^(-3/θ))`. -/
noncomputable def derivativeOrder (ε θ : ℝ) : ℕ :=
  ⌈ε ^ (-3 / θ)⌉₊

/-- Multiplicity as a function of a freely chosen derivative order. -/
def multiplicityAt (d : ℕ) : ℕ := d ^ 3

/-- Multiplicity parameter `m = d^3`. -/
noncomputable def multiplicity (ε θ : ℝ) : ℕ :=
  derivativeOrder ε θ ^ 3

/-- Integer agreement threshold `A = ceil(ε n)`. -/
noncomputable def agreementThreshold (ε : ℝ) (n : ℕ) : ℕ :=
  ⌈ε * n⌉₊

/-- Ambient interpolation dimension `K = floor((1-θ) ε n)`. -/
noncomputable def ambientDimension (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌊(1 - θ) * ε * n⌋₊

/-- Interpolation degree budget `B = ceil(m A / (K-1))`.  The capstone
statement assumes `d < K`, so the displayed denominator is positive. -/
noncomputable def interpolationDegreeBudgetAt
    (d : ℕ) (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ))⌉₊

noncomputable def interpolationDegreeBudget (ε θ : ℝ) (n : ℕ) : ℕ :=
  ⌈(((multiplicity ε θ * agreementThreshold ε n : ℕ) : ℝ) /
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ))⌉₊

/-- Anisotropic higher-jet budget
`W = floor ((1+θ/2) d m / log(e d))`.

We write the denominator as `1 + log d`, equal to `log(e d)` for positive
`d`.  This form avoids carrying the transcendental constant `e` through the
integer estimates. -/
noncomputable def interpolationWeightBudgetAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊((1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ)) /
      (1 + Real.log (d : ℝ))⌋₊

noncomputable def interpolationWeightBudget (ε θ : ℝ) : ℕ :=
  ⌊((1 + θ / 2) * (derivativeOrder ε θ : ℝ) *
      (multiplicity ε θ : ℝ)) /
      (1 + Real.log (derivativeOrder ε θ : ℝ))⌋₊

/-- Ordinary higher-jet cutoff.  The formalization and repaired manuscript
consistently use the floor convention (MF-004). -/
noncomputable def higherJetDegreeBudgetAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * (multiplicityAt d : ℝ)⌋₊

noncomputable def higherJetDegreeBudget (ε θ : ℝ) : ℕ :=
  ⌊(1 + 3 * θ / 4) * (multiplicity ε θ : ℝ)⌋₊

/-- Width of a simple rectangular family of interpolation monomials.
Using `floor(θm/16)` leaves ample slack for the `X`, `Y₀`, and `Y₁`
exponents and makes the dimension injection entirely discrete. -/
noncomputable def interpolationBoxWidthAt (θ : ℝ) (d : ℕ) : ℕ :=
  ⌊θ * (multiplicityAt d : ℝ) / 16⌋₊

noncomputable def interpolationBoxWidth (ε θ : ℝ) : ℕ :=
  ⌊θ * (multiplicity ε θ : ℝ) / 16⌋₊

/-- The clean exact public list-size bound extracted from the manuscript's
root-counting input. -/
def publicListBoundAt (q d : ℕ) : ℕ :=
  q ^ (4 * d + 6)

noncomputable def publicListBound (q : ℕ) (ε θ : ℝ) : ℕ :=
  q ^ (4 * derivativeOrder ε θ + 6)

end RSListDecoding
