import RSListDecoding.Defs.Parameters
import RSListDecoding.Defs.ReedSolomon
import RSListDecoding.Defs.FieldOperationCost

/-!
# Formalization targets

This module contains only the propositions selected as the scope of the
project.  It does not assert that either proposition has been proved.

The target counts coefficient vectors, equivalently degree-`< k`
polynomials.  For distinct evaluation points and `k ≤ n`, this is the usual
combinatorial list size of the Reed--Solomon code.
-/

namespace RSListDecoding

/-- The exact combinatorial capstone selected in `FORMALIZATION_SCOPE.md`.

For each fixed slack `θ`, a sufficiently small positive `ε` is chosen.  The
theorem then bounds, for every received word, the number of degree-`< k`
polynomials agreeing on at least `ceil(ε n)` positions.  There is no decoder
or running-time assertion in this proposition.
-/
def CombinatorialMainStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 →
    ∃ ε₀ : ℝ,
      0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ε₀ ≤ (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ)) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∀ n : ℕ, 1 ≤ n →
          derivativeOrder ε θ < ambientDimension ε θ n →
          ∀ k q : ℕ,
            1 ≤ k → k ≤ ambientDimension ε θ n →
            ∀ hq : Nat.Prime q,
              n ≤ q →
              interpolationDegreeBudget ε θ n < q →
              multiplicity ε θ * agreementThreshold ε n ≤ q ^ 2 →
              ∀ α : Fin n → ZMod q, Function.Injective α →
                IsListDecodableAtAgreement (k := k) hq.ne_zero α
                  (agreementThreshold ε n) (publicListBound q ε θ)

/-- Algorithmic extension in the finite-field-operation model.

There is one absolute exponent constant and, at every admissible parameter
choice, one decoder uniform in the received word.  Its output is exactly the
decoding list, obeys the same cardinality bound, and uses at most the displayed
number of base-field operations.  FieldCost counts addition, subtraction,
negation, multiplication, inversion, and equality testing; control flow,
index arithmetic, and allocation are outside this algebraic model. -/
def AlgorithmicMainStatement : Prop :=
  ∃ c : ℕ, 0 < c ∧
    ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ ε₀ : ℝ,
        0 < ε₀ ∧ ε₀ ≤ 1 ∧
        ε₀ ≤ (θ ^ 3 * (1 - θ) / 768) ^ ((5 + θ) / (1 - θ)) ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          ∀ n : ℕ, 1 ≤ n →
            derivativeOrder ε θ < ambientDimension ε θ n →
            ∀ k q : ℕ,
              1 ≤ k → k ≤ ambientDimension ε θ n →
              ∀ hq : Nat.Prime q,
                n ≤ q →
                interpolationDegreeBudget ε θ n < q →
                multiplicity ε θ * agreementThreshold ε n ≤ q ^ 2 →
                ∀ α : Fin n → ZMod q, Function.Injective α →
                  ∃ decode :
                      (Fin n → ZMod q) →
                        FieldCost (Finset (Message q k)),
                    ∀ y : Fin n → ZMod q,
                      (decode y).result =
                          decodingList (k := k) hq.ne_zero α y
                            (agreementThreshold ε n) ∧
                      (decode y).result.card ≤ publicListBound q ε θ ∧
                      (decode y).operations ≤
                        q ^ (c * (derivativeOrder ε θ ^ 4 + 1))

/-! ## Strengthening with a freely chosen derivative order -/

/-- Capacity-form combinatorial statement.  For every fixed positive
agreement `ε` and multiplicative rate slack `θ`, every sufficiently large
derivative order works.  The code dimension may be any
`k ≤ floor ((1-θ) ε n)`, so this covers every fixed rate strictly below the
agreement fraction. -/
def AllRateCombinatorialMainStatement : Prop :=
  ∀ ε θ : ℝ, 0 < ε → ε < 1 → 0 < θ → θ < 1 →
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∀ n : ℕ, 1 ≤ n → d < ambientDimension ε θ n →
        ∀ k q : ℕ,
          1 ≤ k → k ≤ ambientDimension ε θ n →
          ∀ hq : Nat.Prime q,
            n ≤ q →
            interpolationDegreeBudgetAt d ε θ n < q →
            multiplicityAt d * agreementThreshold ε n ≤ q ^ 2 →
            ∀ α : Fin n → ZMod q, Function.Injective α →
              IsListDecodableAtAgreement (k := k) hq.ne_zero α
                (agreementThreshold ε n) (publicListBoundAt q d)

/-- Algorithmic capacity-form statement in the same finite-field-operation
model as `AlgorithmicMainStatement`. -/
def AllRateAlgorithmicMainStatement : Prop :=
  ∃ c : ℕ, 0 < c ∧
    ∀ ε θ : ℝ, 0 < ε → ε < 1 → 0 < θ → θ < 1 →
      ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
        ∀ n : ℕ, 1 ≤ n → d < ambientDimension ε θ n →
          ∀ k q : ℕ,
            1 ≤ k → k ≤ ambientDimension ε θ n →
            ∀ hq : Nat.Prime q,
              n ≤ q →
              interpolationDegreeBudgetAt d ε θ n < q →
              multiplicityAt d * agreementThreshold ε n ≤ q ^ 2 →
              ∀ α : Fin n → ZMod q, Function.Injective α →
                ∃ decode :
                    (Fin n → ZMod q) → FieldCost (Finset (Message q k)),
                  ∀ y : Fin n → ZMod q,
                    (decode y).result =
                        decodingList (k := k) hq.ne_zero α y
                          (agreementThreshold ε n) ∧
                    (decode y).result.card ≤ publicListBoundAt q d ∧
                    (decode y).operations ≤ q ^ (c * (d ^ 4 + 1))

end RSListDecoding
