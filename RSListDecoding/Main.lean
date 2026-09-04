import RSListDecoding.Lemmas.MainAllRate

/-!
# Trusted statement surface

This is the short file a reader should inspect to determine what the project
proves.  The implementation lives under `RSListDecoding/Lemmas/`; the
capstone below delegates to the completed proof assembly there.
-/

open scoped BigOperators

namespace RSListDecoding

/-- Coefficient-vector evaluation really is the displayed finite sum. -/
example {q k : ℕ} (p : Message q k) (x : ZMod q) :
    evaluateMessage p x = ∑ i : Fin k, p i * x ^ (i : ℕ) := rfl

/-- The agreement threshold is exactly `ceil(ε n)`. -/
example (ε : ℝ) (n : ℕ) : agreementThreshold ε n = ⌈ε * n⌉₊ := rfl

/-- The public list bound is exactly `q^(4d+6)`. -/
example (q : ℕ) (ε θ : ℝ) :
    publicListBound q ε θ = q ^ (4 * derivativeOrder ε θ + 6) := rfl

/-- The scoped combinatorial list-decoding theorem. -/
theorem combinatorial_main : CombinatorialMainStatement :=
  combinatorialMainStatement_proved

/-- The scoped decoder construction and finite-field-operation bound. -/
theorem algorithmic_main : AlgorithmicMainStatement :=
  algorithmicMainStatement_proved

/-- Capacity-form combinatorial theorem with a freely chosen derivative
order. -/
theorem all_rate_combinatorial_main : AllRateCombinatorialMainStatement :=
  allRateCombinatorialMainStatement_proved

/-- Capacity-form decoder and finite-field-operation bound. -/
theorem all_rate_algorithmic_main : AllRateAlgorithmicMainStatement :=
  allRateAlgorithmicMainStatement_proved

end RSListDecoding
