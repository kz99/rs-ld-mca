import RSListDecoding.Lemmas.BoxWidthThreshold
import RSListDecoding.Lemmas.FreeParameters
import RSListDecoding.Lemmas.RankArithmetic
import RSListDecoding.Lemmas.ScaledShell

/-!
# The final rank comparison at arbitrary agreement

For fixed positive `ε` and `θ`, the saving exponent
`2θ / (5+θ)` is positive.  Consequently the final rank coefficient tends to
infinity with a freely chosen derivative order.  This is the step hidden by
the manuscript's special choice `d = ceil (ε^(-3/θ))`.
-/

noncomputable section

namespace RSListDecoding

open Filter

@[simp] theorem scaledShellWeight_eq_interpolationWeightBudgetAt
    (θ : ℝ) (d : ℕ) :
    scaledShellWeight θ d = interpolationWeightBudgetAt θ d := by
  simp [scaledShellWeight, interpolationWeightBudgetAt, multiplicityAt]

@[simp] theorem scaledShellDegree_eq_higherJetDegreeBudgetAt
    (θ : ℝ) (d : ℕ) :
    scaledShellDegree θ d = higherJetDegreeBudgetAt θ d := by
  simp [scaledShellDegree, higherJetDegreeBudgetAt, multiplicityAt]

theorem half_unroundedAmbient_le_ambientDimension_sub_one_of_two_le_order
    {ε θ : ℝ} {d n : ℕ} (hd2 : 2 ≤ d)
    (hdK : d < ambientDimension ε θ n) :
    ((1 - θ) * ε * (n : ℝ)) / 2 ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
  have hK3 : 3 ≤ ambientDimension ε θ n := by omega
  have hK1 : 1 ≤ ambientDimension ε θ n := hK3.trans' (by omega)
  have hround :
      (1 - θ) * ε * (n : ℝ) < (ambientDimension ε θ n : ℝ) + 1 := by
    simpa [ambientDimension] using
      (Nat.lt_floor_add_one ((1 - θ) * ε * (n : ℝ)))
  rw [Nat.cast_sub hK1]
  have hK3_real : (3 : ℝ) ≤ ambientDimension ε θ n := by exact_mod_cast hK3
  linarith

theorem half_rate_le_ambientDimension_sub_one_div_of_two_le_order
    {ε θ : ℝ} {d n : ℕ} (hd2 : 2 ≤ d)
    (hdK : d < ambientDimension ε θ n) :
    (1 - θ) * ε / 2 ≤
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ) := by
  have hn : 0 < n := blockLength_pos_of_order_lt_ambientDimension hdK
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hn_real]
  have hhalf :=
    half_unroundedAmbient_le_ambientDimension_sub_one_of_two_le_order hd2 hdK
  nlinarith

theorem rankSavingExponent_pos {θ : ℝ} (hθ : 0 < θ) :
    0 < rankSavingExponent θ := by
  unfold rankSavingExponent
  positivity

/-- At any fixed positive agreement and slack, all sufficiently large free
derivative orders satisfy the scalar rank comparison after replacing the
rounded ambient rate by its uniform lower bound. -/
theorem exists_freeOrderRankThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ := by
  have hcoefficient :
      0 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) := by
    positivity
  have hpower :
      Tendsto (fun d : ℕ => (d : ℝ) ^ rankSavingExponent θ)
        atTop atTop :=
    (tendsto_rpow_atTop (rankSavingExponent_pos hθ)).comp
      tendsto_natCast_atTop_atTop
  have hproduct :
      Tendsto
        (fun d : ℕ =>
          ((θ ^ 3 / 262144) * ((1 - θ) * ε / 2)) *
            (d : ℝ) ^ rankSavingExponent θ)
        atTop atTop :=
    hpower.const_mul_atTop hcoefficient
  exact eventually_atTop.mp
    (hproduct.eventually (eventually_gt_atTop (1 : ℝ)))

/-- The same threshold supplies the exact comparison consumed by the
discrete dimension theorem, uniformly in the block length. -/
theorem freeOrder_rank_comparison
    {ε θ : ℝ} {d n : ℕ}
    (hθ : 0 < θ) (hd2 : 2 ≤ d)
    (hdK : d < ambientDimension ε θ n)
    (hlarge :
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ) :
    1 < (θ ^ 3 / 262144) *
      (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
      (d : ℝ) ^ rankSavingExponent θ := by
  have hratio :=
    half_rate_le_ambientDimension_sub_one_div_of_two_le_order hd2 hdK
  calc
    1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ := hlarge
    _ ≤ (θ ^ 3 / 262144) *
        (((ambientDimension ε θ n - 1 : ℕ) : ℝ) / (n : ℝ)) *
        (d : ℝ) ^ rankSavingExponent θ := by
      gcongr

end RSListDecoding
