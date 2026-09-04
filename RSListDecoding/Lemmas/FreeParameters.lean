import RSListDecoding.Lemmas.Parameters
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Rounded parameters at a free derivative order

The manuscript sets `d = ceil (ε^(-3/θ))`.  None of the discrete
interpolation, contact, or root-counting arguments requires that identity.
This file proves the rounded budget facts with `d` supplied independently.
-/

noncomputable section

namespace RSListDecoding

theorem multiplicityAt_pos {d : ℕ} (hd : 0 < d) :
    0 < multiplicityAt d := by
  simp [multiplicityAt, hd]

theorem blockLength_pos_of_order_lt_ambientDimension
    {ε θ : ℝ} {d n : ℕ}
    (hdK : d < ambientDimension ε θ n) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
  subst n
  simp [ambientDimension] at hdK

theorem interpolationDenominatorAt_pos
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    0 < ambientDimension ε θ n - 1 := by
  have hK : 1 < ambientDimension ε θ n :=
    lt_of_le_of_lt hd hdK
  omega

theorem interpolationDegreeBudgetAt_pos
    {ε θ : ℝ} {d n : ℕ} (hε : 0 < ε) (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    0 < interpolationDegreeBudgetAt d ε θ n := by
  rw [interpolationDegreeBudgetAt, Nat.ceil_pos]
  apply div_pos
  · exact_mod_cast Nat.mul_pos (multiplicityAt_pos hd)
      (agreementThreshold_pos hε hn)
  · exact_mod_cast interpolationDenominatorAt_pos hd hdK

theorem multiplicityAt_mul_agreementThreshold_le_budget_mul_denominator
    {ε θ : ℝ} {d n : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n) :
    multiplicityAt d * agreementThreshold ε n ≤
      interpolationDegreeBudgetAt d ε θ n *
        (ambientDimension ε θ n - 1) := by
  have hdenNat : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominatorAt_pos hd hdK
  have hdenReal : 0 < ((ambientDimension ε θ n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hdenNat
  have hceil :
      (((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ)) ≤
        (interpolationDegreeBudgetAt d ε θ n : ℝ) := by
    simpa [interpolationDegreeBudgetAt] using
      Nat.le_ceil
        (((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) /
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ))
  have hreal :
      ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) ≤
        (interpolationDegreeBudgetAt d ε θ n : ℝ) *
          ((ambientDimension ε θ n - 1 : ℕ) : ℝ) :=
    (div_le_iff₀ hdenReal).mp hceil
  exact_mod_cast hreal

theorem higherJetDegreeBudgetAt_cast_le {θ : ℝ} {d : ℕ}
    (hθ : 0 ≤ θ) :
    (higherJetDegreeBudgetAt θ d : ℝ) ≤
      (1 + 3 * θ / 4) * (multiplicityAt d : ℝ) := by
  rw [higherJetDegreeBudgetAt]
  apply Nat.floor_le
  positivity

theorem interpolationBoxWidthAt_cast_le {θ : ℝ} {d : ℕ}
    (hθ : 0 ≤ θ) :
    (interpolationBoxWidthAt θ d : ℝ) ≤
      θ * (multiplicityAt d : ℝ) / 16 := by
  rw [interpolationBoxWidthAt]
  apply Nat.floor_le
  positivity

theorem higherJetDegreeBudgetAt_add_three_boxWidthAt_cast_le
    {θ : ℝ} {d : ℕ} (hθ : 0 ≤ θ) :
    ((higherJetDegreeBudgetAt θ d +
        3 * interpolationBoxWidthAt θ d : ℕ) : ℝ) ≤
      (1 + 15 * θ / 16) * (multiplicityAt d : ℝ) := by
  push_cast
  have hC := higherJetDegreeBudgetAt_cast_le (d := d) hθ
  have hH := interpolationBoxWidthAt_cast_le (d := d) hθ
  nlinarith

theorem boxFamilyAt_weightedBudget_lt
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n) :
    (ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) <
      multiplicityAt d * agreementThreshold ε n := by
  have hfactor : (1 - θ) * (1 + 15 * θ / 16) < 1 := by
    nlinarith [mul_pos hθ (sub_pos.mpr hθ₁)]
  have hm : 0 < (multiplicityAt d : ℝ) := by
    exact_mod_cast multiplicityAt_pos hd
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have hxnonneg : 0 ≤ (1 - θ) * ε * (n : ℝ) := by positivity
  have hK : (ambientDimension ε θ n : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    simpa [ambientDimension] using Nat.floor_le hxnonneg
  have hKsub : ((ambientDimension ε θ n - 1 : ℕ) : ℝ) ≤
      (1 - θ) * ε * (n : ℝ) := by
    exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hK
  have hcut :=
    higherJetDegreeBudgetAt_add_three_boxWidthAt_cast_le (d := d) hθ.le
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hcut
  have hmain :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) : ℕ) : ℝ) <
        (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by
    push_cast
    calc
      ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
          ((higherJetDegreeBudgetAt θ d : ℝ) +
            3 * (interpolationBoxWidthAt θ d : ℝ))
          ≤ ((ambientDimension ε θ n - 1 : ℕ) : ℝ) *
              ((1 + 15 * θ / 16) * (multiplicityAt d : ℝ)) := by
                gcongr
      _ ≤ ((1 - θ) * ε * (n : ℝ)) *
              ((1 + 15 * θ / 16) * (multiplicityAt d : ℝ)) := by
                gcongr
      _ = ((1 - θ) * (1 + 15 * θ / 16)) *
              ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by ring
      _ < 1 * ((multiplicityAt d : ℝ) * (ε * (n : ℝ))) := by
            exact mul_lt_mul_of_pos_right hfactor (by positivity)
      _ = (multiplicityAt d : ℝ) * (ε * (n : ℝ)) := by ring
  have hA : ε * (n : ℝ) ≤ (agreementThreshold ε n : ℝ) :=
    le_agreementThreshold ε n
  have hfinal :
      (((ambientDimension ε θ n - 1) *
        (higherJetDegreeBudgetAt θ d +
          3 * interpolationBoxWidthAt θ d) : ℕ) : ℝ) <
        ((multiplicityAt d * agreementThreshold ε n : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hmain ⊢
    exact hmain.trans_le (mul_le_mul_of_nonneg_left hA hm.le)
  exact_mod_cast hfinal

theorem le_interpolationDegreeBudgetAt_of_mul_denominator_lt
    {ε θ : ℝ} {d n t : ℕ} (hd : 0 < d)
    (hdK : d < ambientDimension ε θ n)
    (ht : t * (ambientDimension ε θ n - 1) <
      multiplicityAt d * agreementThreshold ε n) :
    t ≤ interpolationDegreeBudgetAt d ε θ n := by
  by_contra hnot
  have hBt : interpolationDegreeBudgetAt d ε θ n < t :=
    Nat.lt_of_not_ge hnot
  have hden : 0 < ambientDimension ε θ n - 1 :=
    interpolationDenominatorAt_pos hd hdK
  have hmul :
      interpolationDegreeBudgetAt d ε θ n *
          (ambientDimension ε θ n - 1) <
        t * (ambientDimension ε θ n - 1) :=
    Nat.mul_lt_mul_of_pos_right hBt hden
  have hbudget :=
    multiplicityAt_mul_agreementThreshold_le_budget_mul_denominator hd hdK
  exact (not_lt_of_ge hbudget) (hmul.trans ht)

theorem interpolationBoxWidthAt_le_multiplicityAt
    {θ : ℝ} {d : ℕ} (hθ : 0 < θ) (hθ₁ : θ < 1) :
    interpolationBoxWidthAt θ d ≤ multiplicityAt d := by
  have hH := interpolationBoxWidthAt_cast_le (d := d) hθ.le
  have hm : 0 ≤ (multiplicityAt d : ℝ) := by positivity
  have hθsixteen : θ / 16 ≤ 1 := by linarith
  have hreal :
      (interpolationBoxWidthAt θ d : ℝ) ≤
        (multiplicityAt d : ℝ) := by
    calc
      (interpolationBoxWidthAt θ d : ℝ) ≤
          θ * (multiplicityAt d : ℝ) / 16 := hH
      _ = (θ / 16) * (multiplicityAt d : ℝ) := by ring
      _ ≤ 1 * (multiplicityAt d : ℝ) :=
        mul_le_mul_of_nonneg_right hθsixteen hm
      _ = (multiplicityAt d : ℝ) := one_mul _
  exact_mod_cast hreal

theorem freeGlobalDimensionSlacks
    {ε θ : ℝ} {d n : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd : 0 < d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n) :
    interpolationBoxWidthAt θ d ≤ multiplicityAt d ∧
      higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d ≤
        interpolationDegreeBudgetAt d ε θ n ∧
      (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 3 * interpolationBoxWidthAt θ d) ≤
        multiplicityAt d * agreementThreshold ε n := by
  have hweighted := boxFamilyAt_weightedBudget_lt hε hθ hθ₁ hd hn
  refine ⟨interpolationBoxWidthAt_le_multiplicityAt hθ hθ₁, ?_, hweighted.le⟩
  apply le_interpolationDegreeBudgetAt_of_mul_denominator_lt hd hdK
  calc
    (higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d) *
          (ambientDimension ε θ n - 1) =
        (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 2 * interpolationBoxWidthAt θ d) := by
            ac_rfl
    _ ≤ (ambientDimension ε θ n - 1) *
          (higherJetDegreeBudgetAt θ d + 3 * interpolationBoxWidthAt θ d) := by
            gcongr
            omega
    _ < multiplicityAt d * agreementThreshold ε n := hweighted

theorem half_interpolationBoxWidthAtTarget_le_cast
    {θ : ℝ} {d : ℕ}
    (hlarge : 2 ≤ θ * (multiplicityAt d : ℝ) / 16) :
    θ * (multiplicityAt d : ℝ) / 32 ≤
      (interpolationBoxWidthAt θ d : ℝ) := by
  have hfloor := Nat.div_two_lt_floor
    (a := θ * (multiplicityAt d : ℝ) / 16) (by linarith)
  rw [interpolationBoxWidthAt]
  calc
    θ * (multiplicityAt d : ℝ) / 32 =
        (θ * (multiplicityAt d : ℝ) / 16) / 2 := by ring
    _ ≤ (⌊θ * (multiplicityAt d : ℝ) / 16⌋₊ : ℝ) := hfloor.le

end RSListDecoding
