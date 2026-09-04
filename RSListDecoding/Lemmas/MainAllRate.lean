import RSListDecoding.Lemmas.FreeRankThreshold
import RSListDecoding.Lemmas.MainAlgorithmic

/-!
# Capacity-form Reed--Solomon list decoding

The original capstones tie the derivative order to the agreement parameter.
Here it is chosen freely.  For every fixed `0 < ε < 1` and `0 < θ < 1`,
the shell estimate, box-width estimate, and final rank comparison all hold
once `d` exceeds a threshold depending only on `ε, θ`.  The remaining
interpolation and root-enumeration proof is unchanged.
-/

noncomputable section

namespace RSListDecoding

/-- All large-order hypotheses needed by the interpolation proof, collected
under one threshold. -/
theorem exists_freeOrderThreshold
    {ε θ : ℝ} (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      2 ≤ d ∧
      2 ≤ θ * (multiplicityAt d : ℝ) / 16 ∧
      scaledExponentCount d
          (interpolationWeightBudgetAt θ d + multiplicityAt d) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (interpolationWeightBudgetAt θ d)
            (higherJetDegreeBudgetAt θ d) ∧
      (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ scaledShellExponent θ ∧
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ := by
  obtain ⟨dShell, hShell⟩ := exists_scaledShellThreshold hθ hθ₁
  obtain ⟨dBox, hBox⟩ := exists_derivativeOrderThreshold_for_boxWidth hθ
  obtain ⟨dRank, hRank⟩ := exists_freeOrderRankThreshold hε hθ hθ₁
  let d₀ := max 2 (max dShell (max dBox dRank))
  refine ⟨d₀, ?_⟩
  intro d hd₀
  have hd2 : 2 ≤ d := (Nat.le_max_left 2 _).trans hd₀
  have hrest : max dShell (max dBox dRank) ≤ d :=
    (Nat.le_max_right 2 _).trans hd₀
  have hdShell : dShell ≤ d := (Nat.le_max_left _ _).trans hrest
  have hinner : max dBox dRank ≤ d := (Nat.le_max_right _ _).trans hrest
  have hdBox : dBox ≤ d := (Nat.le_max_left _ _).trans hinner
  have hdRank : dRank ≤ d := (Nat.le_max_right _ _).trans hinner
  obtain ⟨hbad, hratio⟩ := hShell d hdShell
  have hshellRaw := scaledShell_cardinality_bound hbad hratio
  have hshell :
      scaledExponentCount d
          (interpolationWeightBudgetAt θ d + multiplicityAt d) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (interpolationWeightBudgetAt θ d)
            (higherJetDegreeBudgetAt θ d) := by
    simpa [multiplicityAt] using hshellRaw
  have hfactor := scaledShellFactor_cast_le_two_rpow hθ hθ₁
    (show 1 ≤ d by omega)
  have hboxRaw := hBox d hdBox
  have hbox : 2 ≤ θ * (multiplicityAt d : ℝ) / 16 := by
    simpa [multiplicityAt] using hboxRaw
  exact ⟨hd2, hbox, hshell, hfactor, hRank d hdRank⟩

/-- The interpolation-space dimension exceeds the total local constraint
dimension at the free-order rounded parameters. -/
theorem freeOrder_interpolation_dimension_lt
    {ε θ : ℝ} {d n q : ℕ} [Fact (Nat.Prime q)]
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd2 : 2 ≤ d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n)
    (hbox : 2 ≤ θ * (multiplicityAt d : ℝ) / 16)
    (hshell :
      scaledExponentCount d
          (interpolationWeightBudgetAt θ d + multiplicityAt d) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (interpolationWeightBudgetAt θ d)
            (higherJetDegreeBudgetAt θ d))
    (hfactor :
      (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ scaledShellExponent θ)
    (hlarge :
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ) :
    n * Module.finrank (ZMod q)
        (contactEnvelopeSpace (R := ZMod q) (d := d)
          (multiplicityAt d) (interpolationWeightBudgetAt θ d)) <
      Module.finrank (ZMod q)
        (interpolationSpace q d (multiplicityAt d)
          (agreementThreshold ε n) (ambientDimension ε θ n)
          (interpolationDegreeBudgetAt d ε θ n)
          (interpolationWeightBudgetAt θ d)
          (higherJetDegreeBudgetAt θ d)) := by
  have hd : 0 < d := by omega
  have hwidth :
      θ * (multiplicityAt d : ℝ) / 32 ≤
        (interpolationBoxWidthAt θ d : ℝ) :=
    half_interpolationBoxWidthAtTarget_le_cast hbox
  have hfactor' :
      (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ shellExponent θ := by
    simpa [scaledShellExponent, shellExponent] using hfactor
  have hcompare := freeOrder_rank_comparison hθ hd2 hdK hlarge
  have harithmetic :
      n * (4 * d ^ 8 * scaledShellFactor θ d) <
        (ambientDimension ε θ n - 1) *
          interpolationBoxWidthAt θ d ^ 3 :=
    contactEnvelope_scalar_lt_globalRectangle
      hθ hd hn (by simpa [multiplicityAt] using hwidth) hfactor' hcompare
  obtain ⟨hH, hdegree, hweighted⟩ :=
    freeGlobalDimensionSlacks hε hθ hθ₁ hd hn hdK
  change
    n * Module.finrank (ZMod q)
        (contactEnvelopeSpace (R := ZMod q) (d := d)
          (d ^ 3) (interpolationWeightBudgetAt θ d)) <
      Module.finrank (ZMod q)
        (interpolationSpace q d (d ^ 3)
          (agreementThreshold ε n) (ambientDimension ε θ n)
          (interpolationDegreeBudgetAt d ε θ n)
          (interpolationWeightBudgetAt θ d)
          (higherJetDegreeBudgetAt θ d))
  exact total_contactEnvelope_finrank_lt_interpolationSpace
    (q := q) (A := agreementThreshold ε n)
    (K := ambientDimension ε θ n)
    (B := interpolationDegreeBudgetAt d ε θ n)
    (W := interpolationWeightBudgetAt θ d)
    (C := higherJetDegreeBudgetAt θ d)
    (H := interpolationBoxWidthAt θ d)
    (R := scaledShellFactor θ d)
    hd (by simpa [multiplicityAt] using hH) hdegree hweighted
      (by simpa [multiplicityAt] using hshell) harithmetic

/-- The explainer polynomial at the free-order rounded parameters. -/
theorem exists_freeOrder_ambient_explainer
    {ε θ : ℝ} {d n q : ℕ}
    (hε : 0 < ε) (hθ : 0 < θ) (hθ₁ : θ < 1)
    (hd2 : 2 ≤ d) (hn : 0 < n)
    (hdK : d < ambientDimension ε θ n)
    (hq : Nat.Prime q)
    (hbox : 2 ≤ θ * (multiplicityAt d : ℝ) / 16)
    (hshell :
      scaledExponentCount d
          (interpolationWeightBudgetAt θ d + multiplicityAt d) ≤
        scaledShellFactor θ d *
          goodScaledExponentCount d
            (interpolationWeightBudgetAt θ d)
            (higherJetDegreeBudgetAt θ d))
    (hfactor :
      (scaledShellFactor θ d : ℝ) ≤
        2 * (d : ℝ) ^ scaledShellExponent θ)
    (hlarge :
      1 < (θ ^ 3 / 262144) * ((1 - θ) * ε / 2) *
        (d : ℝ) ^ rankSavingExponent θ)
    (alpha : Fin n → ZMod q) (halpha : Function.Injective alpha)
    (y : Fin n → ZMod q) :
    ∃ Q : DifferentialPolynomial q d,
      Q ≠ 0 ∧
      (∀ j : Fin (d + 1),
        Q.degreeOf (some j) ≤ interpolationDegreeBudgetAt d ε θ n) ∧
      Q.weightedTotalDegree
          (jetWeight (r := d) (ambientDimension ε θ n - 1)) <
        multiplicityAt d * agreementThreshold ε n ∧
      ∀ p ∈ decodingList (k := ambientDimension ε θ n) hq.ne_zero
          alpha y (agreementThreshold ε n),
        differentialSpecialization Q
          (messagePolynomialAtDimension (Nat.zero_lt_of_lt hdK) p) = 0 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hd : 0 < d := by omega
  have hdim := freeOrder_interpolation_dimension_lt
    (q := q) hε hθ hθ₁ hd2 hn hdK hbox hshell hfactor hlarge
  obtain ⟨hH, hdegree, hweighted⟩ :=
    freeGlobalDimensionSlacks hε hθ hθ₁ hd hn hdK
  have hinterpolant :
      ∃ Q : DifferentialPolynomial q d,
        Q ≠ 0 ∧
        Q ∈ interpolationSpace q d (multiplicityAt d)
          (agreementThreshold ε n) (ambientDimension ε θ n)
          (interpolationDegreeBudgetAt d ε θ n)
          (interpolationWeightBudgetAt θ d)
          (higherJetDegreeBudgetAt θ d) ∧
        ∀ i : Fin n,
          SatisfiesLocalConstraints (multiplicityAt d)
            (alpha i) (y i) Q := by
    exact exists_nonzero_interpolant_satisfying_constraints hd hdim alpha y
  exact exists_ambient_explainer_of_nonzero_interpolant
    hq (Nat.zero_lt_of_lt hdK)
      (Nat.mul_pos (multiplicityAt_pos hd)
        (agreementThreshold_pos hε hn))
      alpha halpha y hinterpolant

/-- Free-order form of the simple runtime bound `W ≤ 2d⁴`. -/
theorem interpolationWeightBudgetAt_le_two_mul_pow_four
    {θ : ℝ} {d : ℕ} (hθ : 0 < θ) (hθ₁ : θ < 1) (hd : 0 < d) :
    interpolationWeightBudgetAt θ d ≤ 2 * d ^ 4 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1
  have hden : 1 ≤ 1 + Real.log (d : ℝ) := by linarith
  have hnum :
      0 ≤ (1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ) := by
    positivity
  have hfloor :
      (interpolationWeightBudgetAt θ d : ℝ) ≤
        ((1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ)) /
          (1 + Real.log (d : ℝ)) := by
    rw [interpolationWeightBudgetAt]
    exact Nat.floor_le (div_nonneg hnum (by linarith))
  have hdivide :
      ((1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ)) /
          (1 + Real.log (d : ℝ)) ≤
        (1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ) :=
    div_le_self hnum hden
  have hfactor2 : 1 + θ / 2 ≤ 2 := by linarith
  have hreal :
      (interpolationWeightBudgetAt θ d : ℝ) ≤ (2 * d ^ 4 : ℕ) := by
    calc
      (interpolationWeightBudgetAt θ d : ℝ) ≤ _ := hfloor
      _ ≤ (1 + θ / 2) * (d : ℝ) * (multiplicityAt d : ℝ) := hdivide
      _ ≤ 2 * (d : ℝ) * (multiplicityAt d : ℝ) := by gcongr
      _ = (2 * d ^ 4 : ℕ) := by simp [multiplicityAt]; ring
  exact_mod_cast hreal

/-- Capacity-form combinatorial list-decoding theorem. -/
theorem allRateCombinatorialMainStatement_proved :
    AllRateCombinatorialMainStatement := by
  intro ε θ hε hε₁ hθ hθ₁
  obtain ⟨d₀, hthreshold⟩ := exists_freeOrderThreshold hε hθ hθ₁
  refine ⟨d₀, ?_⟩
  intro d hd₀ n hn hdK k q _hk hkK hq hnq hBq hMq alpha halpha
  obtain ⟨hd2, hbox, hshell, hfactor, hlarge⟩ := hthreshold d hd₀
  have hd : 0 < d := by omega
  have hnpos : 0 < n := by omega
  have hKn : ambientDimension ε θ n < n :=
    ambientDimension_lt_blockLength hε hε₁ hθ hθ₁ hnpos
  have hB : 0 < interpolationDegreeBudgetAt d ε θ n :=
    interpolationDegreeBudgetAt_pos hε hd hnpos hdK
  simpa only [publicListBoundAt] using
    isListDecodableAtAgreement_of_ambient_explainers_of_le_dimension
      hq hdK hkK hKn hnq hB hBq hMq alpha
        (fun y => exists_freeOrder_ambient_explainer
          hε hθ hθ₁ hd2 hnpos hdK hq hbox hshell hfactor hlarge
            alpha halpha y)

/-- Capacity-form decoder construction and operation bound. -/
theorem allRateAlgorithmicMainStatement_proved :
    AllRateAlgorithmicMainStatement := by
  let cRoot := kopparty_theorem_4_3_algorithm.exponentConstant
  refine ⟨cRoot + 34, by
    have := kopparty_theorem_4_3_algorithm.exponentConstant_pos
    omega, ?_⟩
  intro ε θ hε hε₁ hθ hθ₁
  obtain ⟨d₀, hthreshold⟩ := exists_freeOrderThreshold hε hθ hθ₁
  refine ⟨d₀, ?_⟩
  intro d hd₀ n hn hdK k q _hk hkK hq hnq hBq hMq alpha halpha
  obtain ⟨hd2, hbox, hshell, hfactor, hlarge⟩ := hthreshold d hd₀
  have hd : 0 < d := by omega
  have hnpos : 0 < n := by omega
  have hKn : ambientDimension ε θ n < n :=
    ambientDimension_lt_blockLength hε hε₁ hθ hθ₁ hnpos
  have hB : 0 < interpolationDegreeBudgetAt d ε θ n :=
    interpolationDegreeBudgetAt_pos hε hd hnpos hdK
  have hmA : 0 < multiplicityAt d * agreementThreshold ε n :=
    Nat.mul_pos (multiplicityAt_pos hd) (agreementThreshold_pos hε hnpos)
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hdim := freeOrder_interpolation_dimension_lt
    (q := q) hε hθ hθ₁ hd2 hnpos hdK hbox hshell hfactor hlarge
  have hW : interpolationWeightBudgetAt θ d ≤ 2 * d ^ 4 :=
    interpolationWeightBudgetAt_le_two_mul_pow_four hθ hθ₁ hd
  unfold multiplicityAt at hmA hMq hdim
  let decode : (Fin n → ZMod q) → FieldCost (Finset (Message q k)) :=
    fun y => decoderProgram hq hd hdK hB hkK hmA hMq hBq hdim alpha y
  refine ⟨decode, ?_⟩
  intro y
  have hcorrect :
      (decode y).result =
        decodingList (k := k) hq.ne_zero alpha y
          (agreementThreshold ε n) := by
    dsimp [decode]
    exact decoderProgram_result_eq_decodingList
      hq hd hdK hB hkK hmA hMq hBq hdim alpha halpha y
  have hlist :
      IsListDecodableAtAgreement (k := k) hq.ne_zero alpha
        (agreementThreshold ε n) (publicListBoundAt q d) := by
    simpa only [publicListBoundAt] using
      isListDecodableAtAgreement_of_ambient_explainers_of_le_dimension
        hq hdK hkK hKn hnq hB hBq hMq alpha
          (fun received => exists_freeOrder_ambient_explainer
            hε hθ hθ₁ hd2 hnpos hdK hq hbox hshell hfactor hlarge
              alpha halpha received)
  have hcostLinear :
      (decode y).operations ≤ q ^ ((cRoot + 34) * (d + 1)) := by
    dsimp [decode, cRoot]
    exact decoderProgram_operations_le_q_pow
      hq hd hdK hKn hnq hB hkK
        hmA hMq hBq hW hdim alpha y
  have hdle4 : d ≤ d ^ 4 := by
    simpa using Nat.pow_le_pow_right hd (by omega : 1 ≤ 4)
  have hcost :
      (decode y).operations ≤ q ^ ((cRoot + 34) * (d ^ 4 + 1)) :=
    hcostLinear.trans (Nat.pow_le_pow_right hq.pos
      (Nat.mul_le_mul_left _ (by omega)))
  exact ⟨hcorrect, hcorrect ▸ hlist y, hcost⟩

end RSListDecoding
