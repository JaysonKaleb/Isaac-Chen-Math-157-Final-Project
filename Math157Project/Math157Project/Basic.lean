import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.MeanInequalities

open MeasureTheory ProbabilityTheory
set_option linter.unusedSectionVars false

variable {Ω : Type*} {m : MeasurableSpace Ω}
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (X : Ω → ℝ)

/-!
# Chebyshev's Inequality

This file formalizes the proof chain:
  Markov's Inequality → Chebyshev's Inequality

Reference:
  Sheldon Ross, *A First Course in Probability*,
  Chapter 8; Wikipedia: [Markov's inequality](https://en.wikipedia.org/wiki/Markov%27s_inequality),
  [Chebyshev's inequality](https://en.wikipedia.org/wiki/Chebyshev%27s_inequality).

## Outline

* `level_set_measurable`     -- Lemma 1: {ω | ε ≤ X ω} is measurable
* `indicator_domination`     -- Lemma 2: ε * μ(S) ≤ 𝔼[X] for nonneg X
* `markov_inequality`        -- Theorem 1: P(X ≥ ε) ≤ 𝔼[X] / ε
* `sq_dev_set_equiv`         -- Lemma 3: {|X − μ| ≥ k} = {(X − μ)² ≥ k²}
* `variance_eq_expectation`  -- Lemma 4: Var[X] = 𝔼[(X − 𝔼[X])²]
* `chebyshev_inequality`     -- Theorem 2: P(|X − μ| ≥ k) ≤ Var[X] / k²
-/

-- ============================================================
-- Section 1: Supporting Lemmas (Markov)
-- ============================================================

/-- Lemma 1: The level set {ω | ε ≤ X ω} is measurable.
    This is needed to take the measure of the event {X ≥ ε}. -/
lemma level_set_measurable
    (hX : Measurable X) (ε : ℝ) :
    MeasurableSet {ω | ε ≤ X ω} := by
    measurability

/-- Lemma 2: For nonneg X and ε > 0, we have ε * μ {ω | ε ≤ X ω} ≤ 𝔼[X].
    This is the core computation in Markov's proof: X dominates ε · 1_S pointwise,
    so the same holds after integrating. -/
/-
    Proof: Let S := {ω | ε ≤ X ω}. Then ε · 1_S(ω) ≤ X(ω) for all ω, since
      if ω ∈ S, then 1_S(ω) = 1 and ε ≤ X(ω) by definition of S;
      if ω ∉ S, then 1_S(ω) = 0 and 0 ≤ X(ω) by nonnegativity.
      Integrating this pointwise bound gives ε * μ(S) ≤ 𝔼[X],
      since the integral of ε · 1_S is ε * μ(S).
-/
lemma indicator_domination
    (hX : Measurable X) (hXnn : 0 ≤ X) (hXi : Integrable X μ) (ε : ℝ) (hε : 0 < ε) :
    ε * (μ {ω | ε ≤ X ω}).toReal ≤ ∫ ω, X ω ∂μ := by
    -- Let S := {ω | ε ≤ X ω}; it is measurable by Lemma 1
  set S := {ω | ε ≤ X ω} with hS_def
  have hSmeas : MeasurableSet S := by
    simpa [hS_def] using (level_set_measurable (X := X) (hX := hX) ε)
  -- Pointwise bound: ε · 1_S(ω) ≤ X(ω) for all ω
  -- Case ω ∈ S: indicator = ε ≤ X(ω) by definition of S
  -- Case ω ∉ S: indicator = 0 ≤ X(ω) by nonnegativity
  have hpw : ∀ ω, S.indicator (fun _ => ε) ω ≤ X ω := by
    intro ω
    by_cases hω : ω ∈ S
    · simp only [Set.indicator_of_mem hω]; exact hω
    · simp only [Set.indicator_apply, if_neg hω]; exact hXnn ω
  -- Rewrite LHS: ε * μ(S).toReal = ∫ ε · 1_S ∂μ
  have hint_ind :
    ∫ ω, S.indicator (fun _ => ε) ω ∂μ
    = (μ S).toReal • ε := by
    simpa using integral_indicator_const ε hSmeas
  -- ε · 1_S is nonneg everywhere
  have hind_nn : ∀ ω, 0 ≤ S.indicator (fun _ => ε) ω :=
    fun ω => Set.indicator_nonneg (fun _ _ => hε.le) ω
  -- Conclude by monotonicity of integration (X integrable by hypothesis)
  have hmono := integral_mono_of_nonneg
    (Filter.Eventually.of_forall hind_nn)
    hXi
    (Filter.Eventually.of_forall hpw)
  calc ε * (μ S).toReal
    = (μ S).toReal • ε := by rw [smul_eq_mul, mul_comm]
  _ = ∫ ω, S.indicator (fun _ => ε) ω ∂μ := hint_ind.symm
  _ ≤ ∫ ω, X ω ∂μ := hmono
-- ============================================================
-- Theorem 1: Markov's Inequality
-- ============================================================

/-- **Markov's Inequality**: For a nonneg measurable random variable X and ε > 0,
      P(X ≥ ε) ≤ 𝔼[X] / ε
    Proof: integrate the pointwise bound X ≥ ε · 1_{X ≥ ε}, then divide by ε. -/
theorem markov_inequality
    (hX : Measurable X) (hXnn : 0 ≤ X) (hXi : Integrable X μ)
    (ε : ℝ) (hε : 0 < ε) :
    (μ {ω | ε ≤ X ω}).toReal ≤ (∫ ω, X ω ∂μ) / ε := by
    -- From indicator_domination: ε * μ{X ≥ ε} ≤ 𝔼[X]
    -- Divide both sides by ε (which is positive) to conclude.
    have h := indicator_domination μ X hX hXnn hXi ε hε
    -- Rearrange: a * b ≤ c → b ≤ c / a (for a > 0)
    rwa [le_div_iff₀ hε, mul_comm]


-- ============================================================
-- Section 2: Supporting Lemmas (Chebyshev)
-- ============================================================

/-- Lemma 3: The set equivalence {|X − 𝔼[X]| ≥ k} = {(X − 𝔼[X])² ≥ k²}.
    This lets us apply Markov to the squared deviation (X − 𝔼[X])²,
    which is always nonneg. -/
lemma sq_dev_set_equiv (k : ℝ) (hk : 0 < k) :
    {ω | k ≤ |X ω - ∫ x, X x ∂μ|}
    = {ω | k ^ 2 ≤ (X ω - ∫ x, X x ∂μ) ^ 2} := by
   -- Reduce to a pointwise iff, then use k ≤ |d| ↔ k² ≤ d² (for k > 0)
  ext ω
  simp only [Set.mem_setOf_eq]
  -- rewrite d² as |d|² so both sides involve |d|
  rw [← sq_abs (X ω - ∫ x, X x ∂μ)]
  -- now the goal is: k ≤ |d| ↔ k ^ 2 ≤ |d| ^ 2
  -- both sides are nonneg, so squaring is monotone in both directions
  exact ⟨fun h => pow_le_pow_left₀ hk.le h 2,
         fun h => by nlinarith [abs_nonneg (X ω - ∫ x, X x ∂μ), sq_nonneg k,
                                sq_nonneg (|X ω - ∫ x, X x ∂μ| - k)]⟩

/-- Lemma 4: Under the L² hypothesis, the variance equals 𝔼[(X − 𝔼[X])²],
    and the function (X − 𝔼[X])² is nonneg and integrable.
    This connects the Mathlib definition of variance to the form needed
    to apply Markov's inequality. -/
lemma variance_eq_expectation (hX : MemLp X 2 μ) :
    variance X μ = ∫ ω, (X ω - ∫ x, X x ∂μ) ^ 2 ∂μ := by
  -- Mathlib's variance_eq_integral requires only AEMeasurable X μ,
  -- which follows immediately from the MemLp hypothesis.
  exact variance_eq_integral hX.aemeasurable

-- ============================================================
-- Theorem 2: Chebyshev's Inequality
-- ============================================================

/-- **Chebyshev's Inequality**: For a square-integrable random variable X and k > 0,
      P(|X − 𝔼[X]| ≥ k) ≤ Var[X] / k²
    Proof: Let Y := (X − 𝔼[X])². Apply Markov to Y with threshold k²,
    use Lemma 3 to rewrite the event, and Lemma 4 to substitute the variance. -/
theorem chebyshev_inequality (hX : MemLp X 2 μ) (hXm : Measurable X) (k : ℝ) (hk : 0 < k) :
    (μ {ω | k ≤ |X ω - ∫ x, X x ∂μ|}).toReal ≤ variance X μ / k ^ 2 := by
  -- Let Y ω := (X ω - 𝔼[X])², a nonneg square-integrable function.
  set c := ∫ x, X x ∂μ with hc_def
  set Y := fun ω => (X ω - c) ^ 2 with hY_def
  -- Step 1: measurability of Y.
  -- level_set_measurable (Lemma 1) establishes MeasurableSet {ω | ε ≤ X ω} for all ε,
  -- which captures the measurability of X. We derive Measurable Y from Measurable X
  -- by composing with the measurable maps (· - c) and (· ^ 2).
  -- Note: the level-set measurability of Y itself, e.g. {ω | k² ≤ Y ω}, then follows
  -- from Lemma 1 applied to Y (hYm plays the same role for Y that hXm does for X).
  have hYm : Measurable Y := by
    simp only [hY_def]
    exact (hXm.sub measurable_const).pow_const 2
    -- level_set_measurable on X confirms {ω | ε ≤ X ω} ∈ MeasurableSet for all ε;
    -- here we use Measurable X directly to build Measurable Y via function composition.
  -- Step 2: nonnegativity of Y
  have hYnn : 0 ≤ Y := fun ω => sq_nonneg _
  -- Step 3: integrability of Y via MemLp.integrable_sq applied to (X - c)
  have hYi : Integrable Y μ := by
    have : MemLp (fun ω => X ω - c) 2 μ := hX.sub (memLp_const c)
    simpa [hY_def] using this.integrable_sq
  -- Step 4: rewrite the event {|X - 𝔼[X]| ≥ k} = {Y ≥ k²} using Lemma 3
  have hset : {ω | k ≤ |X ω - c|} = {ω | k ^ 2 ≤ Y ω} := by
    simp only [hY_def]; exact sq_dev_set_equiv μ X k hk
  -- Step 5: apply Markov's inequality to Y with threshold k²
  have hk2 : 0 < k ^ 2 := pow_pos hk 2
  have hMarkov := markov_inequality μ Y hYm hYnn hYi (k ^ 2) hk2
  -- Step 6: rewrite ∫ Y as variance X μ using Lemma 4
  have hvar : variance X μ = ∫ ω, Y ω ∂μ := by
    simp only [hY_def, hc_def]; exact variance_eq_expectation μ X hX
  -- Combine all pieces
  rw [hset, hvar]
  exact hMarkov
