(** De Philippis, Gennaioli, Pigati and Rindler (2026), Theorem 1.6;
    blueprint thm:MS: the anisotropic Michael–Simon inequality for
    rectifiable varifolds.

    Let 1 ≤ k ≤ n, and let F be an integrand of class 1 relative to
    G(n, k) with positive values ([dgpr_integrand]) satisfying (AC1)
    ([dgpr_AC1]), with λ(F) and Λ(F) of def:BF ([is_dgpr_lambda],
    [is_dgpr_Lambda]). Let V ∈ RV_k(R^n) satisfy ‖V‖(R^n) < ∞ and
    Θ^k(‖V‖, x) ≥ 1 for ‖V‖ almost all x. Suppose that the first
    variation δ_F V ([dgpr_first_variation_functional],
    DgprFirstVariationFunctional.v) is representable by integration with
    ‖δ_F V‖(R^n) < ∞, that is, some Radon measure ν over R^n with
    ν(R^n) < ∞ represents the variation of δ_F V of Federer 4.1.5 on the
    nonnegative continuous functions with compact support
    (mr:functionals). Then, with M = R^n ∩ { x : 1 ≤ Θ^k(‖V‖, x) < ∞ }
    ([dgpr_MS_set]) and C = [dgpr_compact_case_constant n C0],
    C0 = [dgpr_upper_entropy_constant n λ(F) Λ(F)],
        ‖V‖(R^n) ≤ C H^k(M)^{1/k} ‖δ_F V‖(R^n)        (eq:MS:MS)
    and, if k > 1,
        ‖V‖(R^n)^{(k − 1)/k} ≤ C ‖δ_F V‖(R^n)        (eq:MS:sobolev)
    ([dgpr_theorem_1_6]). The proof combines thm:main
    ([dgpr_theorem_1_1_rectifiable], DgprMainTheorem.v) with the
    reduction [dgpr_theorem_1_6_from_main] (DgprMichaelSimon.v); the
    constant C depends only on n, λ(F) and Λ(F). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions
  reals topology constructive_ereal.
From Federer Require Import InnerProductUP InnerNorm InnerMetric LinearBasis Hom HomInner
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates HilbertFormCompactness RealNormUP
  NormMetric RelativeClassUP PartialFunctionUP MeasureUP MeasureAlmostUP MeasureIntegralUP
  SummableRealFunctionUP RadonMeasureUP FunctionLatticeUP CompactSupportFunctionUP
  DistributionVariationUP SmoothFunctionSpaceUP SmoothTestSpaces SmoothTestEvaluation
  HausdorffMeasure RealPower MetricDensities.
From Allard Require Import AllardHomInnerProduct AllardOrthogonalProjectors AllardGrassmann
  AllardVarifolds AllardRectifiableVarifolds.
From DPGPR Require Import DgprAnisotropicIntegrand DgprKF DgprVarifoldWeight DgprMichaelSimon
  DgprUpperEntropy DgprCompactCase
  DgprFirstVariationFunctional DgprMainTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Theorem16.
Variable R : realType.
Variables n k : nat.
Hypothesis hk : (0 < k <= n)%N.
Local Notation Rn := (R_n R n).
Local Notation hBn := (@euclidean_inner_productP R n).
Local Notation Nn := (inner_norm hBn).
Local Notation hNn := (inner_norm_real_norm hBn).
Local Notation RnM := (inner_metric_space hBn).
Local Notation HK := (@hausdorff_measure R RnM k).
Local Notation GB := (grassmann_bundle R n k).

(** Source for [dgpr_theorem_1_6]: DPGPR 2026, Theorem 1.6, and
    blueprint thm:MS: under the hypotheses of thm:MS, with
    C = [dgpr_compact_case_constant n (dgpr_upper_entropy_constant n λ(F) Λ(F))],
    the inequality (eq:MS:MS) holds and, if k > 1, (eq:MS:sobolev)
    holds. Direct formalisation. *)
Theorem dgpr_theorem_1_6 (F : Hom Rn Rn -> R) (l L : R) (E : lmodType R) (ev : E -> Rn -> Rn)
    (hE : is_smooth_function_space hNn hNn setT ev) (V : set GB -> \bar R)
    (nu : set (real_norm_metric_space hNn) -> \bar R) :
  dgpr_integrand k F -> dgpr_AC1 k F -> is_dgpr_lambda hk F l -> is_dgpr_Lambda k F L ->
  is_rectifiable_varifold V -> (V setT < +oo)%E ->
  measure_almost_everywhere (varifold_weight V)
    [set x | exists t : \bar R,
      partial_function_graph (@metric_density R RnM k (varifold_weight V)) x t /\ (1 <= t)%E] ->
  is_measure nu -> is_radon_measure nu ->
  (forall f, positive_function_lattice
      (@compactly_supported_continuous_functions R (real_norm_metric_space hNn)) f ->
    exists b : R, is_distribution_variation_value Nn (smooth_test_values_hom hE)
      (dgpr_first_variation_functional hE V F) f b%:E /\
      is_measure_integral nu (real_total_integrand f) b%:E) ->
  (nu setT < +oo)%E ->
  (varifold_weight V setT <=
    (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n l L) *
      real_power (fine (HK (dgpr_MS_set k (varifold_weight V)))) k%:R^-1)%:E * nu setT)%E /\
  ((1 < k)%N ->
    ((real_power (fine (varifold_weight V setT)) ((k%:R - 1) / k%:R))%:E <=
      (dgpr_compact_case_constant n (dgpr_upper_entropy_constant n l L))%:E * nu setT)%E).
Proof.
move=> hF hAC hl hL hV hVf hdens hnu hnur hnug hnuf.
have [hl0 hlL _] := dgpr_KF_bounds hF.1 hAC hl hL.
have hL0 : 0 < L := lt_le_trans hl0 hlL.
have hS := @dgpr_first_variation_functional_variation R n k E ev hE V F hV.1 hVf hF.
have h := @dgpr_theorem_1_6_from_main R n k hk F hF hAC E ev hE V hV hVf hdens _ hS nu hnu hnur
  hnug hnuf.
have h1 := @dgpr_theorem_1_1_rectifiable R n k hk l L hl0 hL0.
have h0 := ltW (dgpr_compact_case_constant_gt0 n (dgpr_upper_entropy_constant n l L)).
have h2 := h _ l L h0 hl hL h1.
exact: h2.
Qed.

End Theorem16.
