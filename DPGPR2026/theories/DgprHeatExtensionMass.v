(** De Philippis, Gennaioli, Pigati and Rindler (2026), section 3,
    conservation of mass by heat extensions; blueprint dgpr_blueprint.tex,
    lem:heat_extension(4), for Z = R and f >= 0. The proof is that of the
    blueprint: Fubini's theorem (Federer 2.6.2) for L^n x nu applied to
    [(x,y) |-> p_s(x-y) f(y)], the invariance of L^n under translations
    (2.7.16) and lem:kernel(1). The product function is measurable because
    open subsets of R^n x R^n are L^n x nu measurable (2.6.2 with the
    countable base of R^n). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP NormMetric NormMetricSubtractContinuity HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  PartialExtendedOrderLoci PartialProductSections MeasureUP MeasureSplit MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP MeasureIntegralGraphEquivalence MeasureIntegralUniqueness
  MeasureIntegralBounds MeasureNonnegativeIntegral SummableRealFunctionUP SummableRealArithmetic CompleteMetricUP
  NormClassOneUP NormClassZeroTopology NormDifferentialUP ScalarNormMetricCompleteness LocalUniquenessExample
  TotalScalarLpUP TotalScalarArithmetic ScalarCountableEmbedding
  ProductMeasure ProductBorelRectangles ProductFunctionMeasurability ProductFunctionFubini
  ParameterizedIntegralUP ParameterizedIntegral CountablyMeasurableUP CountablyMeasurableBasic
  CountablyMeasurableProduct CountablyMeasurableFunctions CountablyMeasurableNullModification
  EuclideanNormCountableBase EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  RealExponentialUP RealExponentialSealed CircularTrigonometrySealed.
From DPGPR Require Import DgprParameterIntegralDifferential DgprHeatKernel DgprHeatKernelDifferential
  DgprHeatExtension DgprHeatSemiconvex DgprLebesgueIntegrals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section HeatMass.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T := (real_norm_metric_space hN).
Local Notation p := (@dgpr_heat_kernel R n).
Local Notation hA := (@scalar_absolute_value_norm R).
Local Notation S := (real_norm_metric_space hA).
Local Notation hZ1 := (@scalar_norm_metric_complete R).
Local Notation LL := (@euclidean_lebesgue_measure R n).
Local Notation hLL := (euclidean_lebesgue_is_measure R n).
Variable nu : set X -> \bar R.
Hypothesis hnu : is_measure nu.
Hypothesis hOpen : forall A : set X, @open T A -> measure_measurable nu A.
Variable m : R.
Hypothesis hmass : nu setT = m%:E.
Local Notation mu := (product_measure hLL hnu).
Local Notation hmu := (product_measure_is_measure hLL hnu).

(** Source for [dgpr_product_open_measurable]: open subsets of
    R^n x R^n are L^n x nu measurable (Federer 2.6.2, with the countable
    base of R^n of 2.6.5 and the measurability of open sets for L^n and
    nu); blueprint lem:heat_extension(4), proof. *)
Lemma dgpr_product_open_measurable (O : set (T * T)) : open O -> measure_measurable mu O.
Proof.
have [U hU] := euclidean_norm_countable_open_base R n.
exact: (@product_open_sets_measurable R [the topologicalType of T] [the topologicalType of T]
  LL nu hLL hnu U U hU hU (@euclidean_distribution_measure_open R n) hOpen O).
Qed.

(** Source for [dgpr_kernel_difference_measurable]: the continuous map
    [(x,y) |-> p_s(x-y)] is L^n x nu measurable (Federer 2.3.2, 2.6.2);
    blueprint lem:heat_extension(4), proof. *)
Lemma dgpr_kernel_difference_measurable (s : R) : 0 < s ->
  is_measure_measurable_function mu
    (partial_function_total (fun q : T * T => (p s (q.1 - q.2) : S))).
Proof.
move=> hs.
have hk : continuous (fun z : T => (p s z : S)).
  move=> z; exact: (@norm_class_zero_continuous_at R X R^o N (fun t : R^o => `|t|) hN hA setT (p s) z
    (dgpr_kernel_class_zero hs) I).
have hsub := @real_norm_metric_subtract_continuous R X N hN.
have hK : continuous (fun q : T * T => (p s (q.1 - q.2) : S)).
  by move=> q; apply: (continuous_comp (hsub q)); exact: hk.
constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hmu.
- move=> W hW; rewrite partial_function_total_preimage; apply: dgpr_product_open_measurable.
  by apply: open_comp hW => q _; exact: hK.
Qed.

Variable g : X -> R^o.
Hypothesis hg : is_measure_measurable_function nu (partial_function_total (fun y => (g y : S))).
Variable M : R.
Hypothesis hgM : forall y, `|g y| <= M.
Hypothesis hg0 : forall y, 0 <= g y.
Local Notation u := (@dgpr_heat_extension R n nu hnu R^o (fun t : R^o => `|t|) hA hZ1 g).

(** Source for [dgpr_mass_integrand_measurable]: the function
    [(x,y) |-> p_s(x-y) f(y)] is L^n x nu measurable (Federer 2.3.3,
    2.6.2); blueprint lem:heat_extension(4), proof. *)
Lemma dgpr_mass_integrand_measurable (s : R) : 0 < s ->
  is_measure_measurable_function mu
    (real_total_integrand (fun q : X * X => p s (q.1 - q.2) * g q.2)).
Proof.
move=> hs.
have h2 := @product_measurable_second_function R X X [the topologicalType of S] LL nu hLL hnu
  (fun y => (g y : S)) hg.
have h := @measurable_total_scalar_product R (X * X)%type mu hmu
  (fun q : X * X => (p s (q.1 - q.2) : S)) (fun q : X * X => (g q.2 : S))
  (dgpr_kernel_difference_measurable hs) h2.
exact: (scalar_real_integrand_measurable hmu h).
Qed.

(** Source for [dgpr_mass_section_x]: for fixed x the integral of
    [y |-> p_s(x-y) f(y)] with respect to nu is u(s,x) (Federer 2.4.12);
    blueprint lem:heat_extension(4), proof. *)
Lemma dgpr_mass_section_x (s : R) (x : X) : 0 < s ->
  is_measure_integral nu (real_total_integrand (fun y => p s (x - y) * g y)) (u s x)%:E.
Proof.
move=> hs.
exact: (dgpr_real_convolution_integral hnu hOpen hmass x hg hgM (dgpr_kernel_class_zero hs)
  (fun z => dgpr_kernel_abs_le z hs)).
Qed.

(** Source for [dgpr_mass_section_y]: for fixed y the integral of
    [x |-> p_s(x-y) f(y)] with respect to L^n is f(y), by the invariance
    of L^n under translations (Federer 2.7.16) and lem:kernel(1);
    blueprint lem:heat_extension(4), proof. *)
Lemma dgpr_mass_section_y (s : R) (y : X) : 0 < s ->
  is_measure_integral LL (real_total_integrand (fun x => p s (x - y) * g y)) (g y)%:E.
Proof.
move=> hs.
have h := dgpr_translation_integral (- y) (dgpr_kernel_mass n hs).
have h2 := real_total_integral_scale hLL (g y) h.
rewrite mulr1 in h2.
apply: (measure_integral_graph_equivalent _ h2) => x z.
by rewrite !real_total_integrand_graph mulrC.
Qed.

(** Source for [dgpr_heat_extension_mass]: DPGPR 2026, section 3;
    blueprint lem:heat_extension(4): for Z = R and f >= 0 the integral of
    u_s with respect to L^n equals the integral of f with respect to nu
    (Federer 2.6.2). *)
Theorem dgpr_heat_extension_mass (s b : R) : 0 < s ->
  is_measure_integral nu (real_total_integrand g) b%:E ->
  is_measure_integral LL (real_total_integrand (u s)) b%:E.
Proof.
move=> hs hb.
pose F := real_total_integrand (fun q : X * X => p s (q.1 - q.2) * g q.2).
have hF := dgpr_mass_integrand_measurable hs.
have hpos : measure_almost_everywhere mu (partial_extended_nonnegative_locus F).
  apply: (measure_almost_everywhere_mono hmu _ (measure_almost_everywhere_true hmu)) => q _.
  exists (p s (q.1 - q.2) * g q.2)%:E; split; first by rewrite real_total_integrand_graph.
  by rewrite lee_fin mulr_ge0 // ltW // dgpr_kernel_gt0.
have [hI _] := nonnegative_measurable_function_integral hmu hF hpos.
have hfin : (nu setT < +oo)%E by rewrite hmass ltry.
have hWhole := @product_whole_countably_measurable R X X LL nu hLL hnu
  (euclidean_lebesgue_countably_measurable R n)
  (finite_measurable_set_countably_measurable (measure_measurable_whole hnu) hfin).
have hCount := countably_measurable_function_on_countable_source hmu
  (@CountablyMeasurableNullModification.extended_real_zero_closed R) hWhole hI.1.
have [hV hH] := @product_function_fubini R X X LL nu hLL hnu F _ hI hCount.
have hgb : is_measure_integral nu (real_total_integrand g) (measure_lower_integral mu F).
  apply: (measure_integral_graph_equivalent _ hH) => y a.
  rewrite parameterized_integral_specification real_total_integrand_graph.
  have hy : is_measure_integral LL (partial_product_horizontal_section F y) (g y)%:E.
    apply: (measure_integral_graph_equivalent _ (dgpr_mass_section_y y hs)) => x z.
    change (partial_function_graph (real_total_integrand (fun x => p s (x - y) * g y)) x z <->
      partial_function_graph F (x, y) z).
    by rewrite !real_total_integrand_graph.
  split; first by move=> ha; exact: esym (measure_integral_unique ha hy).
  by move=> <-.
have hVb := measure_integral_unique hgb hb.
rewrite -hVb.
apply: (measure_integral_graph_equivalent _ hV) => x a.
rewrite parameterized_integral_specification real_total_integrand_graph.
have hx : is_measure_integral nu (partial_product_vertical_section F x) (u s x)%:E.
  apply: (measure_integral_graph_equivalent _ (dgpr_mass_section_x x hs)) => y z.
  change (partial_function_graph (real_total_integrand (fun y => p s (x - y) * g y)) y z <->
    partial_function_graph F (x, y) z).
  by rewrite !real_total_integrand_graph.
split; first by move=> ha; exact: esym (measure_integral_unique ha hx).
by move=> <-.
Qed.

End HeatMass.
