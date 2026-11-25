(** De Philippis, Gennaioli, Pigati and Rindler (2026), blueprint
    section 3, lem:classes(cl:div) and lem:ibp: supporting facts on
    Lebesgue integrals over R^n. Gaussian weights are L^n summable
    (Federer 3.2.13, p. 250, and 2.10.27, p. 191); continuous dominated
    functions are summable (2.4.9, p. 85); L^n is invariant under
    translations (2.7.16, p. 135); pointwise limits of measurable
    functions are measurable (2.3.2(6), pp. 73-74). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology lra ring.
From Federer Require Import Hom RealNormUP RealMetricBackground GrassmannAbbreviations
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric HilbertFormCompactness
  NormDifferentialUP NormDifferentialLocal NormClassOneUP
  PartialFunctionUP PartialFunctionBasic PartialExtendedOrderLoci PartialAbsolutePartsGraph
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP MeasureIntegralUP
  MeasureIntegralGraphEquivalence MeasureAbsoluteSummability MeasureStepIntegralIdentification
  MeasurableTotalLimits NormClassZeroTotalMeasurable
  SummableRealFunctionUP SummableRealArithmetic ExtendedRealOrderLimit RealErrorOrderLimit
  RealDominatedIntegralLimit InvariantRealIntegral MeasurePushforward
  EuclideanLebesgueDimensions EuclideanAdditiveGroup EuclideanLebesgueTranslation
  EuclideanDistributionMeasureContext GaussianProductIntegrand GammaGaussianProductIntegral
  EuclideanPositiveAffineIntegral EulerGamma
  RealExponentialUP RealExponentialSealed RealExponentialLaws RealPower.
From DPGPR Require Import DgprGrowthClasses.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section LebesgueIntegrals.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Local Notation E := (@RealExponential.exponential R).

(** Source for [dgpr_standard_gaussian_summable]: Federer 3.2.13,
    p. 250, with z_j = 1/2 for every j: the function
    [x ↦ exp(-|x|^2)] is L^n summable. *)
Lemma dgpr_standard_gaussian_summable :
  summable_real_functions mu (fun x : X => E (- NX x ^+ 2)).
Proof.
pose z : 'I_n -> R := fun _ => 2^-1.
have hz : forall j, 0 < z j by move=> j; rewrite /z invr_gt0 ltr0n.
have h := @gamma_gaussian_product_integral R n z hz.
exists (\prod_j euler_gamma (hz j)).
have -> : (fun x : X => E (- NX x ^+ 2)) = gaussian_product_integrand z.
  apply: funext=> x; rewrite /gaussian_product_integrand /gaussian_angular_integrand.
  rewrite big1 ?mulr1 // => j _; rewrite /z mulfV ?pnatr_eq0 // subrr.
  exact: real_power_zero_exponent.
exact: h.
Qed.

(** Source for [dgpr_gaussian_summable]: Federer 3.2.13, p. 250,
    combined with the homothety law of 2.10.27, p. 191, for the radius
    c^(1/2): the function [x ↦ exp(-|x|^2/c)] is L^n summable
    whenever 0 < c. *)
Lemma dgpr_gaussian_summable (c : R) : 0 < c ->
  summable_real_functions mu (fun x : X => E (- NX x ^+ 2 / c)).
Proof.
move=> hc; have [a ha] := dgpr_standard_gaussian_summable.
have hr : 0 < Num.sqrt c by rewrite sqrtr_gt0.
have h := @euclidean_positive_affine_integral R n 0 (Num.sqrt c)
  (fun y => E (- NX y ^+ 2)) a hr ha.
exists (Num.sqrt c ^+ n * a).
have -> : (fun x : X => E (- NX x ^+ 2 / c)) =
    (fun x => (fun y => E (- NX y ^+ 2)) ((Num.sqrt c)^-1 *: (x - 0))).
  apply: funext=> x; rewrite subr0 inner_normZ ger0_norm ?invr_ge0 ?ltW //.
  by rewrite exprMn exprVn sqr_sqrtr ?(ltW hc) // mulNr [_ * c^-1]mulrC.
exact: h.
Qed.

(** Source for [dgpr_gaussian_weight_summable]: the weights
    c exp(-|x|^2/c) of def:classes are L^n summable, by 3.2.13,
    p. 250, of Federer. *)
Lemma dgpr_gaussian_weight_summable (c : R) : 0 < c ->
  summable_real_functions mu (fun x : X => dgpr_gaussian_weight c (NX x)).
Proof.
move=> hc; exact: (@summable_real_scale R _ mu hm _ c (dgpr_gaussian_summable hc)).
Qed.

(** Source for [dgpr_dominated_summable]: Federer 2.4.9, p. 85, last
    sentence of the proof: a measurable real function dominated by an
    L^n summable function is L^n summable. *)
Lemma dgpr_dominated_summable (f H : X -> R) :
  is_measure_measurable_function mu (real_total_integrand f) ->
  summable_real_functions mu H -> (forall x, `|f x| <= H x) ->
  summable_real_functions mu f.
Proof.
move=> hf hH hb.
have hdom : measure_almost_everywhere mu (partial_extended_le_locus
    (partial_extended_function_absolute_value (real_total_integrand f)) (real_total_integrand H)).
  apply: (@measure_almost_everywhere_mono R _ mu hm setT _ _ (measure_almost_everywhere_true hm))=> x _.
  exists (`|f x|)%:E,(H x)%:E; split.
  - exists (f x)%:E; split; first exact/real_total_integrand_graph.
    by rewrite abse_EFin.
  - split; first exact/real_total_integrand_graph.
    by rewrite lee_fin; exact: hb.
exact: (@measure_dominated_summable R _ mu hm _ _ hf hH hdom).1.
Qed.

(** Source for [dgpr_continuous_measurable]: Federer 2.3.2, p. 73,
    and 2.6.5, p. 120: a real function on R^n which is continuous with
    respect to the Euclidean norm is L^n measurable. *)
Lemma dgpr_continuous_measurable (f : X -> R) :
  norm_class_zero NX (fun t : R^o => `|t|) setT f ->
  is_measure_measurable_function mu (real_total_integrand f).
Proof.
move=> hf.
have h := @norm_class_zero_scalar_real_measurable R X NX hNX mu hm
  (@euclidean_distribution_measure_open R n) f hf.
exact: (@measurable_partial_real_embedding R _ mu hm _ h).
Qed.

(** Source for [dgpr_limit_measurable]: Federer 2.3.2(6), pp. 73-74:
    the pointwise limit of a sequence of L^n measurable real functions
    is L^n measurable. *)
Lemma dgpr_limit_measurable (f : nat -> X -> R) (g : X -> R) :
  (forall k, is_measure_measurable_function mu (partial_function_total (f k : X -> real_line_metric R))) ->
  (forall x e, 0 < e -> exists N, forall k, (N <= k)%N -> `|f k x - g x| < e) ->
  is_measure_measurable_function mu (real_total_integrand g).
Proof.
move=> hf hl.
have h : is_measure_measurable_function mu (partial_function_total (g : X -> real_line_metric R)).
  apply: (@measurable_total_functions_almost_limit R _ (real_line_metric R) mu hm
    (fun k => f k : X -> real_line_metric R) g setT hf (measure_almost_everywhere_true hm)).
  move=> x _ A hA.
  have [e he hball] := proj1 (metricType_numDomainType.nbhs_mdistP (g x : real_line_metric R) A) hA.
  have [N hN] := hl x e he.
  exists N=> // k hk; apply: hball.
  change (is_true (mdist (g x : real_line_metric R) (f k x) < e)).
  by rewrite real_line_metric_distanceE distrC; exact: hN.
exact: (@measurable_partial_real_embedding R _ mu hm _ h).
Qed.

(** Source for [dgpr_translation_integral]: Federer 2.7.16, p. 135:
    L^n is invariant under the translation [x ↦ x + w], hence so are
    integrals of real functions. *)
Lemma dgpr_translation_integral (f : X -> R) (w : X) (a : R) :
  is_measure_integral mu (real_total_integrand f) a%:E ->
  is_measure_integral mu (real_total_integrand (fun x => f (x + w))) a%:E.
Proof.
move=> hf.
have hinj : injective (@euclidean_translation R n w) by move=> x y; exact: addrI.
have h := @invariant_real_total_integral R _ mu hm (@euclidean_translation R n w) f a hinj
  (euclidean_lebesgue_translation_pushforward w) hf.
have -> : (fun x : X => f (x + w)) = (fun x => f (euclidean_translation w x)).
  by apply: funext=> x; rewrite /euclidean_translation addrC.
exact: h.
Qed.

End LebesgueIntegrals.
