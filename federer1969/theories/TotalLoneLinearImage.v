(** Federer (1969), 4.1.19, p. 377: take
    scalar components of the bounded L1
    functional and expand the finite-dimensional
    coefficient fields. The original L1 norm
    bound follows from the already proved dominated
    integral and bounded-linear continuity laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormBoundedLinearTopology PartialFunctionBasic MeasureUP
  MeasurableFunctionUP MeasurableNormedFunctionUP MeasurableTotalBasic
  BorelFunctionBasic MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SummableRealArithmetic MeasureLpNorm
  MeasureLpMembershipUP VectorDaniellHypotheses VectorDaniellRationalSpan
  VectorDaniellPairingMeasurability SeparableVectorLone.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [total_lone_bounded_linear_image]:
    bounded-linear coefficient maps preserve L1,
    supporting the representation in Federer 4.1.19,
    p. 377, through 2.4.12, pp. 86–87.
    Only the target's supplied separability is used;
    the actual coefficient targets here are finite dimensional.
    The original source measure may be infinite. *)
Theorem total_lone_bounded_linear_image
    (R : realType) (X : choiceType) (A B : lmodType R)
    (NA : A -> R) (NB : B -> R)
    (hNA : is_real_norm NA) (hNB : is_real_norm NB)
    (hSep : is_separable_normed_space hNB)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (L : Hom A B) (c : R) (hC : 0 <= c)
    (hBound : forall v, NB (L v) <= c*NA v)
    (f : X -> real_norm_metric_space hNA) :
  is_measure_lp_function mu 1 (partial_function_total f) ->
  is_measure_lp_function mu 1
    (partial_function_total (fun x => (L (f x) : real_norm_metric_space hNB))) /\
  fine (measure_lp_norm mu NB 1 (partial_function_total
    (fun x => (L (f x) : real_norm_metric_space hNB)))) <=
    c*fine (measure_lp_norm mu NA 1 (partial_function_total f)).
Proof.
move=> hF.
pose g := fun x => (L (f x) : real_norm_metric_space hNB).
have hContinuous : continuous (fun v : real_norm_metric_space hNA =>
    (L v : real_norm_metric_space hNB)).
  apply: (@norm_bounded_linear_continuous R A B NA NB hNA hNB L).
  by exists c; split.
have hGMeas := @measurable_total_borel_postcomposition R X
  (real_norm_metric_space hNA) (real_norm_metric_space hNB) mu hm
  f (fun v => (L v : real_norm_metric_space hNB)) hF.2.1.1
  (continuous_borel_function hContinuous).
have hNonnegative := @measure_lp_norm_nonnegative R X A NA hNA mu 1
  (partial_function_total f) hm (lexx 1) hF.2.1.1.
have hFinite : measure_lp_norm mu NA 1 (partial_function_total f) \is a fin_num.
  by rewrite (ge0_fin_numE hNonnegative); exact: hF.2.2.1.
pose a := fine (measure_lp_norm mu NA 1 (partial_function_total f)).
have hValue : measure_lp_norm mu NA 1 (partial_function_total f) = a%:E.
  by rewrite /a fineK.
have hNormF := @total_vector_norm_integral R X A NA hNA mu hm f hF.2.1.1.
rewrite hValue in hNormF.
have hScaled := @real_total_integral_scale R X mu hm
  (fun x => NA (f x)) a c hNormF.
have hNormG := @total_vector_norm_integral R X B NB hNB mu hm g hGMeas.
have hDom x : `|NB (g x)| <= c*NA (f x).
  rewrite (ger0_norm (real_seminorm_nonnegative hNB.1 _)).
  exact: hBound.
have [b [hIntegral hCap]] := @real_total_dominated_integral R X mu hm
  (fun x => NB (g x)) (fun x => c*NA (f x)) (c*a)
  hNormG.1 hScaled hDom.
have [D hD] := @rational_dense_subspace_exists R B NB hNB hSep.
have hMember := @separable_vector_summable_norm_lone R X B NB hNB D hD
  mu hm g b hGMeas hIntegral.
split; first exact: hMember.
have hEqual : measure_lp_norm mu NB 1 (partial_function_total g) = b%:E.
  exact: (measure_integral_unique hNormG hIntegral).
rewrite hEqual.
exact: (le_trans (ler_norm b) hCap).
Qed.
