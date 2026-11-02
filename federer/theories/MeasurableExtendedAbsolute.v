(** Federer (1969), 2.3.2, p. 74: absolute values of extended-real
    measurable functions remain measurable. The proof uses the open interval
    between the negative and positive thresholds. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPostcomposition MeasureUP MeasureAlmostUP
  MeasureFiniteClosure MeasurableFunctionUP CountableOrderIntervals ExtendedRealOrderTopology
  MeasurableOrderRays MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_absolute_strict_finite_bound]: supporting
    scalar interval identity for the absolute-value assertion in
    Federer 2.3.2, p. 74. Both infinite values fail every
    finite absolute-value bound. *)
Lemma extended_absolute_strict_finite_bound (R : realType) (y : \bar R) (r : R) :
  (`|y| < r%:E) = ((-r)%:E < y) && (y < r%:E).
Proof.
case: y=> [y| |] /=.
- by rewrite !lte_fin ltr_norml.
- by rewrite (ltNge +oo r%:E) leey andbF.
- by rewrite (ltNge +oo r%:E) leey.
Qed.

(** Source for [measurable_extended_absolute_value]: direct
    absolute-value assertion in Federer 2.3.2, p. 74,
    immediately after the positive/negative-part criterion. *)
Theorem measurable_extended_absolute_value (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu
    (partial_function_postcompose f (fun y => (`|y| : extended_real_line R))).
Proof.
move=> hf; have hd : measure_almost_everywhere mu
    (partial_function_domain (partial_function_postcompose f (fun y => (`|y| : extended_real_line R)))).
  rewrite partial_function_postcompose_domain; exact: measurable_function_domain hf.
apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm _ hd))=> q.
rewrite partial_function_postcompose_preimage.
have he : [set y : \bar R | `|y| < (ratr q : R)%:E] =
    [set y | (-ratr q : R)%:E < y] `&` [set y | y < (ratr q : R)%:E].
  apply/seteqP; split=> y; rewrite /= extended_absolute_strict_finite_bound; by move/andP.
rewrite he partial_preimage_intersection.
apply: (@measure_measurable_intersection R X mu hm).
- apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hf).
  exact: order_strict_upper_ray_open.
- apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hf).
  exact: order_strict_lower_ray_open.
Qed.
