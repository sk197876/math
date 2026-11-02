(** Federer (1969), 3.2.20, p. 257: supporting measurability
    of weighted truncations when extending 3.2.5(2), pp. 244–245,
    by 2.4.7, p. 84. Both arguments may take infinite values. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic PartialFunctionUP
  PartialFunctionPreimages MeasureUP MeasureSplit MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP
  MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_total_extended_minimum]: supporting numerical
    closure in Federer 2.3.2, p. 74, for the increasing-convergence
    extension of the area formula in 3.2.20, p. 257.
    The lower-ray inverse image of the minimum is the union of
    the two lower-ray inverse images; no arithmetic domain is removed. *)
Lemma measurable_total_extended_minimum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> extended_real_line R) :
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  is_measure_measurable_function mu (partial_function_total (fun x=>Order.min (f x) (g x))).
Proof.
move=> hf hg.
have hd : measure_almost_everywhere mu
    (partial_function_domain (partial_function_total (fun x=>Order.min (f x) (g x)))).
  rewrite partial_function_total_domain; exact: (measure_almost_everywhere_true hm).
apply: (@measurable_extended_rational_lower_rays_iff R X mu hm _ hd).2=> q.
have hfd : measure_almost_everywhere mu (partial_function_domain (partial_function_total f)).
  rewrite partial_function_total_domain; exact: (measure_almost_everywhere_true hm).
have hgd : measure_almost_everywhere mu (partial_function_domain (partial_function_total g)).
  rewrite partial_function_total_domain; exact: (measure_almost_everywhere_true hm).
have hfm := (@measurable_extended_rational_lower_rays_iff R X mu hm _ hfd).1 hf q.
have hgm := (@measurable_extended_rational_lower_rays_iff R X mu hm _ hgd).1 hg q.
have he : partial_function_preimage (partial_function_total (fun x=>Order.min (f x) (g x)))
    [set y|y<(ratr q:R)%:E]=
    partial_function_preimage (partial_function_total f) [set y|y<(ratr q:R)%:E] `|`
    partial_function_preimage (partial_function_total g) [set y|y<(ratr q:R)%:E].
  rewrite !partial_function_total_preimage; apply/seteqP; split=> x; rewrite /= gt_min.
  - move=> /orP [hf'|hg']; [by left|by right].
  - move=> [hf'|hg']; apply/orP; [by left|by right].
rewrite he; exact: (measure_measurable_union hm hfm hgm).
Qed.
