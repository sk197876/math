(** Federer (1969), 2.4.11, proof p. 86: the truncations gn are measurable
    by the numerical closure in 2.3.2, p. 74. We prove it directly from
    strict rational-ray inverse images. Source context:
    PartialUpperTruncation.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic PartialFunctionPostcomposition
  PartialUpperTruncation MeasureUP MeasureAlmostUP MeasurableFunctionUP MeasurableFunctionBorel
  MeasurableExtendedRationalRays CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_upper_truncation]: supporting
    measurability of the bounded approximants in Federer
    2.4.11, proof p. 86, including infinite input values. *)
Lemma measurable_upper_truncation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X (extended_real_line R)) c :
  is_measure_measurable_function mu f -> is_measure_measurable_function mu (partial_upper_truncation f c).
Proof.
move=> hf; have hd : measure_almost_everywhere mu (partial_function_domain (partial_upper_truncation f c)).
  rewrite partial_upper_truncation_domain; exact: measurable_function_domain hf.
apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm _ hd))=> q.
rewrite /partial_upper_truncation partial_function_postcompose_preimage.
have [hc|hc] := ltP c (ratr q : R)%:E.
- have he : [set y : \bar R | Order.min y c < (ratr q : R)%:E]=setT.
    apply/seteqP; split=> // y _; by rewrite /= gt_min hc orbT.
  rewrite he partial_function_preimage_whole.
  exact (@conull_partial_function_domain_measurable R X (extended_real_line R) mu hm f (measurable_function_domain hf)).
- have he : [set y : \bar R | Order.min y c < (ratr q : R)%:E]=[set y | y < (ratr q : R)%:E].
    apply/seteqP; split=> y; by rewrite /= gt_min (le_gtF hc) orbF.
  rewrite he; apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hf).
  exact: order_strict_lower_ray_open.
Qed.
