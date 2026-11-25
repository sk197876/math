(** Federer (1969), 2.3.2, p. 74, numerical operations: negation and
    positive and negative parts of extended-real measurable functions. The
    scalar operations are those already formalised from 2.1.1, pp. 51–52. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages PartialFunctionPostcomposition
  PartialFunctionGraphEquivalence MeasureUP MeasureSplit MeasureAlmostUP MeasurableFunctionUP
  MeasurableGraphEquivalence ExtendedRealPartial ExtendedRealOrderTopology CountableOrderIntervals
  MeasurableExtendedRationalRays.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_extended_negation]: supporting negation
    case of the basic numerical operations in Federer 2.3.2,
    p. 74. It interchanges lower and upper order rays,
    including both infinite endpoints. *)
Lemma measurable_extended_negation (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_function_postcompose f (fun y => (- y : extended_real_line R))).
Proof.
move=> hf; have hd : measure_almost_everywhere mu
    (partial_function_domain (partial_function_postcompose f (fun y => (- y : extended_real_line R)))).
  rewrite partial_function_postcompose_domain; exact: measurable_function_domain hf.
apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm _ hd))=> q.
rewrite partial_function_postcompose_preimage.
have he : [set y : \bar R | - y < (ratr q : R)%:E] = [set y | - (ratr q : R)%:E < y].
  by apply/seteqP; split=> y; rewrite /= lteNl.
rewrite he; apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hf).
exact: order_strict_upper_ray_open.
Qed.

(** Source for [measurable_extended_positive_part]: direct forward
    positive-part assertion in Federer 2.3.2, p. 74 *)
Lemma measurable_extended_positive_part (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_function_postcompose f (@extended_positive_part R : extended_real_line R -> extended_real_line R)).
Proof.
move=> hf; have hd : measure_almost_everywhere mu
    (partial_function_domain (partial_function_postcompose f (@extended_positive_part R : extended_real_line R -> extended_real_line R))).
  rewrite partial_function_postcompose_domain; exact: measurable_function_domain hf.
apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm _ hd))=> q.
rewrite partial_function_postcompose_preimage.
case hq : (0 < (ratr q : R)%:E).
- have he : [set y : \bar R | extended_positive_part y < (ratr q : R)%:E] =
      [set y | y < (ratr q : R)%:E].
    by apply/seteqP; split=> y; rewrite /= /extended_positive_part gt_max hq andbT.
  rewrite he; apply: (@measurable_function_open_preimage R X (extended_real_line R) mu f hf).
  exact: order_strict_lower_ray_open.
- have he : [set y : \bar R | extended_positive_part y < (ratr q : R)%:E] = set0.
    apply/seteqP; split=> y; last by move=> [].
    by rewrite /= /extended_positive_part gt_max hq andbF.
  rewrite he partial_function_preimage_empty; exact: measure_measurable_empty hm.
Qed.

(** Source for [measurable_extended_negative_part]: direct forward
    negative-part assertion in Federer 2.3.2, p. 74 *)
Lemma measurable_extended_negative_part (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_function_postcompose f (@extended_negative_part R : extended_real_line R -> extended_real_line R)).
Proof.
move=> hf.
have hn := @measurable_extended_negation R X mu hm f hf.
have hp := @measurable_extended_positive_part R X mu hm _ hn.
apply: (@measurable_function_graph_equivalent R X (extended_real_line R) mu _ _ _ hp).
move=> x y; exact: partial_function_postcomposition_associative.
Qed.

(** Source for [measurable_extended_parts_iff]: direct equivalence between
    measurability of f and of both f-plus and f-minus in Federer 2.3.2, p.
    74 The converse uses positive and nonpositive threshold cases, so it
    does not assume arithmetic is total. *)
Theorem measurable_extended_parts_iff (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (f : partial_function X (extended_real_line R)) :
  is_measure_measurable_function mu f <->
  is_measure_measurable_function mu (partial_function_postcompose f (@extended_positive_part R : extended_real_line R -> extended_real_line R)) /\
  is_measure_measurable_function mu (partial_function_postcompose f (@extended_negative_part R : extended_real_line R -> extended_real_line R)).
Proof.
split.
- move=> hf; split.
  + exact: (@measurable_extended_positive_part R X mu hm f hf).
  + exact: (@measurable_extended_negative_part R X mu hm f hf).
- move=> [hp hn].
  have hd := measurable_function_domain hp; rewrite partial_function_postcompose_domain in hd.
  apply: (proj2 (@measurable_extended_rational_lower_rays_iff R X mu hm f hd))=> q.
  case hq : (0 < (ratr q : R)%:E).
  + have h := @measurable_function_open_preimage R X (extended_real_line R) mu _ hp
      [set y | y < (ratr q : R)%:E] (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E).
    rewrite partial_function_postcompose_preimage in h.
    have he : [set y : \bar R | extended_positive_part y < (ratr q : R)%:E] =
        [set y | y < (ratr q : R)%:E].
      by apply/seteqP; split=> y; rewrite /= /extended_positive_part gt_max hq andbT.
    by rewrite he in h.
  + have h := @measurable_function_open_preimage R X (extended_real_line R) mu _ hn
      [set y | - (ratr q : R)%:E < y] (@order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (- (ratr q : R)%:E)).
    rewrite partial_function_postcompose_preimage in h.
    have hscalar (y : \bar R) : (- (ratr q : R)%:E < extended_negative_part y) =
        (y < (ratr q : R)%:E).
      by rewrite /extended_negative_part /extended_positive_part lt_max oppe_lt0 hq orbF lteN2.
    have he : [set y : \bar R | - (ratr q : R)%:E < extended_negative_part y] =
        [set y | y < (ratr q : R)%:E].
      apply/seteqP; split=> y.
      * change ((- (ratr q : R)%:E < extended_negative_part y) -> (y < (ratr q : R)%:E)).
        by rewrite hscalar.
      * change ((y < (ratr q : R)%:E) -> (- (ratr q : R)%:E < extended_negative_part y)).
        by rewrite hscalar.
    by rewrite he in h.
Qed.
