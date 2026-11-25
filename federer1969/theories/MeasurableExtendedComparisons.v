(** Supporting measurable comparisons for Federer (1969), 2.9.8, p. 156: the
    integral-density measure used in its proof must be Borel regular. We
    prove this background consequence of the ray criterion 2.3.2(2), p. 73,
    using rational separation. Comparisons require both partial values; no
    undefined difference of infinities is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialExtendedOrderLoci
  MeasureUP MeasureAlmostUP MeasureFiniteClosure MeasureCountableClosure
  MeasurableFunctionUP MeasurableFunctionBorel CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_lt_locus]: supporting strict comparison set
    for the density regularity argument of Federer 2.9.8, p. 156 Both graph
    witnesses must exist, including at infinite values. *)
Definition partial_extended_lt_locus (R : realType) (X : Type)
    (f g : partial_function X (extended_real_line R)) :=
  [set x | exists a b, partial_function_graph f x a /\ partial_function_graph g x b /\ a<b].

(** Source for [measurable_extended_strict_comparison]: supporting
    ray-criterion consequence for Federer 2.9.8, p. 156, specifically the
    comparison set. Strict order is separated by a finite rational even at
    infinite endpoints. *)
Lemma measurable_extended_strict_comparison (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  is_measure phi -> is_measure_measurable_function phi f -> is_measure_measurable_function phi g ->
  measure_measurable phi (partial_extended_lt_locus f g).
Proof.
move=> hm hf hg.
have he : partial_extended_lt_locus f g=\bigcup_q
    (partial_function_preimage f [set y | y<(ratr q : R)%:E] `&`
     partial_function_preimage g [set y | (ratr q : R)%:E<y]).
  apply/seteqP; split.
  - move=> x [a [b [ha [hb hab]]]].
    have [q [haq hqb]] := @extended_rationals_order_dense R a b hab.
    exists q=> //; split; [by exists a|by exists b].
  - move=> x [q _ [[a [ha haq]] [b [hb hqb]]]].
    exists a,b; split=> //; split=> //; exact: lt_trans haq hqb.
rewrite he; apply: (@measure_measurable_countable_union R X _ phi hm setT _ (countableP _))=> q _.
apply: (@measure_measurable_intersection R X phi hm).
- apply: (@measurable_function_open_preimage R X (extended_real_line R) phi f hf).
  exact (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E).
- apply: (@measurable_function_open_preimage R X (extended_real_line R) phi g hg).
  exact (@order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] (ratr q : R)%:E).
Qed.

(** Source for [measurable_extended_weak_comparison]: Supporting Federer
    2.9.8, p. 156.Take the complement of reverse strict order inside the
    common partial domain, rather than in all of X. *)
Lemma measurable_extended_weak_comparison (R : realType) (X : choiceType)
    (phi : set X -> \bar R) (f g : partial_function X (extended_real_line R)) :
  is_measure phi -> is_measure_measurable_function phi f -> is_measure_measurable_function phi g ->
  measure_measurable phi (partial_extended_le_locus f g).
Proof.
move=> hm hf hg.
have he : partial_extended_le_locus f g=
    (partial_function_domain f `&` partial_function_domain g) `\` partial_extended_lt_locus g f.
  apply/seteqP; split.
  - move=> x [a [b [ha [hb hab]]]]; split.
    + split; [by exists a|by exists b].
    + move=> [b' [a' [hb' [ha' hba]]]].
      have ea := partial_function_single_valued ha ha'.
      have eb := partial_function_single_valued hb hb'.
      by move: hba; rewrite -ea -eb ltNge hab.
  - move=> x [[[a ha] [b hb]] hn]; exists a,b; split=> //; split=> //.
    rewrite leNgt; apply/negP=> hba; apply: hn; exists b,a; by split=> //; split.
rewrite he; apply: (@measure_measurable_difference R X phi hm).
- apply: (@measure_measurable_intersection R X phi hm).
  + exact (@conull_partial_function_domain_measurable R X (extended_real_line R) phi hm f (measurable_function_domain hf)).
  + exact (@conull_partial_function_domain_measurable R X (extended_real_line R) phi hm g (measurable_function_domain hg)).
- exact (@measurable_extended_strict_comparison R X phi g f hm hg hf).
Qed.
