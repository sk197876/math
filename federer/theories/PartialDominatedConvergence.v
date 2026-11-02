(** Federer (1969), 2.4.9, p. 85: supporting graph formulations of pointwise
    convergence and the common finite-value region for a sequence dominated
    by a summable h. Source context: MeasureIntegralAlmostEquality.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealOrderLimit PartialFunctionUP MeasureUP MeasureAlmostUP MeasureAlmostBasic
  PartialExtendedOrderLoci PartialAbsolutePartsGraph MeasureIntegralUP MeasureSummableFiniteValues ExtendedDominatedLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_convergence_locus]: direct graph
    formulation of fn(x) tending to g(x) in Federer
    2.4.9, p. 85. All sequence values must exist
    at the point in question; null exceptional sets remain allowed. *)
Definition partial_extended_convergence_locus (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :=
  [set x | exists (u : nat -> \bar R) z,
    (forall n, partial_function_graph (f n) x (u n)) /\
    partial_function_graph g x z /\ extended_order_limit u z].

(** Source for [partial_dominated_real_limit_locus]: supporting
    common region of finite values for Federer 2.4.9,
    p. 85, retaining explicit domination and convergence. *)
Definition partial_dominated_real_limit_locus (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :=
  [set x | exists (u : nat -> R) (z c : R),
    (forall n, partial_function_graph (f n) x (u n)%:E) /\
    partial_function_graph g x z%:E /\ partial_function_graph h x c%:E /\
    (forall n, (`|u n| <= c)%R) /\ (`|z| <= c)%R /\
    extended_order_limit (fun n => (u n)%:E) z%:E].

(** Source for [measure_dominated_finite_limit_region]: supporting
    conull region on which all scalar calculations in Federer
    2.4.9, p. 85, are finite. This is obtained
    from summability of h, countably many bounds and pointwise
    convergence, not imposed as an additional hypothesis. *)
Lemma measure_dominated_finite_limit_region (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_measure_summable mu h ->
  (forall n, measure_almost_everywhere mu
    (partial_extended_le_locus (partial_extended_function_absolute_value (f n)) h)) ->
  measure_almost_everywhere mu (partial_extended_convergence_locus f g) ->
  measure_almost_everywhere mu (partial_dominated_real_limit_locus f g h).
Proof.
move=> hs hb hl.
have hh := @measure_summable_finite_almost R X mu hm h hs.
have hall := @measure_almost_everywhere_countable R X [the choiceType of (nat : Type)] mu hm setT
  (fun n => partial_extended_le_locus (partial_extended_function_absolute_value (f n)) h)
  (countableP setT) (fun n _ => hb n).
have hg := @measure_almost_everywhere_and R X mu hm _ _ hl
  (@measure_almost_everywhere_and R X mu hm _ _ hh hall).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hg).
move=> x [[u [z [hu [hz hlim]]]] [[c [hc hcfin]] hbounds]].
have hbu n : `|u n| <= c.
  have [v [w [[r [hr erv]] [hw hle]]]] := hbounds n I.
  have er := partial_function_single_valued (hu n) hr.
  have ew := partial_function_single_valued hc hw.
  by rewrite -erv -er -ew in hle.
have hbc n : `|u n| <= (fine c)%:E by rewrite fineK //; exact: hbu.
have [huf hzf] := extended_finite_dominated_values hlim hbc.
have hzb := extended_dominated_limit_bound hlim hbu.
exists (fun n => fine (u n)), (fine z), (fine c).
split; first by move=> n; rewrite fineK.
split; first by rewrite fineK.
split; first by rewrite fineK.
split.
- move=> n; have hn := hbu n.
  by rewrite -(fineK (huf n)) -(fineK hcfin) in hn.
split.
- by rewrite -(fineK hzf) -(fineK hcfin) in hzb.
- have he : (fun n => (fine (u n))%:E) = u.
    by apply/funext=> n; rewrite fineK.
  by rewrite he fineK.
Qed.

(** Source for [measure_dominated_limit_bound]: domination of
    the limit g by h in Federer 2.4.9, p. 85,
    used to infer summability of g. *)
Lemma measure_dominated_limit_bound (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  measure_almost_everywhere mu (partial_dominated_real_limit_locus f g h) ->
  measure_almost_everywhere mu (partial_extended_le_locus (partial_extended_function_absolute_value g) h).
Proof.
move=> hg; apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hg).
move=> x [u [z [c [hu [hz [hc [hub [hzb hlim]]]]]]]].
exists (`|z|%:E),c%:E; split; first by exists z%:E; split.
by split.
Qed.
