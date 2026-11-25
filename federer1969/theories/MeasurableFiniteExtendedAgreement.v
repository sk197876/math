(** Federer (1969), 3.1.4, p. 214: the set where two measurable
    extended-real functions are finite and equal is measurable. This is
    the domain description for approximate coordinate derivatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionPreimages
  MeasureUP MeasureFiniteClosure MeasurableFunctionUP MeasurableExtendedAgreement
  ExtendedRealOrderTopology CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_finite_extended_agreement]: the finite
    equality locus in the last sentence of the first proof paragraph
    of Federer 3.1.4, p. 214. The functions need not themselves be
    approximate order limits. *)
Lemma measurable_finite_extended_agreement (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F G : X -> extended_real_line R) :
  is_measure_measurable_function mu (partial_function_total F) ->
  is_measure_measurable_function mu (partial_function_total G) ->
  measure_measurable mu [set x | exists c : R, F x=c%:E /\ G x=c%:E].
Proof.
move=> hF hG.
have he : [set x | exists c : R, F x=c%:E /\ G x=c%:E]=
    partial_function_agreement (partial_function_total F) (partial_function_total G) `&`
    (F @^-1` [set y : extended_real_line R | -oo<y] `&`
     F @^-1` [set y : extended_real_line R | y < +oo]).
  apply/seteqP; split=> x.
  - move=> [c [hfc hgc]]; split.
    + by exists c%:E; split.
    + split; by rewrite /= hfc ?ltNyr ?ltry.
  - move=> [[v [hfv hgv]] [hlo hhi]].
    change (F x=v) in hfv; change (G x=v) in hgv.
    change (is_true (-oo<F x)) in hlo; change (is_true (F x < +oo)) in hhi.
    case hFx: (F x)=> [c| |].
    + exists c; split=> //; by rewrite hgv -hfv hFx.
    + by move: hhi; rewrite hFx ltxx.
    + by move: hlo; rewrite hFx ltxx.
rewrite he; apply: (@measure_measurable_intersection R X mu hm).
- exact: measurable_extended_agreement hm hF hG.
- apply: (@measure_measurable_intersection R X mu hm).
  + have hh := measurable_function_open_preimage hF
      (@order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] -oo).
    by rewrite partial_function_total_preimage in hh.
  + have hh := measurable_function_open_preimage hF
      (@order_strict_lower_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)] +oo).
    by rewrite partial_function_total_preimage in hh.
Qed.
