(** Replacing a cellwise function by its equal graph on a covering relation,
    supporting Federer (1969), 2.9.8, p. 156. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP CoveringRelationLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [covering_value_range_graph_equivalent]:
    supporting substitution into the upper and lower
    limit formulas for Federer 2.9.8, p. 156.
    Equality is required only on related cells. *)
Lemma covering_value_range_graph_equivalent (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f g : partial_function (set X) (\bar R)) :
  (forall x S, V x S -> forall y, partial_function_graph f S y <-> partial_function_graph g S y) ->
  forall x e, covering_value_range V f x e=covering_value_range V g x e.
Proof.
move=> he x e; apply/seteqP; split=> [y [S [hS [hd hy]]]|y [S [hS [hd hy]]]];
  exists S; split=> //; split=> //; [exact: (he x S hS y).1 hy|exact: (he x S hS y).2 hy].
Qed.

(** Source for [covering_limits_graph_equivalent]: supporting
    substitution of the integral mean in Federer 2.9.8,
    p. 156, into the monotone epsilon infimum
    and supremum definitions of 2.8.16, p. 151. *)
Lemma covering_limits_graph_equivalent (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f g : partial_function (set X) (\bar R)) :
  (forall x S, V x S -> forall y, partial_function_graph f S y <-> partial_function_graph g S y) ->
  forall x, covering_upper_limit V f x=covering_upper_limit V g x /\
    covering_lower_limit V f x=covering_lower_limit V g x.
Proof.
move=> he x.
have hv e := @covering_value_range_graph_equivalent R X V f g he x e.
split; rewrite /covering_upper_limit /covering_lower_limit.
- congr (_ _); apply/seteqP; split=> [b [e [he' ->]]|b [e [he' ->]]]; exists e; split=> //; by rewrite hv.
- congr (_ _); apply/seteqP; split=> [b [e [he' ->]]|b [e [he' ->]]]; exists e; split=> //; by rewrite hv.
Qed.

(** Source for [covering_limit_graph_equivalent]: supporting
    transfer of the actual partial limit in Federer
    2.9.8, p. 156. Fineness of the
    base relation and both limit values are preserved. *)
Lemma covering_limit_graph_equivalent (R : realType) (X : metricType R)
    (V : X -> set X -> Prop) (f g : partial_function (set X) (\bar R)) :
  (forall x S, V x S -> forall y, partial_function_graph f S y <-> partial_function_graph g S y) ->
  forall x y, partial_function_graph (covering_relation_limit V f) x y <->
    partial_function_graph (covering_relation_limit V g) x y.
Proof.
move=> he x y; have [hu hl] := @covering_limits_graph_equivalent R X V f g he x.
by rewrite /covering_relation_limit /= hu hl.
Qed.
