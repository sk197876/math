(** Federer (1969), 4.1.7, p. 358: local
    uniqueness and positivity become ordinary almost
    everywhere statements on the original countably
    finite domain. This supporting implication uses
    2.1.3, p. 55, and 2.3.4, p. 76. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureAlmostUP MeasureAlmostBasic
  CountablyMeasurableUP LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countably_finite_locally_null_is_null]:
    local exceptional-set nullity implies global
    nullity when the domain is countably measurable,
    supporting Federer 4.1.7, p. 358, by
    2.3.4, p. 76. This does not assert
    the implication on arbitrary Radon spaces. *)
Lemma countably_finite_locally_null_is_null (R:realType) (X:choiceType)
    (mu:set X->\bar R) (hm:is_measure mu) (N:set X):
  measure_countably_measurable mu setT ->measure_locally_null mu N ->mu N=0.
Proof.
move=>[D [hD [hCover hFinite]]] hLocal.
have hUnion:mu (\bigcup_(C in D) (C `&` N))=0.
  apply:(@measure_null_countable_union R X [the choiceType of set X] mu hm D
    (fun C=>C `&` N) hD)=>C hC.
  exact:hLocal C (hFinite C hC).2.
apply:(@measure_null_subset R X mu hm _ _ _ hUnion)=>x hx.
have hAll:(\bigcup_(C in D) C) x by rewrite -hCover.
have [C hC hCx]:=hAll; exists C=>//; by split.
Qed.
