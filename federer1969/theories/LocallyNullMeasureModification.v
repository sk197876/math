(** Federer (1969), 2.5.14, p. 108: supporting measurability under changes
    on locally null sets in the vector-density argument. Caratheodory's
    finite-test criterion, 2.1.2, p. 54, suffices. This is a local variant
    of the null-modification observation in 2.3.2, p. 73, not an assertion
    that locally null sets have zero total measure. Source context:
    LocallyNullMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureSplit MeasureNullModification
  MeasureAlmostBasic PartialFunctionBasic PartialFunctionPreimages MeasurableFunctionUP
  LocallyNullMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_set_locally_null_modification]:
    supporting local measurable modification for Federer 2.5.14,
    p. 108, derived directly from the finite-test criterion
    of 2.1.2, p. 54. *)
Lemma measurable_set_locally_null_modification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B N : set X) :
  measure_locally_null mu N -> (forall x, ~ N x -> (A x <-> B x)) ->
  measure_measurable mu A -> measure_measurable mu B.
Proof.
move=> hN he hA; apply/(measure_measurable_finite_test hm)=> T hT.
have hn := hN T hT.
have hI : mu (T `&` B)=mu (T `&` A).
  apply: (@measure_null_modification_value R X mu hm _ _ _ hn)=> x hx.
  split=> [[ht hb]|[ht ha]]; split=> //.
  - apply: (proj2 (he x _)); last exact hb.
    by move=> hn'; apply: hx; split.
  - apply: (proj1 (he x _)); last exact ha.
    by move=> hn'; apply: hx; split.
have hD : mu (T `\` B)=mu (T `\` A).
  apply: (@measure_null_modification_value R X mu hm _ _ _ hn)=> x hx.
  split=> [[ht hb]|[ht ha]]; split=> //.
  - move=> ha; apply: hb; apply: (proj1 (he x _)); last exact ha.
    by move=> hn'; apply: hx; split.
  - move=> hb; apply: ha; apply: (proj2 (he x _)); last exact hb.
    by move=> hn'; apply: hx; split.
by rewrite hI hD -(hA T).
Qed.

(** Source for [measurable_total_locally_null_modification]:
    weak-density modifications in Federer 2.5.14, p. 108,
    may be checked locally. This supporting result is valid for
    any topological target and any total measurable map. *)
Theorem measurable_total_locally_null_modification (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : X -> Y) (N : set X) :
  measure_locally_null mu N -> (forall x, ~ N x -> f x=g x) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g).
Proof.
move=> hN he hf; constructor.
- rewrite partial_function_total_domain; exact: measure_almost_everywhere_true hm.
- move=> U hU; rewrite partial_function_total_preimage.
  have hmU := measurable_function_open_preimage hf hU.
  rewrite partial_function_total_preimage in hmU.
  apply: (@measurable_set_locally_null_modification R X mu hm _ _ N hN _ hmU).
  move=> x hx; change (U (f x) <-> U (g x)).
  by rewrite (he x hx).
Qed.
