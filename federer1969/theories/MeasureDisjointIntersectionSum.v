(** The two countable sums at the end of Federer (1969), 2.9.2, p. 153.
    Restriction permits arbitrary test sets S, which need not be measurable.
    Source context: MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import MeasureUP MeasureRestriction MeasureCountableAdditivity
  NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_disjoint_union_intersection_sum]: supporting
    restriction-and-additivity identity for Federer 2.9.2, p. 153 The
    measurable disjoint cells may have infinite measure and the test set is
    arbitrary. *)
Lemma measure_disjoint_union_intersection_sum (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (F : nat -> set X) :
  is_measure mu -> (forall n, measure_measurable mu (F n)) ->
  (forall n m, n != m -> forall x, F n x -> F m x -> False) ->
  forall S, mu ((\bigcup_n F n) `&` S)=nonnegative_sum setT (fun n => mu (F n `&` S)).
Proof.
move=> hm hF hd S.
have h := @measure_sequence_disjoint_additivity R X (measure_restrict mu S)
  (measure_restrict_is_measure hm S) F
  (fun n => @measure_restrict_measurable R X mu S (F n) (hF n)) hd.
rewrite /measure_restrict (setIC S (\bigcup_n F n)) in h.
rewrite h; apply: nonnegative_sum_ext=> n _; by rewrite setIC.
Qed.
