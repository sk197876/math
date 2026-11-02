(** Federer (1969), 2.1.3(3),(4),(2), pp. 55-56: finite unions, disjoint
    increments and their sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumNatPrefix
  MeasureUP MeasureBasic MeasureSplit MeasureFiniteClosure
  MeasureFiniteAdditivity SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_sequence_prefix_measurable]: Federer
    2.1.3(2), pp. 55-56; finite unions of measurable sets are measurable. *)
Lemma measure_sequence_prefix_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  forall n, measure_measurable mu (set_sequence_prefix F n).
Proof.
move=> hF; elim=> [|n IH].
- rewrite set_sequence_prefix_zero; exact: measure_measurable_empty hm.
- rewrite set_sequence_prefix_succ; exact: (@measure_measurable_union R I mu hm _ _ IH (hF n)).
Qed.

(** Source for [measure_sequence_disjointify_measurable]: Federer
    2.1.3(4), proof p. 55; the disjoint increments are measurable,
    by the complement and finite-intersection assertions. *)
Lemma measure_sequence_disjointify_measurable (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) ->
  forall n, measure_measurable mu (set_sequence_disjointify F n).
Proof.
move=> hF n; apply: (@measure_measurable_difference R I mu hm _ _ (hF n)).
exact: (@measure_sequence_prefix_measurable R I mu hm F hF n).
Qed.

(** Source for [measure_sequence_disjointify_prefix_sum]: Federer
    2.1.3(3),(4), proof p. 55; a finite union's measure equals the
    sum of the measures of its disjoint increments. *)
Lemma measure_sequence_disjointify_prefix_sum (R : realType) (I : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (F : nat -> set I) :
  (forall n, measure_measurable mu (F n)) -> forall n,
  mu (set_sequence_prefix F n) =
    nonnegative_sum [set k | (k < n)%N] (fun k => mu (set_sequence_disjointify F k)).
Proof.
move=> hF; elim=> [|n IH].
- by rewrite set_sequence_prefix_zero nonnegative_sum_nat_prefix_zero (measure_empty hm).
- rewrite nonnegative_sum_nat_prefix_succ; last by move=> k; exact: (@measure_nonnegative R I mu hm).
  rewrite -IH -set_sequence_disjointify_prefix set_sequence_prefix_succ setUC.
  have hd : forall x, set_sequence_disjointify F n x ->
      set_sequence_prefix (set_sequence_disjointify F) n x -> False.
    move=> x hn [k hk hxk].
    have hne : n != k by rewrite neq_ltn; apply/orP; right.
    exact: (@set_sequence_disjointify_disjoint I F n k hne x hn hxk).
  rewrite (@measure_disjoint_union R I mu _ _
    ((@measure_sequence_disjointify_measurable R I mu hm F hF n)) hd).
  by rewrite set_sequence_disjointify_prefix addeC.
Qed.
