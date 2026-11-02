(** Local correction to Federer (1969), 2.6.5, p. 119: the unrestricted
    associativity assertion is false. This file verifies that elementary
    measure. The local Federer erratum has no associativity correction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [infinite_discrete_measure]: Supporting Federer 2.6.5, p.
    119. *)
Definition infinite_discrete_measure (R : realType) (X : Type) (A : set X) : \bar R :=
  if `[< exists x, A x >] then +oo else 0.

(** Source for [infinite_discrete_measure_empty]: local correction to
    Federer 2.6.5, p. 119. *)
Lemma infinite_discrete_measure_empty (R : realType) (X : Type) :
  @infinite_discrete_measure R X set0 = 0.
Proof. by rewrite /infinite_discrete_measure asboolF //; move=> [x []]. Qed.

(** Source for [infinite_discrete_measure_nonempty]: local correction to
    Federer 2.6.5, p. 119. *)
Lemma infinite_discrete_measure_nonempty (R : realType) (X : Type) (A : set X) :
  (exists x, A x) -> infinite_discrete_measure R A = +oo.
Proof. by move=> h; rewrite /infinite_discrete_measure asboolT. Qed.

(** Source for [infinite_discrete_measure_is_measure]: This uses the measure
    definition in Federer 2.1.2, p. 53, for the local correction to 2.6.5,
    p. 119. *)
Lemma infinite_discrete_measure_is_measure (R : realType) (X : choiceType) :
  is_measure (@infinite_discrete_measure R X).
Proof.
constructor.
- by move=> A; rewrite /infinite_discrete_measure; case: ifP=> _; rewrite ?leey ?lexx.
- move=> A F hF hc.
  case: (pselect (exists x, A x))=> [[x hx]|hA].
  + have [B hB hxB] := hc x hx.
    have ha : infinite_discrete_measure R A = +oo.
      apply: infinite_discrete_measure_nonempty; by exists x.
    have hb : infinite_discrete_measure R B = +oo.
      apply: infinite_discrete_measure_nonempty; by exists x.
    rewrite ha -hb; exact: nonnegative_sum_term hB.
  + rewrite /infinite_discrete_measure asboolF //.
    exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [infinite_discrete_measure_measurable]: supporting
    measurability of every set for gamma; the only finite test set is empty.
    This supports the local correction to Federer 2.6.5, p. 119. *)
Lemma infinite_discrete_measure_measurable (R : realType) (X : choiceType) (A : set X) :
  measure_measurable (@infinite_discrete_measure R X) A.
Proof.
apply/(measure_measurable_finite_test (infinite_discrete_measure_is_measure R X)).
move=> T; rewrite /infinite_discrete_measure.
case: ifP=> [/asboolP hT|/asboolP hT]; first by rewrite ltxx.
move=> _; have ht : T = set0.
  apply/seteqP; split=> x; last by [].
  move=> hx; exfalso; apply: hT; by exists x.
by rewrite ht set0I set0D !asboolF ?add0e //; move=> [x []].
Qed.
