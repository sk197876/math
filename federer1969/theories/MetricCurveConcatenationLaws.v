(** Federer (1969), 3.2.46, p. 281: actual curve
    values on each part of a concatenation, supporting its
    admissibility and integral additivity. *)
From mathcomp Require Import all_boot all_order all_algebra reals lra ring
  classical_sets.
From Federer Require Import MetricCurveConcatenation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [metric_curve_concatenation_left]: the
    original first curve is retained up to its final parameter,
    supporting Federer 3.2.46, p. 281. *)
Lemma metric_curve_concatenation_left (R : realType) (Y : Type)
    (C D : R -> Y) b c t : t <= b ->
  metric_curve_concatenation C D b c t = C t.
Proof. by move=> ht; rewrite /metric_curve_concatenation ht. Qed.

(** Source for [metric_curve_concatenation_right]: the
    translated second curve is retained from the junction,
    including the junction itself, supporting the actual
    integral splitting in Federer 3.2.46, p. 281. *)
Lemma metric_curve_concatenation_right (R : realType) (Y : Type)
    (C D : R -> Y) b c t : C b = D c -> b <= t ->
  metric_curve_concatenation C D b c t = D (t-b+c).
Proof.
move=> hJoin hbt; rewrite /metric_curve_concatenation.
case: ifP=> ht; last reflexivity.
have he : t = b by apply/eqP; rewrite eq_le ht hbt.
by rewrite he subrr add0r hJoin.
Qed.

(** Source for [metric_curve_concatenation_image]: the
    joined curve stays in the original domain A if both
    representatives do, supporting Federer 3.2.46, p. 281. *)
Lemma metric_curve_concatenation_image (R : realType) (Y : Type)
    (C D : R -> Y) (A : Y -> Prop) b c :
  (forall t, A (C t)) -> (forall t, A (D t)) ->
  forall t, A (metric_curve_concatenation C D b c t).
Proof.
move=> hC hD t; rewrite /metric_curve_concatenation; case: ifP=> ht;
  [exact: hC | exact: hD].
Qed.
