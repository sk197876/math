(** Image counting for the partition-refinement argument of Federer (1969),
    2.10.10, p. 176, used for 2.5.10, p. 101. The supporting numerical sum
    grouping is 2.1.1(9), p. 53 *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSumImageBound CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measure_image_bound]: grouping
    points by their image cannot increase the count,
    supporting the monotonicity of partition counts in
    Federer 2.10.10, p. 176. Repeated images
    and infinite sets are included. *)
Lemma counting_measure_image_bound (R : realType) (X Y : choiceType)
    (A : set X) (f : X -> Y) :
  counting_measure (R:=R) (f @` A)<=counting_measure (R:=R) A.
Proof.
rewrite !counting_measure_sum.
apply: nonnegative_sum_image_bound=> x hx; by rewrite lee_fin ler01.
Qed.
