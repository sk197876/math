(** Counting comparisons supporting the multiplicity argument of Federer
    (1969), 2.10.10, p. 176, used by the geometric example in 2.5.10, p.
    101. The numerical-sum tools are 2.1.1(3),(9), pp. 52–53. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumGrouping
  CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measure_singleton_value]: the
    unit mass of a point, Federer 2.1.2, p. 54,
    supporting the finite and infinite multiplicities in
    2.10.10, p. 176. *)
Lemma counting_measure_singleton_value (R : realType) (X : choiceType) (x : X) :
  counting_measure (R:=R) [set x]= 1.
Proof. by rewrite counting_measure_sum nonnegative_sum_singleton // lee_fin ler01. Qed.

(** Source for [counting_measure_injection_bound]: an
    injection cannot increase the number of source points,
    supporting the counting limit in Federer 2.10.10,
    p. 176. Infinite counts are included by the
    finite-subsum and grouping laws of 2.1.1(3),(9),
    pp. 52–53. *)
Lemma counting_measure_injection_bound (R : realType) (X Y : choiceType)
    (A : set X) (B : set Y) (f : X -> Y) :
  (forall x, A x -> B (f x)) ->
  (forall x y, A x -> A y -> f x=f y -> x=y) ->
  counting_measure (R:=R) A<=counting_measure (R:=R) B.
Proof.
move=> hf hinj; rewrite !counting_measure_sum.
rewrite (@nonnegative_sum_grouping R X Y A B f (fun _ => 1)); last 2 first.
- exact hf.
- by move=> x hx; rewrite lee_fin ler01.
apply: nonnegative_sum_mono=> y hy.
case: (pselect ((A `&` [set x | f x==y]) !=set0))=> [[x [hx /eqP hfx]]|hn].
- have he : A `&` [set z | f z==y]=[set x].
    apply/seteqP; split=> z.
    + move=> [hz /eqP hfz]; exact: hinj hz hx (eq_trans hfz (esym hfx)).
    + move=> ->; split=> //; exact/eqP.
  by rewrite he nonnegative_sum_singleton // lee_fin ler01.
- have he : A `&` [set x | f x==y]=set0.
    apply/seteqP; split=> z hz; last by [].
    exfalso; apply: hn; by exists z.
  by rewrite he nonnegative_sum_empty lee_fin ler01.
Qed.
