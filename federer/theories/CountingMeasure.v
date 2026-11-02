(** Federer (1969), 2.1.2, pp. 53-54. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSumUP NonnegativeSumSealed NonnegativeSumSupport NonnegativeSum NonnegativeSumConstant NonnegativeSumRestriction NonnegativeSumCover CountingMeasureUP CountingMeasureSealed MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [counting_measure]: Federer 2.1.2, p. 54;
    public counting measure, accessed through the sealed specification. *)
Definition counting_measure (R : realType) (I : choiceType) :
    set I -> \bar R := @CountingMeasure.value R I.
Arguments counting_measure {R I} _.

(** Source for [counting_measure_laws]: Federer 2.1.2,
    p. 54; abstract cardinality characterization of the public measure. *)
Lemma counting_measure_laws (R : realType) (I : choiceType) :
  is_counting_measure (@counting_measure R I).
Proof. exact: CountingMeasure.laws. Qed.

(** Source for [counting_measure_sum]: Federer 2.1.2,
    p. 54; supporting expression as a sum of unit masses, proved
    from the abstract law rather than by unfolding a construction. *)
Lemma counting_measure_sum (R : realType) (I : choiceType) (A : set I) :
  counting_measure (R := R) A = nonnegative_sum A (fun _ => (1 : R)%:E).
Proof.
exact: (@nonnegative_sum_unique R I A (fun _ => (1 : R)%:E) _ _
  (@counting_measure_laws R I A) (NonnegativeSum.laws A _)).
Qed.

(** Source for [counting_measure_finite]: Federer 2.1.2,
    p. 54, counting measure of a finite set is its number of elements. *)
Lemma counting_measure_finite (R : realType) (I : choiceType) (B : {fset I}) :
  counting_measure (R := R) [set` B] = (#|` B|%:R : R)%:E.
Proof.
rewrite counting_measure_sum nonnegative_sum_finite; last by move=> x _; rewrite lee_fin ler01.
by rewrite sumEFin big_seq_fsetE sumr_const cardT cardfE -mulr_natl mulr1 cardE.
Qed.

(** Source for [counting_measure_infinite]: Federer 2.1.2,
    p. 54, counting measure of an infinite set is infinity. *)
Lemma counting_measure_infinite (R : realType) (I : choiceType) (A : set I) :
  infinite_set A -> counting_measure (R := R) A = +oo.
Proof. by move=> hA; rewrite counting_measure_sum nonnegative_sum_infinite_constant // ltr01. Qed.

(** Source for [counting_measure_is_measure]: Federer 2.1.2,
    p. 54, counting measure is a measure over the ambient set. *)
Lemma counting_measure_is_measure (R : realType) (I : choiceType) :
  is_measure (@counting_measure R I).
Proof.
constructor; first by move=> A; rewrite counting_measure_sum nonnegative_sum_nonnegative.
move=> A F _ hc; rewrite counting_measure_sum.
have he : nonnegative_sum F (@counting_measure R I) =
    nonnegative_sum F (fun B => nonnegative_sum B (fun _ => (1 : R)%:E)).
  by apply: nonnegative_sum_ext=> B _; rewrite counting_measure_sum.
rewrite he; apply: nonnegative_sum_cover hc=> x; by rewrite lee_fin ler01.
Qed.

(** Source for [counting_measure_measurable]: Federer 2.1.2,
    p. 54, all subsets are measurable for counting measure. *)
Lemma counting_measure_measurable (R : realType) (I : choiceType) (A : set I) :
  measure_measurable (@counting_measure R I) A.
Proof.
move=> T; rewrite !counting_measure_sum.
apply: nonnegative_sum_split=> x _; by rewrite lee_fin ler01.
Qed.
