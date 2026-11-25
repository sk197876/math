(** Federer (1969), 2.5.7, p. 99: the bounded increasing scalar functional
    built from normalized covering-set integrals in case p=1. This
    supporting module treats the sequence of normalized integrals abstractly
    as numbers in [0,M]; later integral arguments must establish those
    bounds and the coordinatewise order properties. The sum itself uses the
    project's sealed nonnegative-summation interface. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumScale DyadicDensityWeights StrictNonnegativeSumComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_average_sum]: the weighted sum in Federer 2.5.7, p.
    99 Here a(n) will be the covering-set integral divided by its positive
    finite measure, and the weights have the book's one-based values. *)
Definition dyadic_average_sum (R : realType) (a : nat -> R) :=
  nonnegative_sum setT (fun n => (@density_dyadic_weight R n*a n)%:E).

(** Source for [dyadic_average_score]: real value of the bounded weighted
    sum used in Federer 2.5.7, p. 99 Exactness is proved below under the
    normalized-integral bounds. *)
Definition dyadic_average_score (R : realType) (a : nat -> R) := fine (dyadic_average_sum a).

(** Source for [dyadic_average_sum_bound]: the estimate r(u)<=M in Federer
    2.5.7, p. 99 This is its scalar summation step, including M=0. *)
Lemma dyadic_average_sum_bound (R : realType) (a : nat -> R) (M : R) :
  (0 <= M)%R -> (forall n, (0 <= a n <= M)%R) -> dyadic_average_sum a <= M%:E.
Proof.
move=> hM ha.
have hw n : (0 <= @density_dyadic_weight R n)%R := ltW (density_dyadic_weight_positive R n).
have hle : dyadic_average_sum a <= nonnegative_sum setT
    (fun n => M%:E*(@density_dyadic_weight R n)%:E).
  apply: nonnegative_sum_mono=> n _; rewrite -EFinM lee_fin [(M * _)%R]mulrC.
  apply: (ler_wpM2l (hw n)); exact: (andP (ha n)).2.
apply: le_trans hle _.
rewrite (@nonnegative_sum_scale R [the choiceType of (nat : Type)] setT
  (fun n => (@density_dyadic_weight R n)%:E) M hM (fun n _ => hw n)).
rewrite -{2}[M%:E]mule1.
apply: lee_wpmul2l; first by rewrite lee_fin.
exact: density_dyadic_weights_sum_bound.
Qed.

(** Source for [dyadic_average_score_exact]: finiteness of the scalar
    functional in Federer 2.5.7, p. 99 No infinity is projected to a
    spurious real value under these hypotheses. *)
Lemma dyadic_average_score_exact (R : realType) (a : nat -> R) (M : R) :
  (0 <= M)%R -> (forall n, (0 <= a n <= M)%R) ->
  (dyadic_average_score a)%:E=dyadic_average_sum a.
Proof.
move=> hM ha; rewrite /dyadic_average_score fineK //.
rewrite (ge0_fin_numE (nonnegative_sum_nonnegative _ _)).
exact: le_lt_trans (@dyadic_average_sum_bound R a M hM ha) (ltry M).
Qed.

(** Source for [dyadic_average_score_bounds]: the range [0,M] of r in
    Federer 2.5.7, p. 99 *)
Lemma dyadic_average_score_bounds (R : realType) (a : nat -> R) (M : R) :
  (0 <= M)%R -> (forall n, (0 <= a n <= M)%R) -> (0 <= dyadic_average_score a <= M)%R.
Proof.
move=> hM ha; apply/andP; split.
- apply: fine_ge0; exact: nonnegative_sum_nonnegative.
- have hh := @dyadic_average_sum_bound R a M hM ha.
  by rewrite -(@dyadic_average_score_exact R a M hM ha) lee_fin in hh.
Qed.

(** Source for [dyadic_average_score_monotone]: order preservation of the
    weighted functional in Federer 2.5.7, p. 99 *)
Lemma dyadic_average_score_monotone (R : realType) (a b : nat -> R) (M : R) :
  (0 <= M)%R -> (forall n, (0 <= a n <= M)%R) -> (forall n, (0 <= b n <= M)%R) ->
  (forall n, (a n <= b n)%R) -> (dyadic_average_score a <= dyadic_average_score b)%R.
Proof.
move=> hM ha hb hab.
have hh : dyadic_average_sum a <= dyadic_average_sum b.
  apply: nonnegative_sum_mono=> n _; rewrite lee_fin.
  apply: (ler_wpM2l (ltW (density_dyadic_weight_positive R n))); exact: hab n.
by rewrite -(@dyadic_average_score_exact R a M hM ha)
  -(@dyadic_average_score_exact R b M hM hb) lee_fin in hh.
Qed.

(** Source for [dyadic_average_score_strict]: strict increase of r in
    Federer 2.5.7, p. 99 A strict inequality in one integral coordinate
    suffices because every weight is positive and the smaller sum is finite. *)
Lemma dyadic_average_score_strict (R : realType) (a b : nat -> R) (M : R) j :
  (0 <= M)%R -> (forall n, (0 <= a n <= M)%R) -> (forall n, (0 <= b n <= M)%R) ->
  (forall n, (a n <= b n)%R) -> (a j < b j)%R ->
  (dyadic_average_score a < dyadic_average_score b)%R.
Proof.
move=> hM ha hb hab hj.
have hh : dyadic_average_sum a < dyadic_average_sum b.
  apply: (@strict_nonnegative_sum_comparison R [the choiceType of (nat : Type)] setT
    (fun n => (@density_dyadic_weight R n*a n)%:E) (fun n => (@density_dyadic_weight R n*b n)%:E) j I).
  - move=> n _; rewrite lee_fin; exact: mulr_ge0 (ltW (density_dyadic_weight_positive R n)) (andP (ha n)).1.
  - move=> n _; rewrite lee_fin; exact: mulr_ge0 (ltW (density_dyadic_weight_positive R n)) (andP (hb n)).1.
  - move=> n _; rewrite lee_fin; apply: (ler_wpM2l (ltW (density_dyadic_weight_positive R n))); exact: hab n.
  - by rewrite lte_fin (ltr_pM2l (density_dyadic_weight_positive R j)).
  - exact: le_lt_trans (@dyadic_average_sum_bound R a M hM ha) (ltry M).
by rewrite -(@dyadic_average_score_exact R a M hM ha)
  -(@dyadic_average_score_exact R b M hM hb) lte_fin in hh.
Qed.
