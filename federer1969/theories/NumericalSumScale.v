(** Federer (1969), 2.1.1(6), p. 52: multiplication of numerical sums by a
    nonzero real scalar. Source context: NumericalSum.v. Option equality
    asserts equality of domains as well as values. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealPartsScale
  ExtendedRealDifferenceScale NonnegativeSum NonnegativeSumSupport NonnegativeSumScale
  NumericalSum NumericalSumValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_negate]: Federer 2.1.1(6),
    p. 52, scalar minus one; negation exchanges the two variations. *)
Lemma numerical_sum_negate (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) :
  numerical_sum A (fun x => - f x) = omap -%E (numerical_sum A f).
Proof.
rewrite /numerical_sum.
have hn : nonnegative_sum A (fun x => extended_negative_part (-f x)) =
    nonnegative_sum A (fun x => extended_positive_part (f x)).
  apply: nonnegative_sum_ext=> x _; by rewrite /extended_negative_part oppeK.
rewrite hn; apply: nonnegative_difference_negate; exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [numerical_sum_positive_scale]: Federer
    2.1.1(6), p. 52, positive coefficient; both variations scale
    by the same coefficient. *)
Lemma numerical_sum_positive_scale (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (c : R) :
  (0 < c)%R -> numerical_sum A (fun x => c%:E * f x) =
    omap (fun x => c%:E * x) (numerical_sum A f).
Proof.
move=> hc; rewrite /numerical_sum.
have hp : nonnegative_sum A (fun x => extended_positive_part (c%:E * f x)) =
    c%:E * nonnegative_sum A (fun x => extended_positive_part (f x)).
  rewrite -nonnegative_sum_scale; last 2 first.
  - exact: ltW hc.
  - by move=> x _; exact: extended_positive_part_nonnegative.
  apply: nonnegative_sum_ext=> x _; exact: extended_positive_part_scale (ltW hc).
have hn : nonnegative_sum A (fun x => extended_negative_part (c%:E * f x)) =
    c%:E * nonnegative_sum A (fun x => extended_negative_part (f x)).
  rewrite -nonnegative_sum_scale; last 2 first.
  - exact: ltW hc.
  - by move=> x _; exact: extended_negative_part_nonnegative.
  apply: nonnegative_sum_ext=> x _; exact: extended_negative_part_scale (ltW hc).
rewrite hp hn; apply: nonnegative_difference_positive_scale=> //;
  exact: nonnegative_sum_nonnegative.
Qed.

(** Source for [numerical_sum_scale]: Federer 2.1.1(6), p. 52; every nonzero
    finite real coefficient factors out, including for undefined sums. *)
Theorem numerical_sum_scale (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (c : R) :
  c != 0%R -> numerical_sum A (fun x => c%:E * f x) =
    omap (fun x => c%:E * x) (numerical_sum A f).
Proof.
move=> hc0; have [hc|hc] := leP 0%R c.
- apply: numerical_sum_positive_scale; by rewrite lt_def hc0 hc.
- have hnc : (0 < -c)%R by rewrite oppr_gt0.
  have he : numerical_sum A (fun x => c%:E * f x) =
      numerical_sum A (fun x => - ((-c)%:E * f x)).
    apply: numerical_sum_ext=> x _; by rewrite EFinN mulNe oppeK.
  rewrite he numerical_sum_negate (@numerical_sum_positive_scale R I A f (-c)%R hnc).
  case: (numerical_sum A f)=> [z|] //=; by rewrite EFinN mulNe oppeK.
Qed.
