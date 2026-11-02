(** Federer (1969), 2.1.1(7), p. 53: additivity under the definedness of the
    sum of the totals. editions: NumericalSum.v. The proof combines
    nonnegative variations and cancels their difference. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealAddVariations
  NonnegativeSum NonnegativeSumSupport NonnegativeSumAdd NumericalSum
  NumericalSumValues NumericalSumDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_add]: Federer 2.1.1(7), p. 53; if both sums
    and their sum are defined, the pointwise addition is defined on A and
    its numerical sum is the sum of the totals. *)
Theorem numerical_sum_add (R : realType) (I : choiceType)
    (A : set I) (f g : I -> \bar R) a b c :
  numerical_sum A f = Some a -> numerical_sum A g = Some b ->
  extended_add a b = Some c ->
  (forall x, A x -> adde_def (f x) (g x)) /\
  numerical_sum A (fun x => f x+g x) = Some c.
Proof.
move=> ha hb hc.
have hd : adde_def a b by apply/(proj1 (extended_add_defined a b)); exists c.
have hcval : a+b = c.
  move: hc; rewrite /extended_add hd; by move=> [].
pose u x := extended_positive_part (f x) + extended_positive_part (g x).
pose v x := extended_negative_part (f x) + extended_negative_part (g x).
have hu : forall x, A x -> 0 <= u x.
  move=> x _; apply: adde_ge0; exact: extended_positive_part_nonnegative.
have hv : forall x, A x -> 0 <= v x.
  move=> x _; apply: adde_ge0; exact: extended_negative_part_nonnegative.
have hU : nonnegative_sum A u =
    nonnegative_sum A (fun x => extended_positive_part (f x)) +
    nonnegative_sum A (fun x => extended_positive_part (g x)).
  apply: nonnegative_sum_add; by move=> x _; exact: extended_positive_part_nonnegative.
have hV : nonnegative_sum A v =
    nonnegative_sum A (fun x => extended_negative_part (f x)) +
    nonnegative_sum A (fun x => extended_negative_part (g x)).
  apply: nonnegative_sum_add; by move=> x _; exact: extended_negative_part_nonnegative.
have ht : (nonnegative_sum A u < +oo) || (nonnegative_sum A v < +oo).
  rewrite hU hV; apply: (@nonnegative_differences_add_domain R _ _ _ _ a b);
    try exact: nonnegative_sum_nonnegative; assumption.
have hpoint := nonnegative_sum_difference_domain hu hv ht.
split.
- move=> x hx; apply: extended_add_parts_domain; exact: hpoint.
- have he : numerical_sum A (fun x => f x+g x) = numerical_sum A (fun x => u x-v x).
    apply: numerical_sum_ext=> x _; symmetry; exact: extended_add_parts_difference.
  rewrite he (numerical_sum_difference hu hv ht).
  rewrite nonnegative_difference_value ?nonnegative_sum_nonnegative // hU hV.
  rewrite nonnegative_differences_add_identity ?nonnegative_sum_nonnegative //.
  by rewrite (numerical_sum_value ha) (numerical_sum_value hb) hcval.
Qed.
