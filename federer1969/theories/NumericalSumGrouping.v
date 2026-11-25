(** Federer (1969), 2.1.1(9), p. 53: grouping a defined signed sum by
    fibres. Source context: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial NonnegativeSum NonnegativeSumSupport
  NonnegativeSumGrouping NumericalSum NumericalSumValues NumericalSumDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_grouping]: Federer 2.1.1(9),
    p. 53; every inner fibre sum is defined and the sum of their
    values equals the original defined sum. The existential inner
    function records these actual values, rather than assigning a
    default value to an undefined inner sum. *)
Theorem numerical_sum_grouping (R : realType) (I J : choiceType)
    (A : set I) (Y : set J) (h : I -> J) (f : I -> \bar R) z :
  (forall x, A x -> Y (h x)) -> numerical_sum A f = Some z ->
  exists g : J -> \bar R,
    (forall y, Y y -> numerical_sum (A `&` [set x | h x == y]) f = Some (g y)) /\
    numerical_sum Y g = Some z.
Proof.
move=> hh hz.
pose u y := nonnegative_sum (A `&` [set x | h x == y])
  (fun x => extended_positive_part (f x)).
pose v y := nonnegative_sum (A `&` [set x | h x == y])
  (fun x => extended_negative_part (f x)).
have hu : forall y, Y y -> 0 <= u y by move=> y _; exact: nonnegative_sum_nonnegative.
have hv : forall y, Y y -> 0 <= v y by move=> y _; exact: nonnegative_sum_nonnegative.
have hU : nonnegative_sum Y u = nonnegative_sum A (fun x => extended_positive_part (f x)).
  symmetry; apply: nonnegative_sum_grouping hh _=> x _; exact: extended_positive_part_nonnegative.
have hV : nonnegative_sum Y v = nonnegative_sum A (fun x => extended_negative_part (f x)).
  symmetry; apply: nonnegative_sum_grouping hh _=> x _; exact: extended_negative_part_nonnegative.
have ht : (nonnegative_sum Y u < +oo) || (nonnegative_sum Y v < +oo).
  rewrite hU hV; apply/numerical_sum_defined; by exists z.
have hd := nonnegative_sum_difference_domain hu hv ht.
exists (fun y => u y - v y); split.
- move=> y hy; change (extended_subtract (u y) (v y) = Some (u y-v y)).
  by rewrite /extended_subtract /extended_add (hd y hy).
- rewrite (numerical_sum_difference hu hv ht) hU hV; exact hz.
Qed.
