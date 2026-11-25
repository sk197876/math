(** Supporting proof for Federer (1969), 2.10.2(1), p. 171: zero-dimensional
    Hausdorff measure equals counting measure. A measure with measurable
    unit atoms is counting measure, by disjoint finite subsums and the
    singleton covering inequality of 2.1.2, pp. 53–54. This intermediate
    criterion is not separately stated in 2.10.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureIndexedCover MeasureDisjointSupport
  NonnegativeSum NonnegativeSumSupport CountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_unit_atoms_counting_measure]:
    supporting criterion for Federer 2.10.2(1), p. 171;
    prove both inequalities from the existing measure and
    numerical-sum laws, including infinite and uncountable sets. *)
Theorem measurable_unit_atoms_counting_measure (R : realType) (X : choiceType)
    (mu : set X -> \bar R) : is_measure mu ->
  (forall x, measure_measurable mu [set x]) ->
  (forall x, mu [set x] = 1) -> forall A, mu A=@counting_measure R X A.
Proof.
move=> hm hme hunit A.
have hsum : nonnegative_sum A (fun x => mu [set x])=counting_measure (R:=R) A.
  rewrite counting_measure_sum; apply: nonnegative_sum_ext=> x _; exact: hunit.
apply/eqP; rewrite eq_le; apply/andP; split.
- case: (pselect (finite_set A))=> hA; last by rewrite (@counting_measure_infinite R X A hA); exact: leey.
  rewrite -hsum; apply: (measure_indexed_cover hm (finite_set_countable hA)).
  by move=> x hx; exists x.
- rewrite -hsum; apply: (measure_disjoint_sum_bound hm).
  + by move=> x hx y ->.
  + by move=> x _; exact: hme.
  + move=> x y hx hy hxy; apply/seteqP; split=> // z [-> he].
    by exfalso; apply: hxy; exact he.
Qed.
