(** Supporting degenerate-cover consequences for Federer (1969), 2.10.2, p.
    171: singleton and countable sets have zero positive-integer-dimensional
    Hausdorff and spherical measure. Derive these facts from the proved
    counting, dimension-drop and spherical comparison laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure HausdorffDimensionDrop
  HausdorffSphericalComparison MeasureUP MeasureIndexedCover NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_positive_degree_singleton_zero]: supporting
    singleton boundary of the dimension-drop assertion in Federer 2.10.2(1),
    p. 171 *)
Lemma hausdorff_positive_degree_singleton_zero (R : realType) (X : metricType R)
    (m : nat) (x : X) : (0<m)%N -> @hausdorff_measure R X m [set x]=0.
Proof.
move=> hm; apply: (@hausdorff_finite_mass_higher_degree_zero R X 0 m [set x] hm).
by rewrite hausdorff_zero_singleton ltry.
Qed.

(** Source for [spherical_positive_degree_singleton_zero]: supporting
    zero-diameter boundary for the spherical comparison of Federer
    2.10.2(2), p. 171 Strictly positive radii suffice even though the
    singleton has diameter zero. *)
Lemma spherical_positive_degree_singleton_zero (R : realType) (X : metricType R)
    (m : nat) (x : X) : (0<m)%N -> @spherical_measure R X m [set x]=0.
Proof.
move=> hm; have hh := @spherical_measure_le_double_hausdorff_measure R X m [set x].
rewrite (hausdorff_positive_degree_singleton_zero x hm) mule0 in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (@spherical_measure_is_measure R X m)).
Qed.

(** Source for [hausdorff_positive_degree_countable_zero]:
    supporting countable-target boundary of Federer 2.10.2(1),
    p. 171, by the singleton calculation and the countable
    covering inequality of 2.1.2, p. 53. *)
Theorem hausdorff_positive_degree_countable_zero (R : realType) (X : metricType R)
    (m : nat) (A : set X) : (0<m)%N -> countable A -> @hausdorff_measure R X m A=0.
Proof.
move=> hm hA; have hmu := @hausdorff_measure_is_measure R X m.
have hcov : A `<=` \bigcup_(x in A) [set x] by move=> x hx; exists x.
have hb := measure_indexed_cover hmu hA hcov.
rewrite (nonnegative_sum_zero (fun x _ => @hausdorff_positive_degree_singleton_zero R X m x hm)) in hb.
by apply/eqP; rewrite eq_le hb (measure_nonnegative hmu).
Qed.

(** Source for [spherical_positive_degree_countable_zero]: supporting
    countable-target corollary for Federer 2.10.2(2), p. 171, from its
    spherical comparison *)
Theorem spherical_positive_degree_countable_zero (R : realType) (X : metricType R)
    (m : nat) (A : set X) : (0<m)%N -> countable A -> @spherical_measure R X m A=0.
Proof.
move=> hm hA; have hh := @spherical_measure_le_double_hausdorff_measure R X m A.
rewrite (@hausdorff_positive_degree_countable_zero R X m A hm hA) mule0 in hh.
by apply/eqP; rewrite eq_le hh (measure_nonnegative (@spherical_measure_is_measure R X m)).
Qed.
