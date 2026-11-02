(** Federer (1969), 2.10.47, p. 204: the degree-zero case of the compact
    finite-positive subset theorem. H^0 counts points by 2.10.2(1), p. 171,
    so a singleton suffices in any metric space, even without compactness of
    the original set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import HausdorffMeasure HausdorffCountingMeasure MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_zero_positive_compact_subset]: the
    m=0 case of 2.10.47, p. 204. The proof gives
    mass exactly one and does not need an ambient Euclidean
    hypothesis or compactness of A. This strengthening is
    a boundary case, not the positive-degree construction. *)
Theorem hausdorff_zero_positive_compact_subset (R : realType) (X : metricType R) (A : set X) :
  0<@hausdorff_measure R X 0 A ->
  exists B, [/\ compact B, B `<=` A & @hausdorff_measure R X 0 B = 1].
Proof.
move=> hpos.
have hne : A!=set0.
  apply: contrapT=> hn.
  have he : A=set0 by apply/seteqP; split=> [x hx|x []]; apply: hn; by exists x.
  by rewrite he (measure_empty (@hausdorff_measure_is_measure R X 0)) ltxx in hpos.
have [x hx] := hne; exists [set x]; split.
- exact: compact_set1.
- by move=> y ->.
- exact: hausdorff_zero_singleton.
Qed.
