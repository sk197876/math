(** All compact convex section tubes, including empty
    fibres, in Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric InnerConvex
  CompactSetDistanceProfile CompactMetricBounded IntegralGeometricGauge IntegralGeometricGaugeEmpty
  ConvexIntrinsicFinitePart EuclideanLebesgueDimensions MeasureUP MeasureBasic VectorSetSum VectorSetSumLaws
  CompactConvexClosedTubePolynomial SteinerTubePolynomial SteinerAscendingScalarPolynomial EuclideanBallVolume.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_intrinsic_finite_part_value]: supporting
    scalar representation of every original section coefficient
    in Federer 3.2.45, p. 279. Nonempty compact
    convex sources use the already proved intrinsic-volume
    finiteness; the empty source uses its proved zero
    gauge. Every natural degree, including zero, remains. *)
Lemma compact_convex_intrinsic_finite_part_value (R : realType) n k (hKN : (k<=n)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R n))) :
  compact S -> is_inner_convex S ->
  @integral_geometric_gauge R n k hKN 1 S=
    (fine (@integral_geometric_gauge R n k hKN 1 S))%:E.
Proof.
move=> hCompact hConvex; case: (pselect (S !=set0))=> [hNonempty|hEmpty].
- pose C : compact_metric_set (inner_metric_space (@euclidean_inner_productP R n)) :=
    exist _ S (mem_set (conj hCompact hNonempty)).
  exact: convex_intrinsic_finite_part_value hNonempty hConvex (compact_metric_diameter_finite C).
- have hS : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  by rewrite hS (@integral_geometric_gauge_empty R n k hKN 1 (lexx 1)) fine0.
Qed.

(** Source for [compact_convex_ball_sum_padded_polynomial]: supporting
    pointwise section polynomial in Federer 3.2.45,
    p. 279. The actual compact convex section plus
    its closed ball has the complete original Steiner
    volume, padded by zero above the section dimension.
    Empty sections have zero volume and every original
    coefficient zero. Nonempty sections use the proved
    nearest-point closed-tube identity. No source interior,
    positive volume or nonempty-fibre premise is added. *)
Theorem compact_convex_ball_sum_padded_polynomial (R : realType) q N (hQN : (q<=N)%N)
    (S : set (inner_metric_space (@euclidean_inner_productP R q))) (r : R) :
  compact S -> is_inner_convex S -> 0<r ->
  @euclidean_lebesgue_measure R q (vector_set_sum S
    [set z | inner_norm (@euclidean_inner_productP R q) z<=r])=
  (\sum_(i : 'I_N.+1)
    (if (i<=q)%N then fine (@integral_geometric_gauge R q (q-i) (leq_subr i q) 1 S)*
      euclidean_unit_ball_volume R i else 0)*r^+i)%:E.
Proof.
move=> hCompact hConvex hr; case: (pselect (S !=set0))=> [hNonempty|hEmpty].
- pose C : compact_metric_set (inner_metric_space (@euclidean_inner_productP R q)) :=
    exist _ S (mem_set (conj hCompact hNonempty)).
  have hClosed : closed S := compact_closed (@metric_hausdorff R _) hCompact.
  rewrite -(@euclidean_closed_ball_vector_sum_tube R q S (compact_set_distance_profile C) r
    hClosed hNonempty (compact_set_distance_profile_specification C)).
  rewrite (@compact_convex_closed_tube_polynomial R q C r hConvex hr).
  exact: (@steiner_tube_polynomial_padded_scalar_value R q N hQN S r hNonempty hConvex
    (compact_metric_diameter_finite C)).
- have hS : S=set0.
    apply/seteqP; split=> x hx; last by [].
    exfalso; apply: hEmpty; by exists x.
  rewrite hS vector_set_sum_empty_left (measure_empty (euclidean_lebesgue_is_measure R q)).
  have hSum : (\sum_(i : 'I_N.+1)
      (if (i<=q)%N then fine (@integral_geometric_gauge R q (q-i) (leq_subr i q) 1 set0)*
        euclidean_unit_ball_volume R i else 0)*r^+i)=0.
    apply: big1=> i _; case: (i<=q)%N; last exact: mul0r.
    by rewrite (@integral_geometric_gauge_empty R q (q-i) (leq_subr i q) 1 (lexx 1)) fine0 !mul0r.
  by rewrite hSum.
Qed.
