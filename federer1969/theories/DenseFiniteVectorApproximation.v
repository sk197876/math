(** Federer (1969), 2.5.12, printed p. 105: approximation of a measurable w
    by finitely many values in the countable dense rational subspace D. The
    proof here uses the existing abstract nearest-prefix partitions from
    2.4.12. Including zero gives a pointwise error majorant nu(w), allowing
    the finite-measure localisation in the printed proof to be replaced
    later by dominated convergence. No completeness of E is needed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  MeasureUP MeasurableFunctionUP MeasurableTotalBasic PointwiseLimit
  FiniteNearestApproximationUP FiniteNearestApproximationSealed
  FiniteNearestApproximation VectorDaniellHypotheses VectorDaniellRationalSpan
  VectorDaniellDualExtension VectorDaniellWeakMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_finite_vector_approximation]: supporting
    approximation by values in D for Federer 2.5.12, p. 105.
    The approximants have measurable finite fibres, converge
    pointwise, and have norm error at most the original norm.
    This strengthens the local finite-piece approximation into
    a global sequence using the sealed partition laws. *)
Theorem dense_finite_vector_approximation (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (D : set E) (hD : is_rational_dense_subspace hN D)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (w : X -> real_norm_metric_space hN) :
  is_measure_measurable_function phi (partial_function_total w) ->
  exists g : nat -> X -> real_norm_metric_space hN,
    (forall n, is_measure_measurable_function phi (partial_function_total (g n))) /\
    (forall n, finite_set (g n @` setT)) /\
    (forall n x, D (g n x)) /\
    (forall n x, N (w x-g n x) <= N (w x)) /\
    (forall x, (fun n => g n x) @ \oo --> w x).
Proof.
move=> hw.
have [e [he1 he2]] := countable_enumeration hD.1 hD.2.2.1.
pose y n : real_norm_metric_space hN := if n is i.+1 then e i else 0.
have hy n : D (y n) by case: n=> [|n]; [exact: hD.2.2.1 | exact: he1].
have hyd : dense (y @` setT).
  apply: (dense_superset hD.2.1)=> v hv.
  have [n hn] := he2 v hv; exists n.+1=> //; exact hn.
pose q := @FiniteNearestApproximation.value R
  [the metricType R of real_norm_metric_space hN] y.
have hq := @FiniteNearestApproximation.laws R
  [the metricType R of real_norm_metric_space hN] y.
pose g n x := y (q n (w x)).
exists g; split.
- move=> n; exact: (measurable_total_borel_postcomposition hphi hw
    (finite_nearest_map_borel hq n)).
split.
- move=> n; apply: (sub_finite_set
    (B := (fun z => y (q n z)) @` setT)).
  + move=> z [x _ <-]; by exists (w x).
  + exact: finite_nearest_map_finite_image hq n.
split; first by move=> n x; exact: hy.
split.
- move=> n x.
  have hh := finite_nearest_map_reference_bound hq n (w x).
  change (is_true (N (w x-g n x) <= N (w x-0))) in hh.
  by rewrite subr0 in hh.
- move=> x; exact (@finite_nearest_map_converges R [the metricType R of real_norm_metric_space hN] y q hq hyd (w x)).
Qed.
