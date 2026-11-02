(** Federer (1969), 3.2.18, p. 255: disjoint compact charts for
    a finite-measure rectifiable measurable set. Existence discharges all
    laws of the independent specification in RectifiableCompactChartsUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  MeasureUP HausdorffMeasure RectifiableSetUP RectifiableCompactChartsUP
  RectifiableCompactChartLaws PositiveRectifiableCompactChart
  FiniteMeasureMaximalPositiveCover RectifiableChartEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [federer_3_2_18]: the whole lemma, Federer 3.2.18,
    p. 255. Compact parameter domains and global maps have pairwise
    disjoint images in W covering it up to H^m null mass. Each
    restriction is univalent, its inverse has Lipschitz bound lambda,
    and the actual differential exists with both displayed norm bounds
    at every parameter point. The proof expands the printed combination
    of earlier results by a maximal family of positive compact images. *)
Theorem federer_3_2_18 (R : realType) m n (lambda : R) (W : set (R_n R n)) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  1<lambda ->
  exists (K : nat -> set (R_n R m)) (psi : nat -> R_n R m -> R_n R n),
    is_rectifiable_compact_chart_cover lambda W K psi.
Proof.
move=> hRect hW hLam.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y m.
pose P : set (set Y) := [set C | @is_rectifiable_chart_piece R m n lambda W C /\ (0<mu C)%E].
have hEligible C (hC : P C) : C `<=` W /\ measure_measurable mu C /\ (0<mu C)%E.
  split; first exact hC.1.1.
  split; [exact: rectifiable_chart_piece_measurable hC.1|exact hC.2].
have hSupply A (hAm : measure_measurable mu A) (hAW : A `<=` W) (hAPos : (0<mu A)%E) :
    exists C, P C /\ C `<=` A.
  have [C [hC [hCA hPos]]] := positive_rectifiable_compact_chart hLam hRect hAm hAW hAPos.
  exists C; split; [by split|exact hCA].
have [G [hCount [hGP [hDis hNull]]]] := @finite_measure_maximal_positive_cover R Y
  mu W P (@hausdorff_measure_is_measure R Y m) hW hRect.2 hEligible hSupply.
have hLam0 : 0<=lambda := le_trans ler01 (ltW hLam).
apply: (@rectifiable_chart_family_enumeration R m n lambda W G hLam0 hCount hDis _ hNull).
by move=> C hC; exact: (hGP C hC).1.
Qed.
