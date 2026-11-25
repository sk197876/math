(** Federer (1969), 3.2.47(3), p. 283: supporting
    transport to actual orthonormal Euclidean coordinates when
    applying 3.2.22. Only the public finite-inner-chart laws
    are used, and arbitrary original sets retain their actual
    finite Hausdorff rectifiability. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric FiniteInnerChartUP FiniteInnerCartesianGeometry
  LipschitzUP LipschitzBasic NormMetricScaleContinuity
  RectifiableSetUP FiniteMeasureRectifiableImages HausdorffMeasure
  TopologicalBorel ContinuousBorelPreimages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_chart_direct_lipschitz]: actual
    orthonormal parametrization preserves distances, by 1.7.1,
    p. 28, supporting the coarea coordinates of 3.2.47(3), p. 283. *)
Lemma finite_inner_chart_direct_lipschitz (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (A:set (R_n R n)):
  is_finite_inner_chart B e p ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space hB) A e.
Proof.
move=>hChart; apply:metric_lipschitz_of_bound; split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
change (is_true (inner_norm hB (e x-e y)<=inner_norm (@euclidean_inner_productP R n) (x-y))).
rewrite -linearB; by rewrite (finite_inner_chart_norm hB hChart).
Qed.

(** Source for [finite_inner_chart_coordinates_image]: exact
    original-set restoration through inverse coordinates, supporting
    3.2.47(3), p. 283, by the coordinate laws of 1.7.1, p. 28. *)
Lemma finite_inner_chart_coordinates_image (R:realType) (V:lmodType R)
    B n (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (S:set V):
  is_finite_inner_chart B e p ->e @` (p @` S)=S.
Proof.
move=>hChart; apply/seteqP; split=>x.
- move=>[z [y hy <-] <-]; by rewrite (finite_inner_chart_right_inverse hChart).
- move=>hx; exists (p x); last exact:finite_inner_chart_right_inverse hChart x.
  by exists x.
Qed.

(** Source for [finite_inner_chart_measure_rectifiable_coordinates]:
    actual finite rectifiability passes to Euclidean coordinates,
    supporting 3.2.22 in the converse proof of 3.2.47(3), p. 283.
    No source measurability or null hull excess is assumed. *)
Theorem finite_inner_chart_measure_rectifiable_coordinates (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) m (S:set V):
  is_finite_inner_chart B e p ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) m) m S ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m (p @` S).
Proof.
move=>hChart hS.
exact (@hausdorff_measure_rectifiable_lipschitz_image R (inner_metric_space hB)
  (inner_metric_space (@euclidean_inner_productP R n)) m S p
  (@finite_inner_chart_inverse_lipschitz R V B hB n e p S hChart) hS).
Qed.

(** Source for [finite_inner_chart_coordinates_borel]: actual
    Borel sets stay Borel in inverse coordinates, supporting
    the measurable slicing domains of 3.2.47(3), p. 283. *)
Lemma finite_inner_chart_coordinates_borel (R:realType) (V:lmodType R)
    B (hB:@is_inner_product R V B) n
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n)) (S:set V):
  is_finite_inner_chart B e p ->@borel_set (inner_metric_space hB) S ->
  @borel_set (inner_metric_space (@euclidean_inner_productP R n)) (p @` S).
Proof.
move=>hChart hS.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose Y:=inner_metric_space hB.
have [L [_ hBound]]:=@finite_inner_chart_direct_lipschitz R V B hB n e p setT hChart.
have hContinuous:continuous (fun z:X=>(e z:Y)).
  exact (metric_fixed_lipschitz_continuous hBound.1 (fun x y=>hBound.2 x y I I)).
have hImage:p @` S=e @^-1` S.
  apply/seteqP; split=>z.
  - move=>[x hx <-]; change (S (e (p x))).
    by rewrite (finite_inner_chart_right_inverse hChart).
  - move=>hz; exists (e z); first exact hz.
    exact:finite_inner_chart_left_inverse hChart z.
rewrite hImage; exact:(continuous_borel_preimage hContinuous hS).
Qed.
