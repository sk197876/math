(** Federer (1969), 3.2.46, pp. 281–282: actual
    path-Lipschitz maps preserve Hausdorff null sets and
    countably finite Hausdorff covers. A proved finite
    carrier bound suffices for these supporting assertions;
    the original metrics and real degrees remain explicit. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier
  RiemannianHausdorff RiemannianPathLipschitz RealHausdorffMeasure
  RealPowerPositiveLipschitz RealPower LipschitzUP HausdorffLipschitzImages
  MeasureUP MeasureAlmostBasic ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_hausdorff_image_finite_bound]:
    a positive finite Hausdorff image bound supporting
    3.2.46, p. 282, through 2.10.11, p. 176.
    The auxiliary bound may be enlarged by the finite
    carrier; no sharp original Lipschitz constant is claimed.
    All nonnegative real degrees and arbitrary subsets remain. *)
Theorem riemannian_hausdorff_image_finite_bound (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f -> exists L : R, 0<L /\ forall p (hp : 0<=p) S,
    (riemannian_hausdorff_measure hh p hp (f @` S)<=
      (real_power L p)%:E*riemannian_hausdorff_measure hg p hp S)%E.
Proof.
move=> hLip.
have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
exists L; split; first exact hL.
move=> p hp S; rewrite !riemannian_hausdorff_carrier.
exact (@real_hausdorff_positive_lipschitz R
  [the metricType R of riemannian_metric_space hg]
  [the metricType R of riemannian_metric_space hh] f L p hp hL hBound S).
Qed.

(** Source for [riemannian_natural_hausdorff_image_finite_bound]:
    natural-degree specialization for actual finite image
    covers in 3.2.46, p. 282. Dimension zero, empty
    subsets and infinite masses are retained. *)
Theorem riemannian_natural_hausdorff_image_finite_bound (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh) :
  is_riemannian_path_lipschitz f -> exists L : R, 0<L /\ forall k (hp : 0<=k%:R :> R) S,
    (riemannian_hausdorff_measure hh k%:R hp (f @` S)<=
      (L^+k)%:E*riemannian_hausdorff_measure hg k%:R hp S)%E.
Proof.
move=> hLip.
have [L [hL hBound]] := @riemannian_path_lipschitz_carrier R m n A B g h hg hh f hLip.
exists L; split; first exact hL.
move=> k hp S; rewrite !riemannian_hausdorff_carrier !real_hausdorff_measure_natural.
exact (@hausdorff_lipschitz_image_bound R
  [the metricType R of riemannian_metric_space hg]
  [the metricType R of riemannian_metric_space hh] f L k hBound S).
Qed.

(** Source for [riemannian_path_lipschitz_null_image]:
    actual Hausdorff null-image preservation in every real
    degree, supporting 3.2.46, p. 282. No source
    measurability or finite metric-component hypothesis is added. *)
Corollary riemannian_path_lipschitz_null_image (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    p (hp : 0<=p) S :
  is_riemannian_path_lipschitz f -> riemannian_hausdorff_measure hg p hp S=0%E ->
  riemannian_hausdorff_measure hh p hp (f @` S)=0%E.
Proof.
move=> hLip hNull.
have [L [hL hBound]] := @riemannian_hausdorff_image_finite_bound R m n A B g h hg hh f hLip.
have hEstimate := hBound p hp S; rewrite hNull mule0 in hEstimate.
by apply/eqP; rewrite eq_le hEstimate (measure_nonnegative
  (@riemannian_hausdorff_is_measure R n B h hh p hp)).
Qed.
