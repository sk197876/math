(** Federer (1969), 3.2.35, pp. 271--272:
    the whole Steiner and Cauchy assertions
    for the original nonempty bounded convex body. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  MetricSetDistanceUP SteinerTubePolynomial SteinerTubeZeroDimension SteinerTubeInduction
  EuclideanOpenConvexBoundary ConvexBodyCauchy RectifiableSetUP HausdorffMeasure IntegralGeometricGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_steiner_tube_formula]: the
    entire first assertion of Federer 3.2.35,
    p. 271. The actual radius tube volume
    equals the printed polynomial for every
    original nonempty bounded convex S and
    every positive radius. Arbitrary source
    measurability and lower-dimensional bodies are
    retained. The explicit n=0 extension supplies
    the induction base without negative degrees. *)
Theorem convex_steiner_tube_formula (R:realType):
  forall n (S:set (inner_metric_space (@euclidean_inner_productP R n))) d,
    S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->
    is_steiner_tube_volume S d.
Proof.
elim=>[S d hNonempty hS hBound hD|k hIH S d hNonempty hS hBound hD].
- exact:steiner_tube_zero_dimension hNonempty hD.
- exact:(steiner_tube_induction_step hIH hNonempty hS hBound hD).
Qed.

(** Source for [federer_3_2_35]: the complete
    theorem in Federer 3.2.35, pp. 271--272:
    the original bounded convex body's Steiner
    polynomial, and for open S its genuinely
    finite rectifiable boundary with the Cauchy
    Hausdorff mass formula. Intrinsic volumes
    are the existing actual normalized projection
    averages, with proved zeroth coefficient one.
    The boundary proof applies the erratum
    p. 5, book p. 271 line 24:
    the radial map is g(x)^(-1)x. *)
Theorem federer_3_2_35 (R:realType) k
    (S:set (inner_metric_space (@euclidean_inner_productP R k.+1))) d:
  S!=set0 ->is_inner_convex S ->metric_set_bounded S ->is_metric_set_distance S d ->
  is_steiner_tube_volume S d /\
  (open S ->is_m_rectifiable k (closure S `\` interior S) /\
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R k.+1)) k (closure S `\` interior S)=
      ((2:R)%:E*@integral_geometric_gauge R k.+1 k (leqnSn k) 1 S)%E).
Proof.
move=>hNonempty hS hBound hD; split.
- exact:convex_steiner_tube_formula hNonempty hS hBound hD.
- move=>hOpen; split; last exact:convex_body_cauchy_formula hNonempty hOpen hS hBound.
  have hRect:=@euclidean_open_convex_boundary_rectifiable R k.+1 S hNonempty hOpen hS hBound.
  by rewrite subn1 /= in hRect.
Qed.
