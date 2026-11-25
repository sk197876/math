(** Federer (1969), 3.3.20, p. 307: actual extremal projection and Gross lower bound. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct PowerCantorPairUP EuclideanOneCoordinate EuclideanProjectionSpace
  EuclideanLebesgueDimensions EuclideanScalarLength PlanarUnitProjectionExistence
  CriticalProjectionScalarBound CriticalOriginalExtremalProjection GrossOriginalProjectionBound
  ProjectionMeasure LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_original_extremal_projection_volume]: an
    actual member of the original O*(2,1) attains projected L^1
    volume 3/sqrt(5) on the unchanged original E, 3.3.20, p. 307.
    Unit-frame existence and exact scalar/Euclidean measure compatibility
    discharge every projection and normalization premise. *)
Theorem critical_original_extremal_projection_volume (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  exists p:euclidean_projection_space R 2 1,
    euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` euclidean_cantor_product A A)=
      (3/Num.sqrt (5:R))%:E.
Proof.
move=>hc hPair.
pose u:=(2:R)/Num.sqrt 5.
pose v:=(1:R)/Num.sqrt 5.
have [_ [_ [hUnit _]]]:=@critical_projection_extremal_direction R.
have [p hP]:=planar_unit_coordinate_projection_exists hUnit.
have [_ hMass]:=@critical_original_extremal_projection R c A f hc hPair.
exists p;rewrite euclidean_one_measure_scalar_image image_comp.
have hFunction:(fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x))=
    (fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x).
  apply:funext=>x;exact:hP x.
change (lebesgue_scalar_measure
  ((fun x:inner_metric_space (@euclidean_inner_productP R 2)=>
    euclidean_one_project (euclidean_projection_linear p x)) @` euclidean_cantor_product A A)=(3/Num.sqrt (5:R))%:E).
by rewrite hFunction.
Qed.

(** Source for [critical_original_cantor_square_gross_lower]: the
    Gross lower bound 3/sqrt(5) in 3.3.20, p. 307, follows from
    the actual original extremal projection and the existing original-set
    projection comparison. No supplied maximizing projection or desired
    Gross value is an extra hypothesis. *)
Theorem critical_original_cantor_square_gross_lower (R:realType) (c:R)
    (A:set (real_line_metric R)) (f:R->R):
  0<c ->is_power_cantor_pair c (1/2:R) (fun _:nat=>2%N) A f ->
  ((3/Num.sqrt (5:R))%:E<=@gross_measure R 2 1 (euclidean_cantor_product A A))%E.
Proof.
move=>hc hPair.
have [p hValue]:=critical_original_extremal_projection_volume hc hPair.
have h:=@gross_original_projection_bound R 2 1 (leqnSn 1) (euclidean_cantor_product A A) p.
by rewrite hValue in h.
Qed.
