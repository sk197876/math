(** Federer (1969), 3.3.20, p. 307: continuous actual coordinates on the original line-projection space. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane MetricCartesianProductUP
  EuclideanOneCoordinate EuclideanProjectionSpace TopologicalProductMaps PlanarProjectionCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.

(** Source for [planar_projection_first_coefficient]: the actual first
    coefficient u_1 of P_u in 3.3.20, p. 307, evaluated on the
    existing first coordinate vector. No normal vector is selected. *)
Definition planar_projection_first_coefficient (R:realType) (p:euclidean_projection_space R 2 1):R:=
  euclidean_one_project (euclidean_projection_linear p (@euclidean_real_plane_pair R 1 0)).

(** Source for [planar_projection_second_coefficient]: the actual second
    coefficient u_2 of P_u in 3.3.20, p. 307. *)
Definition planar_projection_second_coefficient (R:realType) (p:euclidean_projection_space R 2 1):R:=
  euclidean_one_project (euclidean_projection_linear p (@euclidean_real_plane_pair R 0 1)).

(** Source for [planar_projection_actual_coefficient_laws]: the actual
    coordinate evaluations have unit squared sum and give the exact
    original projection formula, 3.3.20, p. 307. *)
Theorem planar_projection_actual_coefficient_laws (R:realType) (p:euclidean_projection_space R 2 1):
  let u:=planar_projection_first_coefficient p in
  let v:=planar_projection_second_coefficient p in
  u^+2+v^+2= 1 /\forall x:inner_metric_space (@euclidean_inner_productP R 2),
    euclidean_one_project (euclidean_projection_linear p x)=
      u * euclidean_real_plane_first x+v * euclidean_real_plane_second x.
Proof.
move=>u v;have [a [b [hUnit hFormula]]]:=planar_original_projection_unit_coordinates p.
have hU:u=a.
  rewrite /u /planar_projection_first_coefficient hFormula
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) mulr1 mulr0 addr0.
  by [].
have hV:v=b.
  rewrite /v /planar_projection_second_coefficient hFormula
    (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) mulr0 mulr1 add0r.
  by [].
by rewrite hU hV;split.
Qed.

(** Source for [planar_projection_fixed_scalar_value_continuous]:
    continuity of actual coefficient evaluations for the open direction
    family in 3.3.20, p. 307. The existing joint projection evaluation
    and scalar coordinate maps prove it. *)
Theorem planar_projection_fixed_scalar_value_continuous (R:realType)
    (x:inner_metric_space (@euclidean_inner_productP R 2)):
  continuous (fun p:euclidean_projection_space R 2 1=>
    (euclidean_one_project (euclidean_projection_linear p x):real_line_metric R)).
Proof.
pose P:=euclidean_projection_space R 2 1.
pose E:=inner_metric_space (@euclidean_inner_productP R 2).
have hPair:continuous (fun p:P=>(p,x)).
  apply:topological_pair_continuous;last exact:cst_continuous.
  by move=>p;exact:cvg_id.
have hImage:continuous (fun p:P=>(euclidean_projection_linear p x:
    inner_metric_space (@euclidean_inner_productP R 1))).
  move=>p;exact:continuous_comp (hPair p) (@euclidean_projection_evaluation_continuous R 2 1 (p,x)).
move=>p;exact:continuous_comp (hImage p) (@euclidean_one_project_continuous R (euclidean_projection_linear p x)).
Qed.
