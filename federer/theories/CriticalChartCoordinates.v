(** Federer (1969), 3.4.2(7), p. 314: the original projection
    and inverse chart form a coordinate system for relative calculus. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormDifferentialUP NormClassOneUP NormRegularity
  NormRegularityOperations NormCoordinateSystemUP EuclideanProjectionSpace
  CriticalManifoldFamilyUP CriticalManifoldChartLaws CriticalChartRetractionClass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_chart_coordinate_system]: the inverse
    (p|S)^(-1) used to define F in 3.4.2(7), p. 314. The chart
    laws give the exact coordinate image and inverse identities.
    The projection is bounded linear on the original open preimage
    domain. This permits direct use of the relative calculus of
    3.1.22, pp. 235–236. *)
Theorem critical_chart_coordinate_system (R:realType) m mu k
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) g:
  is_critical_manifold_chart k Z S p g ->
  is_norm_coordinate_system
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R mu)) S
    (fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x))
    (euclidean_projection_linear p @` S) (euclidean_projection_linear p) g k.
Proof.
move=>hChart.
pose X:=R_n R m;pose V:=R_n R mu.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NV:=inner_norm (@euclidean_inner_productP R mu).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNV:=inner_norm_real_norm (@euclidean_inner_productP R mu).
pose U:=fun x=>(euclidean_projection_linear p @` S) (euclidean_projection_linear p x).
have hR:=critical_chart_retraction_class hChart.
have hInterior x (hx:U x):norm_domain_interior NX U x:=(norm_class_continuous hR hx).1.
have hPClass:=@norm_class_linear R X V NX NV hNX hNV U
  (hom_of_linear (euclidean_projection_linear p)) k hInterior
  (critical_projection_bounded_linear p).
have hSU:S `<=` U by move=>x hx;exists x.
constructor.
- exact:hPClass.
- exact:(critical_chart_inverse_class hChart).
- by move=>x.
- rewrite (critical_chart_inverse_image hChart).
  apply/seteqP;split;[by move=>x hx;split;last exact:hSU x hx|by move=>x [hx _]].
- move=>u hu;exact:(critical_chart_right_inverse hChart hu).2.
Qed.
