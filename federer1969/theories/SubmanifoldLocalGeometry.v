(** Federer (1969), 3.1.19, p. 231: coordinate systems give
    class-k retractions and every submanifold is locally compact.
    The topology is always that of the actual subset. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness NormMetric NormDifferentialUP NormRegularity RetractionUP
  NormCoordinateTopology NormRetractionLocalCompact MetricSubsetBackground
  EuclideanSubmanifoldUP SubmanifoldChartsUP SubmanifoldStraighteningCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [submanifold_local_retractions]: psi composed with
    phi retracts the coordinate neighbourhood onto B intersect T,
    Federer 3.1.19, p. 231. This includes class zero and mu=0. *)
Theorem submanifold_local_retractions (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k B ->
  forall b, B b -> exists T rho,
    norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) T b /\
    is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n))
      T (B `&` T) rho k.
Proof.
move=>hB b hb.
have hcharts:=submanifold_convex_coordinates hB.
have [T [V [phi [psi [hTb [hV [hphi [hpsi [hphiV [hpsiT [him hcan]]]]]]]]]]]:=hcharts b hb.
exists T,(fun x=>psi (phi x)); split=>//.
exact (@norm_coordinate_retraction R (R_n R n) (R_n R mu)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm (@euclidean_inner_productP R mu))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R mu))
  T (B `&` T) V phi psi k hphi hpsi (fun x hx=>hx.2) hphiV him hcan).
Qed.

(** Source for [submanifold_locally_compact]: every submanifold
    of Euclidean space is locally compact, Federer 3.1.19, p. 231.
    The proof uses the already proved coordinate retractions and
    compact closed norm balls; no positive class or dimension is assumed. *)
Theorem submanifold_locally_compact (R:realType) n mu k (B:set (R_n R n)) :
  @is_euclidean_submanifold R n mu k B ->
  locally_compact [set:metric_subset (fun x:real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R n))=>B x)].
Proof.
move=>hB.
exact (@finite_norm_locally_retracted_subset_compact R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R n))
  n (@coordinate_basis R n) (@coordinate_basisP R n) B k
  (@submanifold_local_retractions R n mu k B hB)).
Qed.
