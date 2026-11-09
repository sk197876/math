(** Federer (1969), 3.4.2(2)–(3), p. 310: the fixed subspace and the
    manifold family Ω. Projection charts are specified by their laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom ModuleQuotient SubspaceCarrier GrassmannSubspaces
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  InnerConvex NormMetric NormDifferentialUP NormRegularity EuclideanSubmanifoldUP
  EuclideanProjectionSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_critical_manifold_chart]: the projection chart in
    3.4.2(3), p. 310. Its kernel lies in Z, its original image is convex
    and open, and its class-k inverse satisfies both inverse equations.
    These equations specify the inverse independently of a construction. *)
Record is_critical_manifold_chart (R:realType) m mu k
    (Z:subspace (R_n R m)) (S:set (R_n R m))
    (p:euclidean_projection_space R m mu) (g:R_n R mu->R_n R m):Prop:={
  (** Source for [critical_chart_kernel]: ker p is contained in Z,
      3.4.2(3), p. 310. *)
  critical_chart_kernel:forall x,euclidean_projection_linear p x=0 ->Z x;
  (** Source for [critical_chart_convex_image]: the original projected
      manifold is convex, 3.4.2(3), p. 310. *)
  critical_chart_convex_image:is_inner_convex (euclidean_projection_linear p @` S);
  (** Source for [critical_chart_open_image]: the original projected
      manifold is open in R^mu, 3.4.2(3), p. 310. *)
  critical_chart_open_image:@open
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R mu)))
    (euclidean_projection_linear p @` S);
  (** Source for [critical_chart_inverse_class]: the inverse has class k
      on the original image, 3.4.2(3), p. 310. *)
  critical_chart_inverse_class:norm_class
    (inner_norm_real_norm (@euclidean_inner_productP R mu))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (euclidean_projection_linear p @` S) g k;
  (** Source for [critical_chart_left_inverse]: the inverse recovers
      every original source point, 3.4.2(3), p. 310. *)
  critical_chart_left_inverse:forall x,S x ->g (euclidean_projection_linear p x)=x;
  (** Source for [critical_chart_right_inverse]: the inverse takes values
      in S and is a right inverse on p(S), 3.4.2(3), p. 310. *)
  critical_chart_right_inverse:forall u,(euclidean_projection_linear p @` S) u ->
    S (g u) /\euclidean_projection_linear p (g u)=u
}.

(** Source for [critical_manifold_family]: Ω(mu,k) in 3.4.2(3), p. 310.
    Z has its actual basis dimension d and nu=m-d. The zero-dimensional
    alternative retains every class-k discrete submanifold; only positive
    dimension requires a global projection chart. *)
Definition critical_manifold_family (R:realType) m d
    (Z:G (R_n R m) d) mu k (S:set (R_n R m)):Prop:=
  (m-d<=mu)%N /\(0<k)%N /\is_euclidean_submanifold mu k S /\
  (mu=0%N \/exists (p:euclidean_projection_space R m mu) g,
    is_critical_manifold_chart k (grassmann_val Z) S p g).
