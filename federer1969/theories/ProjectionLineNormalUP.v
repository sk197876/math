(** Federer (1969), 3.2.35, p. 272:
    independent linear laws for the normal line
    of a codimension-one orthogonal projection. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct EuclideanProjectionSpace EuclideanProjectionMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_projection_line_normal]: the
    line direction of the boundary fibres for
    p in O*(n,n-1), Federer 3.2.35,
    p. 272, from the orthogonal projection
    laws of 1.7.4, p. 30. Unit length,
    membership in the actual kernel and its
    exact scalar spanning law precede a separate
    proved existence theorem. No endpoint, boundary
    fibre or multiplicity conclusion is assumed. *)
Record is_projection_line_normal (R:realType) k
    (p:orthogonal_projection_metric_space R k.+1 k) (w:R_n R k.+1):Prop:={
  projection_line_normal_unit:euclidean_inner_product w w= 1;
  projection_line_normal_kernel:euclidean_projection_linear p w=0;
  projection_line_normal_span:forall z,euclidean_projection_linear p z=0 ->
    z=euclidean_inner_product z w*:w
}.
