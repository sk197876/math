(** Federer (1969), 4.1.9, p. 363: the original
    time interval and time-space product are open in
    their existing Euclidean norm topologies. Use the
    previously proved scalar-coordinate topology adapter. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  RealMetricBackground InnerNorm InnerMetric HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanOneCoordinate EuclideanDistributionMeasureContext
  EuclideanCartesianMap CurrentCartesianDomain CurrentHomotopyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_homotopy_time_domain_open]: the
    original open A remains open under R=R^1,
    supporting the actual homotopy domain of Federer
    4.1.9, p. 363. *)
Theorem current_homotopy_time_domain_open (R:realType) (A:set R)
    (hA:@is_homotopy_parameter_interval R A):
  forall x,@current_homotopy_time_domain R A x->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R 1%N)) (@current_homotopy_time_domain R A) x.
Proof.
pose X:=R_n R 1%N.
pose N:=inner_norm (@euclidean_inner_productP R 1%N).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R 1%N).
pose XT:=real_norm_metric_space hN.
have hCoordinate:continuous (fun x:XT=>(@euclidean_one_project R x:real_line_metric R)).
  move=>x.
  exact:(@continuous_comp [the topologicalType of XT]
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R 1%N)]
    [the topologicalType of real_line_metric R]
    (fun z:XT=>(z:inner_metric_space (@euclidean_inner_productP R 1%N)))
    (@euclidean_one_project R) x (@euclidean_distribution_norm_to_inner R 1%N x)
    (@euclidean_one_project_continuous R x)).
have hOpen:@open XT (@current_homotopy_time_domain R A).
  exact:((@continuousP XT (real_line_metric R) (@euclidean_one_project R)).1
    hCoordinate A (@homotopy_parameter_open R A hA)).
move=>x hx.
apply:(@norm_domain_interior_neighbourhood R X N hN (@current_homotopy_time_domain R A) x).2.
exact:(@open_nbhs_nbhs XT x (@current_homotopy_time_domain R A) (conj hOpen hx)).
Qed.

(** Source for [current_homotopy_product_domain_open]: the
    original A times U is an open Euclidean
    domain, supporting Federer 4.1.9, p. 363,
    through the original block-coordinate product topology. *)
Theorem current_homotopy_product_domain_open (R:realType) n nu (A:set R)
    (U:set (R_n R n)) (V:set (R_n R nu))
    (f g:R_n R n->R_n R nu) (h:R_n R (1+n)%N->R_n R nu)
    (hGeometry:@is_current_homotopy_geometry R n nu A U V f g h):
  forall z,@current_homotopy_product_domain R n A U z->norm_domain_interior
    (inner_norm (@euclidean_inner_productP R (1+n)%N))
    (@current_homotopy_product_domain R n A U) z.
Proof.
exact:(@current_cartesian_domain_open R 1%N n (@current_homotopy_time_domain R A) U
  (@current_homotopy_time_domain_open R A
    (@current_homotopy_parameter_interval R n nu A U V f g h hGeometry))
  (@current_homotopy_source_open R n nu A U V f g h hGeometry)).
Qed.
