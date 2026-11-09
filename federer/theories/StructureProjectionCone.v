(** Federer (1969), 3.3.1, p. 287: the second displayed
    formula for X follows from the actual distance to ker p. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerNorm
  EuclideanProjectionSpace StructureCone StructureProjectionKernel
  StructureProjectionDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [structure_projection_coneE]: the second display
    of Federer 3.3.1, p. 287, in words: membership in X(a,r,ker p,s)
    is equivalent to s inverse times |p(x-a)| being strictly
    below |x-a|, and |x-a| being strictly below r. The original
    projection and its actual kernel occur, with no additional
    distance formula premise. *)
Theorem structure_projection_coneE (R:realType) n m (hmn:(m<=n)%N)
    (p:euclidean_projection_space R n m)
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (r: \bar R) (s:R) x:
  structure_cone (structure_projection_kernel hmn p) a r s x <->
    s^-1*inner_norm (@euclidean_inner_productP R m)
      (euclidean_projection_linear p (x-a)) <
        inner_norm (@euclidean_inner_productP R n) (x-a) /\
    ((inner_norm (@euclidean_inner_productP R n) (x-a))%:E<r)%E.
Proof.
have hd:=structure_projection_distance_laws (@structure_projection_kernelE R n m hmn p).
exact:((@structure_cone_specification R n (n-m)
  (structure_projection_kernel hmn p) a r s) _ hd x).
Qed.
