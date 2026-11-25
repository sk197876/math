(** Federer (1969), 4.1.7, pp. 355–359:
    the original open subset of Euclidean space
    is locally compact. Reuse the finite-norm
    local compactness theorem and its open-subspace
    law, also used in 4.1.5. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  FiniteNormEquivalence OpenSubspaceMeasure CurrentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_domain_locally_compact]: the
    original domain U has the local compactness
    required for its Radon positive-test supremum,
    supporting Federer 4.1.7, pp. 355–359. *)
Theorem current_domain_locally_compact (R:realType) n (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x):
  locally_compact [set:current_domain R n U].
Proof.
pose X:=R_n R n.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose XT:=real_norm_metric_space hN.
have hOpen:@open XT U.
  rewrite openE=>x hx;exact:(norm_domain_interior_neighbourhood hN U x).1 (@hU x hx).
have hLocal:=@finite_norm_locally_compact R X n (@coordinate_basis R n)
  (@coordinate_basisP R n) N hN.
exact:(@pseudometric_open_subspace_locally_compact R XT hLocal U hOpen).
Qed.
