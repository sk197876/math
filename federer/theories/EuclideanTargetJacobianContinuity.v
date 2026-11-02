(** Federer (1969), 3.2.10, p. 248: supporting continuity
    of the target-degree Jacobian in its differential. The
    adjoint and top-source formulas are those of 1.7.6,
    pp. 33–34; no measure theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanHomOperator NormMetric
  EuclideanRectangularAdjoint EuclideanLinearJacobian EuclideanNormalJacobian
  EuclideanJacobianContinuity RealMetricBackground EuclideanInnerProduct FiniteCoordinates ExteriorOperatorNorm EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [euclidean_target_jacobian_continuous]: the
    measurability implicit in the first integral of Federer
    3.2.10, p. 248. Supporting continuity of J_n L,
    including singular maps and zero-dimensional spaces. *)
Theorem euclidean_target_jacobian_continuous (R:realType) m n:
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_linear_jacobian n L:real_line_metric R)).
Proof.
have he (L:Hom (R_n R m) (R_n R n)):euclidean_linear_jacobian n L=
    euclidean_linear_jacobian n (euclidean_rectangular_adjoint L).
  exact (@exterior_operator_adjoint_norm_equal R (euclidean_two_nonzero R)
    (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m n
    (@coordinate_basis R m) (@coordinate_basis R n)
    (@coordinate_basisP R m) (@coordinate_basisP R n) (hom_as_linear L)
    (hom_as_linear (euclidean_rectangular_adjoint L))
    (euclidean_rectangular_adjoint_pairing L) n).
have hfun:(fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_linear_jacobian n L:real_line_metric R))=
    (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
      (euclidean_linear_jacobian n (euclidean_rectangular_adjoint L):real_line_metric R)).
  apply:boolp.funext=>L; exact:he.
rewrite hfun; move=>L.
exact (continuous_comp (@euclidean_rectangular_adjoint_continuous R m n L)
  (@euclidean_top_jacobian_continuous R n m (euclidean_rectangular_adjoint L))).
Qed.
