(** Federer (1969), 3.2.46, p. 282: a
    frozen pair of metric forms computes the target-degree
    Jacobian continuously in the original linear map.
    Local linear isometries are existence witnesses only. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanHomOperator NormMetric
  EuclideanLinearJacobian InnerProductUP RiemannianLinearJacobian PositiveSymmetricNormFactor
  EuclideanTargetJacobianContinuity EuclideanSliceJacobianRepresentative
  EuclideanHomPostcomposeContinuity RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [frozen_riemannian_target_jacobian_continuous]:
    continuity implicit in the local coarea reduction of
    3.2.46, p. 282. The actual source and
    target forms remain fixed; singular maps and target
    degree zero are included by 1.7.6, pp. 33–34. *)
Theorem frozen_riemannian_target_jacobian_continuous (R : realType) m n B C
    (hB : @is_inner_product R (R_n R m) B)
    (hC : @is_inner_product R (R_n R n) C) :
  continuous (fun D : real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (riemannian_linear_jacobian hB hC n D : real_line_metric R)).
Proof.
have [L hL] := positive_symmetric_norm_factor_exists hB.
have [M hM] := positive_symmetric_norm_factor_exists hC.
have [I [hLI [hIL hCoordinates]]] := riemannian_linear_jacobian_coordinates hL hM.
have hEqual : (fun D : real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (riemannian_linear_jacobian hB hC n D : real_line_metric R)) =
    (fun D : real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
      (euclidean_linear_jacobian n (hom_comp (hom_of_linear M)
        (hom_comp D (hom_of_linear I))) : real_line_metric R)).
  apply:funext=> D; exact:hCoordinates.
rewrite hEqual=> D.
exact (continuous_comp (@euclidean_hom_precompose_continuous R m n m (hom_of_linear I) D)
  (continuous_comp (@euclidean_hom_postcompose_continuous R m n n (hom_of_linear M)
    (hom_comp D (hom_of_linear I)))
    (@euclidean_target_jacobian_continuous R m n
      (hom_comp (hom_of_linear M) (hom_comp D (hom_of_linear I)))))).
Qed.
