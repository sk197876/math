(** Federer (1969), 3.2.3, p. 243: measurability of the
    top-source Jacobian is used in the area integral. This
    supporting continuity follows from the exterior map laws
    and finite-dimensional operator-space topology of 1.7.6. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom HomInner TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  NormMetric EuclideanHomOperator HomSpaceNormTopology HomeomorphismUP
  EuclideanLinearMaps EuclideanLinearJacobian FiniteExteriorPowers SimpleElementary
  ExteriorGrading ExteriorMaps ExteriorNorm ExteriorFrameUnitNorm ExteriorOperatorNorm
  TopExteriorNorm ExteriorMapNormContinuity RealMetricBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_top_jacobian_continuous]: supporting
    the integrand in Federer 3.2.3, p. 243. The
    source-top Jacobian is continuous in the operator norm,
    including zero-dimensional and singular maps. *)
Theorem euclidean_top_jacobian_continuous (R:realType) m n:
  continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_linear_jacobian m L:real_line_metric R)).
Proof.
pose w:=e_lambda (@coordinate_basis R m) (ord_tuple m).
have hw:exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R m) w= 1.
  exact (euclidean_top_product_unit_norm (euclidean_two_nonzero R) m).
have he L:euclidean_linear_jacobian m L=
    exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
      (exterior_power_map (hom_as_linear L) m w).
  exact (@top_exterior_operator_unit_value R (euclidean_two_nonzero R)
    (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R m) (@euclidean_inner_productP R n) m
    (@coordinate_basis R m) (@coordinate_basisP R m) (hom_as_linear L) w hw).
have hHome:=@hom_space_norm_homeomorphism R (R_n R m) (R_n R n)
  (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n)
  (@euclidean_operator_norm R m n) (@euclidean_operator_norm_is_norm R m n).
have hc:=@exterior_map_norm_continuous R (euclidean_two_nonzero R)
  (R_n R m) (R_n R n) (@euclidean_inner_product R m) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m) m w (product_simple _).
have hfun:(fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (euclidean_linear_jacobian m L:real_line_metric R))=
    (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
      (exterior_norm (euclidean_two_nonzero R) (@euclidean_inner_productP R n)
        (exterior_power_map (hom_as_linear L) m w):real_line_metric R)).
  by apply:funext=>L; exact (he L).
have hId:continuous (fun L:real_norm_metric_space (@euclidean_operator_norm_is_norm R m n)=>
    (L:inner_metric_space (hom_inner_productP (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R n) (@coordinate_basisP R m)))).
  exact (homeomorphism_inverse_continuous hHome).
rewrite hfun; move=>L.
exact (continuous_comp (hId L) (hc L)).
Qed.
