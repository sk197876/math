(** Federer (1969), 4.1.9, p. 364: the original
    displacement norm and endpoint differential norms
    are continuous on the original source. These
    supporting laws justify the measurable scalar
    integrands in all three affine mass estimates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional NormDifferentialLocal NormDifferentialLinear
  NormDifferentialChain NormDifferentialArithmetic NormFiniteLinearBound NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap EuclideanCurveJacobian
  CurrentMapDifferential CurrentCartesianAffineSlice CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopySliceClass CurrentHomotopyTimeVelocity
  CurrentAffineHomotopyDifferential CurrentExteriorOperatorMassBound EuclideanOperatorConvexBound
  EuclideanHomOperator OperatorNormUP OperatorNormSealed ExteriorGrading ExteriorPowers
  ExteriorMaps ExteriorHomogeneousProducts CurrentCoefficientNorms
  CurrentMapDifferentialNormContinuity CurrentDomain NormClassZeroArithmetic NormClassZeroTopology NormMetricContinuity
  RealMetricBackground ScalarNormExtendedEmbedding NormClassOneUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentAffineHomotopyScalarFields.
Variable R:realType.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Local Notation W := (R_n R 1%N).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation NZ := (inner_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation NW := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ := (inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Local Notation hNW := (inner_norm_real_norm (@euclidean_inner_productP R 1%N)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation slice := (@current_homotopy_slice_map R n nu h).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Local Notation P := (@euclidean_first_injection_map R 1%N n).
Local Notation Point t x := (@euclidean_block_join R 1%N n (@euclidean_one_embed R t,x)).

Local Notation UT := (current_domain R n U).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation Df x := (@current_map_differential R n nu U f x).
Local Notation Dg x := (@current_map_differential R n nu U g x).

(** Source for [current_affine_displacement_norm_continuous]:
    the actual original factor |g-f| is continuous on
    U, supporting its mass integrals in Federer 4.1.9,
    p. 364. Values outside U are not used. *)
Theorem current_affine_displacement_norm_continuous:
  continuous (fun x:UT=>(NY (g (set_val x)-f (set_val x)):real_line_metric R)).
Proof.
have hDelta:=@norm_class_zero_subtract R X Y NX NY hNY U g f
  (norm_class_continuous (classes.2 0%N)) (norm_class_continuous (classes.1 0%N)).
have hContinuous:=@norm_class_zero_restriction_continuous R X Y NX NY hNX hNY U
  (fun x=>g x-f x) hDelta.
move=>x B hB.
exact:(hContinuous x _
  (@real_norm_metric_norm_continuous R Y NY hNY (g (set_val x)-f (set_val x)) B hB)).
Qed.

(** Source for [current_affine_endpoint_differential_norms_continuous]:
    the actual original ||Df|| and ||Dg|| are continuous
    on U, supporting every original affine mass integral
    in Federer 4.1.9, p. 364. Their total
    representatives add no assertion outside U. *)
Theorem current_affine_endpoint_differential_norms_continuous:
  continuous (fun x:UT=>(Op (Df (set_val x)):real_line_metric R)) /\
  continuous (fun x:UT=>(Op (Dg (set_val x)):real_line_metric R)).
Proof.
have hF:=@current_class_one_differential_norm_continuous R n nu U f (classes.1 1%N).
have hG:=@current_class_one_differential_norm_continuous R n nu U g (classes.2 1%N).
split.
- have hContinuous:=@norm_class_zero_restriction_continuous R X R^o NX (fun t:R^o=>`|t|)
    hNX (@scalar_absolute_value_norm R) U (fun x=>Op (Df x)) hF.
  move=>x B hB;exact:(hContinuous x _ (@scalar_norm_real_identity_continuous R (Op (Df (set_val x))) B hB)).
- have hContinuous:=@norm_class_zero_restriction_continuous R X R^o NX (fun t:R^o=>`|t|)
    hNX (@scalar_absolute_value_norm R) U (fun x=>Op (Dg x)) hG.
  move=>x B hB;exact:(hContinuous x _ (@scalar_norm_real_identity_continuous R (Op (Dg (set_val x))) B hB)).
Qed.
End CurrentAffineHomotopyScalarFields.
