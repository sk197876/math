(** Federer (1969), 4.1.4, p. 349: zero coordinate
    derivatives imply constancy on C_e. This adapter uses
    the earlier uniqueness of directional limits, the actual
    first differential and the released rank-zero inference. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormDifferentialLocal
  NormDifferentialDirectional NormedCurveDerivativeUP NormClassOneUP NormBoundedLinearTopology
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CoordinateZeroConnectedConstancy.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [connected_zero_coordinate_quotients_constant]:
    the constancy inference for the actual smoothed dual
    density in Federer 4.1.4, p. 349. No separability or
    finite-dimensional target premise is required. *)
Theorem connected_zero_coordinate_quotients_constant (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A:set (R_n R n)) (f:R_n R n->Y):
  norm_class_one (inner_norm (@euclidean_inner_productP R n)) NY (fun _=>True) f ->
  @open (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A ->
  @connected (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) A ->
  (forall x,A x ->forall i:'I_n,
    punctured_norm_limit NY
      (fun t=>t^-1*:(f (x+t*:(@coordinate_basis R n i))-f x)) 0) ->
  forall a b,A a ->A b ->f b=f a.
Proof.
move=>[D hD] hOpen hConnected hZero.
pose N:=inner_norm (@euclidean_inner_productP R n).
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
apply:(@connected_zero_coordinate_differential_constant R n Y NY hNY A f D hConnected).
- move=>x hx.
  have hNbhs:nbhs (x:real_norm_metric_space hN) A.
    move:hOpen; rewrite openE; exact.
  have hInterior:=(@norm_domain_interior_neighbourhood R (R_n R n) N hN A x).2 hNbhs.
  apply:(@norm_differential_restrict R (R_n R n) Y N NY (fun _=>True) A f x (D x)
    (fun _ _=>Logic.I) hInterior).
  exact:(norm_class_one_differential hD Logic.I).
- move=>x hx i.
  apply:(@punctured_norm_limit_unique R Y NY hNY
    (fun t=>t^-1*:(f (x+t*:(@coordinate_basis R n i))-f x)) (D x (@coordinate_basis R n i)) 0).
  + exact:(norm_differential_directional_limit hN hNY
      (norm_class_one_differential hD Logic.I) (@coordinate_basis R n i)).
  + exact:(@hZero x hx i).
Qed.
