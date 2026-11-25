(** Federer (1969), 4.1.14, p. 371: identify the
    original smooth deformation-chain mass bound with the
    actual compact affine image. Openness and parameter
    evidence are aligned internally by proof irrelevance,
    as in the preceding source-neighbourhood proof of
    4.1.13, pp. 369–370. No mathematical premise or
    transport of the caller's current is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentSpaces CurrentMassSealed CurrentIntegrationCriterion
  NormalisedCurrentSealed CurrentMapDifferential EuclideanHomOperator
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentHomotopyCompactCylinder
  CurrentHomotopyProductSupport CurrentCompactMapProper
  CurrentDeformationChainPushforward CurrentCompactPushforwardAlgebra
  CurrentPushforwardDataIndependence CurrentSmoothAffineMajorantMassBound
  SummableRealFunctionUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentSmoothAffineCompactImageMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Hypothesis hA:@is_homotopy_parameter_interval R A.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variables f g:X->Y.
Variable h:Z->Y.
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Variable T:@current_space R h2 n U hU m.
Hypothesis hT:@is_integration_representable_current R h2 n m U hU T.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) (@current_support R h2 n U hU m T).
Local Notation time:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m AT U hAT hU time T).
Hypothesis hProductCompact:@compact (real_norm_metric_space hNZ)
  (@current_support R h2 (1+n)%N AU hAU (1+m)%N product).
Hypothesis hImage:forall z,AU z->V (h z).
Hypothesis hSmooth:norm_class_all_orders hNZ hNY AU h.
Hypothesis hAffine:forall t x,A t->U x->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Variable sigma:X->R.
Hypothesis hF:forall x,@current_support R h2 n U hU m T x->
  @euclidean_operator_norm R n nu (@current_map_differential R n nu U f x)<=sigma x.
Hypothesis hG:forall x,@current_support R h2 n U hU m T x->
  @euclidean_operator_norm R n nu (@current_map_differential R n nu U g x)<=sigma x.

(** Source for [current_smooth_affine_compact_image_mass]: the
    exact support-wise smooth affine majorant bound of
    Federer 4.1.14, p. 371, for the original compact
    pushforward of the interval product. Every original
    presentation of the source and target openness is allowed. *)
Theorem current_smooth_affine_compact_image_mass:
  (@CurrentMass.value R h2 nu (1+m)%N V hV
    (@current_compact_map_pushforward R h2 (1+n)%N nu AU V hAU hV h hImage hSmooth
      (1+m)%N product hProductCompact)<=
    measure_lower_integral (@NormalisedCurrent.measure R h2 n m U hU T hT)
      (real_total_integrand (fun x:current_domain R n U=>
        (NY (g (set_val x)-f (set_val x))*(sigma (set_val x))^+m)%R)))%E.
Proof.
have hParameter:hA=@current_homotopy_parameter_interval R n nu A U V f g h hH.1:=
  Prop_irrelevance _ _.
have hSource:hU=@current_homotopy_source_open R n nu A U V f g h hH.1:=
  Prop_irrelevance _ _.
have hTarget:hV=@current_homotopy_target_open R n nu A U V f g h hH.1:=
  Prop_irrelevance _ _.
subst hA hU hV.
pose hA:=@current_homotopy_parameter_interval R n nu A U V f g h hH.1.
pose hU:=@current_homotopy_source_open R n nu A U V f g h hH.1.
pose hV:=@current_homotopy_target_open R n nu A U V f g h hH.1.
pose hp:=@current_homotopy_compact_support_proper R h2 n nu m A U V f g h hH T hCompact.
have hBound:=@current_smooth_affine_majorant_mass_bound R h2 n nu m
  A U V f g h hH T hT hAffine hp sigma hF hG.
rewrite (@current_deformation_chain_pushforward R h2 n nu m A U V f g h hH T hp)
  in hBound.
pose hpProduct:=@current_homotopy_product_proper R h2 n nu m
  A U V f g h hH.1 T hp.
pose hpCompact:=@current_compact_map_proper R h2 (1+n)%N nu (1+m)%N
  AU V hAU product h hImage (norm_class_continuous (hSmooth 0%N)) hProductCompact.
have hSame:=@current_pushforward_data_independent R h2 (1+n)%N nu (1+m)%N AU V
  (@current_cartesian_domain_open R 1%N n AT U
    (@current_homotopy_time_domain_open R A
      (@current_homotopy_parameter_interval R n nu A U V f g h hH.1))
    (@current_homotopy_source_open R n nu A U V f g h hH.1))
  (@current_homotopy_target_open R n nu A U V f g h hH.1) product h
  (@current_homotopy_image R n nu A U V f g h hH.1) hImage hH.2 hSmooth
  hpProduct hpCompact.
rewrite /current_compact_map_pushforward -hSame.
exact:hBound.
Qed.
End CurrentSmoothAffineCompactImageMass.
