(** Federer (1969), 4.1.14, p. 371: each compatible
    smooth affine image of [0,1] times T has the exact
    mass bound with weight |b_i-a_i|(sigma+eta_i)^m.
    Reuse the actual deformation chain of 4.1.9, p. 363,
    its public pushforward identity and the original
    support-wise smooth majorant estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate SmoothCompactSet CurrentDomain CurrentSpaces
  CurrentMassSealed CurrentIntegrationCriterion NormalisedCurrentSealed
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain
  CurrentHomotopyTimeSegment CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentHomotopyCompactCylinder CurrentDeformationChainSealed
  CurrentDeformationChainPushforward CurrentAffineHomotopyUP CurrentAffineHomotopySealed
  CurrentAffineHomotopyGeometry CurrentCompactPushforwardAlgebra
  CurrentPushforwardDataIndependence CurrentSmoothApproximationUP
  CurrentAffineMajorantApproximationUP CurrentSmoothAffineMajorantMassBound
  CurrentSmoothAffineCompactImageMass
  SummableRealFunctionUP MeasureIntegralBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineMajorantSmoothImageMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNZ:=(inner_norm_real_norm (@euclidean_inner_productP R (1+n)%N)).
Variables (U:set X) (V:set Y).
Hypothesis hV:forall y,V y->norm_domain_interior NY V y.
Variable K:smooth_compact_set hNX U.
Variables f g:X->Y.
Variable sigma:X->R^o.
Variables (A:set R) (W:set X) (a b:nat->X->Y) (eta:nat->R).
Hypothesis hData:@is_current_affine_majorant_approximation R n nu U V K f g sigma
  A W a b eta.
Local Notation hA:=(current_affine_majorant_parameter hData).
Local Notation hW:=(current_affine_majorant_domain_open hData).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A W).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT W hAT hW).
Local Notation hFirst:=(current_affine_majorant_first_approximation hData).
Local Notation hSecond:=(current_affine_majorant_second_approximation hData).
Local Notation hHomotopyApprox:=(current_affine_majorant_homotopy_approximation hData).
Local Notation Hi i:=(@CurrentAffineHomotopy.value R n nu (a i) (b i)).

(** Source for [current_affine_majorant_smooth_homotopy]:
    every actual affine approximant is an original smooth
    homotopy on the same open A times W, supporting
    Federer 4.1.14, pp. 371–372. Its whole-source
    image is the proved approximation-family law. *)
Definition current_affine_majorant_smooth_homotopy i:
  @is_smooth_current_homotopy R n nu A W V (a i) (b i) (Hi i).
Proof.
refine (conj (@Build_is_current_homotopy_geometry R n nu A W V
  (a i) (b i) (Hi i) hA hW hV _ _ _)
  (current_smooth_approximation_class hHomotopyApprox i)).
- exact:current_smooth_approximation_image hHomotopyApprox i.
- move=>x _;exact:(@current_affine_homotopy_start R n nu (a i) (b i) (Hi i)
    (@CurrentAffineHomotopy.laws R n nu (a i) (b i)) x).
- move=>x _;exact:(@current_affine_homotopy_end R n nu (a i) (b i) (Hi i)
    (@CurrentAffineHomotopy.laws R n nu (a i) (b i)) x).
Defined.

Variable T:@current_space R h2 n W hW m.
Hypothesis hT:@is_integration_representable_current R h2 n m W hW T.
Hypothesis hSupport:@current_support R h2 n W hW m T `<=` smooth_compact_carrier K.
Hypothesis hCompact:@compact (real_norm_metric_space hNX) (@current_support R h2 n W hW m T).
Local Notation time:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N m
  AT W hAT hW time T).
Hypothesis hProductCompact:@compact (real_norm_metric_space hNZ)
  (@current_support R h2 (1+n)%N AU hAU (1+m)%N product).
Local Notation image i:=(@current_compact_map_pushforward R h2 (1+n)%N nu AU V hAU hV
  (Hi i) (current_smooth_approximation_image hHomotopyApprox i)
  (current_smooth_approximation_class hHomotopyApprox i) (1+m)%N product hProductCompact).
Local Notation mu:=(@NormalisedCurrent.measure R h2 n m W hW T hT).

(** Source for [current_affine_majorant_smooth_image_mass]: the
    exact smooth affine-chain majorant integral before taking
    the limit in Federer 4.1.14, p. 371. The original
    source variation is retained. No normality of T or
    extra differential assumption for that variation is needed. *)
Theorem current_affine_majorant_smooth_image_mass i:
  (@CurrentMass.value R h2 nu (1+m)%N V hV (image i)<=
    measure_lower_integral mu (real_total_integrand
      (fun x:current_domain R n W=>
        (NY (b i (set_val x)-a i (set_val x))*(sigma (set_val x)+eta i)^+m)%R)))%E.
Proof.
pose hH:=current_affine_majorant_smooth_homotopy i.
have hAffine:forall t x,A t->W x->
    @current_homotopy_slice_map R n nu (Hi i) t x=(1-t)*:a i x+t*:b i x.
  move=>t x _ _;exact:CurrentAffineHomotopy.laws.
have hBound:=@current_smooth_affine_compact_image_mass R h2 n nu m A W V hA hW hV
  (a i) (b i) (Hi i) hH T hT hCompact hProductCompact
  (current_smooth_approximation_image hHomotopyApprox i)
  (current_smooth_approximation_class hHomotopyApprox i) hAffine
  (fun x=>sigma x+eta i)
  (fun x hx=>@current_affine_majorant_first_cap R n nu U V K f g sigma
    A W a b eta hData i x (@hSupport x hx))
  (fun x hx=>@current_affine_majorant_second_cap R n nu U V K f g sigma
    A W a b eta hData i x (@hSupport x hx)).
exact hBound.
Qed.
End CurrentAffineMajorantSmoothImageMass.
