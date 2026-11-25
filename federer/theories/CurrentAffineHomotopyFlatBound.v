(** Federer (1969), 4.1.13, pp. 369–370: the exact
    variable-rho flat estimate on a source on which the
    affine homotopy is defined. The support-neighbourhood
    and original-domain transport are supplied separately.
    Reuse the preceding current formulas and §4.1.9 mass bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanHomOperator OperatorNormUP OperatorNormSealed CurrentDomain CurrentSpaces
  CurrentBoundary CurrentMapDifferential CurrentIntegrationCriterion NormalCurrentsUP
  NormalisedCurrentSealed SmoothCompactSet CurrentPushforwardSealed
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass
  CurrentHomotopyCylinder CurrentHomotopyEndpointProper CurrentHomotopyBoundaryCylinder
  CurrentDeformationChainSealed CurrentFlatNorm CurrentHomotopyFlatBound
  CurrentAffineHomotopyMaximumBound MeasureIntegralBounds SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentAffineHomotopyFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation Op := (@euclidean_operator_norm R n nu).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:R_n R (1+n)%N->Y).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h hH.1).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hH).
Local Notation UT := (current_domain R n U).
Local Notation displacement := (fun x:UT=>NY (g (set_val x)-f (set_val x))).
Local Notation rho := (fun x:UT=>Num.max
  (Op (@current_map_differential R n nu U f (set_val x)))
  (Op (@current_map_differential R n nu U g (set_val x)))).
Hypothesis hAffine:forall t x,A t->U x->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Variable K:smooth_compact_set hNY V.

Section PositiveDegree.
Variable j:nat.
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hNormal:@is_locally_normal_current R h2 n U hU j.+1 T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j.+1 A U V f g h hH.1 T.
Hypothesis hImage:h @` (@current_homotopy_closed_cylinder R h2 n nu j.+1
  A U V f g h hH.1 T) `<=` smooth_compact_carrier K.
Local Notation boundary := (@current_boundary R h2 n j U hU T).
Local Notation mu := (@NormalisedCurrent.measure R h2 n j.+1 U hU T hNormal.1).
Local Notation muB := (@NormalisedCurrent.measure R h2 n j U hU boundary hNormal.2).
Local Notation cost := (measure_lower_integral mu
  (real_total_integrand (fun x:UT=>displacement x*(rho x)^+j.+1))).
Local Notation costB := (measure_lower_integral muB
  (real_total_integrand (fun x:UT=>displacement x*(rho x)^+j))).
Local Notation hpF := (@current_homotopy_start_proper R h2 n nu j.+1
  A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n nu j.+1
  A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV
  T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV
  T g endpoints.2 classes.2 hpG).
Local Notation hpB := (@current_homotopy_boundary_cylinder_proper R h2 n nu j
  A U V f g h hH.1 T hProper).

(** Source for [current_affine_homotopy_positive_flat_bound]:
    the positive-degree estimate in Federer 4.1.13,
    pp. 369–370, on the smaller homotopy source. Its
    two exact weights are |g-f|rho^(j+1) and |g-f|rho^j.
    The mass decomposition uses the original two chains;
    no global derivative constant replaces rho. *)
Theorem current_affine_homotopy_positive_flat_bound:
  (@current_flat_norm R h2 nu j.+1 V hV K (G-F)<=cost+costB)%E.
Proof.
have hFirst:=(@current_affine_homotopy_maximum_bound R h2 n nu j.+1
  A U V f g h hH T hNormal.1 hAffine hProper).2.
have hSecond:=(@current_affine_homotopy_maximum_bound R h2 n nu j
  A U V f g h hH boundary hNormal.2 hAffine hpB).2.
have hFlat:=@current_homotopy_positive_flat_bound R h2 n nu
  A U V f g h hH K j T hProper hImage.
exact:(le_trans hFlat (leeD hFirst hSecond)).
Qed.
End PositiveDegree.

Section DegreeZero.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hT:@is_integration_representable_current R h2 n 0%N U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu 0%N A U V f g h hH.1 T.
Hypothesis hImage:h @` (@current_homotopy_closed_cylinder R h2 n nu 0%N
  A U V f g h hH.1 T) `<=` smooth_compact_carrier K.
Local Notation mu := (@NormalisedCurrent.measure R h2 n 0%N U hU T hT).
Local Notation hpF := (@current_homotopy_start_proper R h2 n nu 0%N
  A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n nu 0%N
  A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV
  T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV
  T g endpoints.2 classes.2 hpG).

(** Source for [current_affine_homotopy_zero_flat_bound]:
    the degree-zero estimate in Federer 4.1.13,
    pp. 369–370, has only the original displacement
    integral. In particular, zero endpoint differential
    norms do not change the zeroth power into zero. *)
Theorem current_affine_homotopy_zero_flat_bound:
  (@current_flat_norm R h2 nu 0%N V hV K (G-F)<=
    measure_lower_integral mu (real_total_integrand displacement))%E.
Proof.
have hMass:=(@current_affine_homotopy_maximum_bound R h2 n nu 0%N
  A U V f g h hH T hT hAffine hProper).2.
have hWeight:(fun x:UT=>displacement x*(rho x)^+0%N)=displacement.
  by apply:funext=>x;rewrite expr0 mulr1.
rewrite hWeight in hMass.
exact:(le_trans (@current_homotopy_zero_flat_bound R h2 n nu
  A U V f g h hH K T hProper hImage) hMass).
Qed.
End DegreeZero.
End CurrentAffineHomotopyFlatBound.
