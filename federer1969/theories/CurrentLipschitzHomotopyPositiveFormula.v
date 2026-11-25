(** Federer (1969), 4.1.14, p. 371: the
    locally Lipschitz image retains the original
    positive-degree homotopy formula of 4.1.9,
    p. 363. Apply the preceding segment-product
    boundary, actual image linearity and endpoint
    identities. The current is only locally flat;
    properness is required only on the original
    closed cylinder over its support. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanOneCoordinate CurrentSpaces CurrentDirac CurrentBoundary
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentProperSupportLinear
  OrientedSegmentProductBoundary CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopyTimeSegment
  CurrentHomotopyEndpointProper CurrentHomotopyProductSupport
  CurrentHomotopyBoundaryCylinder FlatCurrentsUP FlatCurrentUnion
  CurrentLocallyFlatBoundary CurrentLocallyFlatTimeCylinder
  CurrentLipschitzHomotopyUP CurrentLipschitzHomotopySlices
  CurrentLipschitzPushforwardSealed CurrentLipschitzPushforwardBasic
  CurrentLipschitzDeformationChainSealed
  CurrentLipschitzHomotopyEndpointPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentLipschitzHomotopyPositiveFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X:=(R_n R n).
Local Notation Y:=(R_n R nu).
Local Notation Z:=(R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_locally_lipschitz_current_homotopy R n nu A U V f g h.
Local Notation geometry:=hHomotopy.1.
Local Notation hU:=(current_homotopy_source_open geometry).
Local Notation hV:=(current_homotopy_target_open geometry).
Local Notation hA:=(current_homotopy_parameter_interval geometry).
Local Notation AT:=(@current_homotopy_time_domain R A).
Local Notation hAT:=(@current_homotopy_time_domain_open R A hA).
Local Notation AU:=(@current_homotopy_product_domain R n A U).
Local Notation hAU:=(@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation CC:=(@current_space R h2 (1+n)%N AU hAU j.+1).
Local Notation image:=(current_homotopy_image geometry).
Local Notation endpoints:=(current_homotopy_endpoint_images geometry).
Local Notation endpoint_local:=(@current_lipschitz_homotopy_endpoints R n nu
  A U V f g h geometry hHomotopy.2).
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hT:@is_locally_flat_current R h2 n j.+1 U hU T.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j.+1
  A U V f g h geometry T.
Local Notation time:=(@current_homotopy_time_segment R A hA h2).
Local Notation product:=(@CartesianCurrentProduct.value R h2 1%N n 1%N j.+1
  AT U hAT hU time T).
Local Notation product_local:=(@locally_flat_current_time_cylinder R h2 n j.+1
  A U hA hU T hT).
Local Notation product_boundary:=(@current_boundary R h2 (1+n)%N j.+1
  AU hAU product).
Local Notation chain:=(@CurrentLipschitzDeformationChain.value R h2 n nu j.+1
  A U V f g h hHomotopy T hT hProper).
Local Notation initial_proper:=(@current_homotopy_start_proper R h2 n nu j.+1
  A U V f g h geometry T hProper).
Local Notation final_proper:=(@current_homotopy_end_proper R h2 n nu j.+1
  A U V f g h geometry T hProper).
Local Notation boundary:=(@current_boundary R h2 n j U hU T).
Local Notation boundary_local:=(@locally_flat_current_boundary R h2 n j U hU T hT).
Local Notation boundary_proper:=(@current_homotopy_boundary_cylinder_proper R h2
  n nu j A U V f g h geometry T hProper).
Local Notation boundary_chain:=(@CurrentLipschitzDeformationChain.value R h2 n nu j
  A U V f g h hHomotopy boundary boundary_local boundary_proper).
Local Notation F:=(@CurrentLipschitzPushforward.value R h2 n nu j.+1
  U V hU hV f endpoints.1 endpoint_local.1 T hT initial_proper).
Local Notation G:=(@CurrentLipschitzPushforward.value R h2 n nu j.+1
  U V hU hV g endpoints.2 endpoint_local.2 T hT final_proper).

(** Source for [current_lipschitz_homotopy_positive_formula]:
    g#T-f#T equals boundary of the actual
    deformation chain plus the deformation chain
    of boundary T, the original positive-degree
    formula retained in Federer 4.1.14, p. 371.
    No normality, mass or compact-support hypothesis
    is imposed on the original locally flat T. *)
Theorem current_lipschitz_homotopy_positive_formula:
  G-F=@current_boundary R h2 nu j.+1 V hV chain+boundary_chain.
Proof.
have hZero:0<=(0:R)<=1 by rewrite lexx ler01.
have hOne:0<=(1:R)<=1 by rewrite ler01 lexx.
pose P0:CC:=@CartesianCurrentProduct.value R h2 1%N n 0%N j.+1
  AT U hAT hU (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R 0)) T.
pose P1:CC:=@CartesianCurrentProduct.value R h2 1%N n 0%N j.+1
  AT U hAT hU (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R 1)) T.
pose PB:CC:=@CartesianCurrentProduct.value R h2 1%N n 1%N j
  AT U hAT hU time boundary.
pose hP0:=@current_lipschitz_homotopy_point_product_locally_flat R h2 n nu j.+1
  A U V f g h hHomotopy T hT 0 hZero.
pose hP1:=@current_lipschitz_homotopy_point_product_locally_flat R h2 n nu j.+1
  A U V f g h hHomotopy T hT 1 hOne.
pose hPB:=@locally_flat_current_time_cylinder R h2 n j
  A U hA hU boundary boundary_local.
pose hp0:=@current_lipschitz_homotopy_point_product_proper R h2 n nu j.+1
  A U V f g h hHomotopy T hProper 0 hZero.
pose hp1:=@current_lipschitz_homotopy_point_product_proper R h2 n nu j.+1
  A U V f g h hHomotopy T hProper 1 hOne.
pose hpB:=@current_homotopy_product_proper R h2 n nu j
  A U V f g h geometry boundary boundary_proper.
have hSegment:=@oriented_segment_product_boundary_positive R h2 1%N n
  AT U hAT hU (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_homotopy_time_segment_domain R A hA) j T.
change (product_boundary=(P1-P0-PB:CC)) in hSegment.
pose E:CC:=(-1:R)*:P0+P1.
have hEndpoint:E=(P1-P0:CC) by rewrite /E scaleN1r addrC.
have hDifference:product_boundary=((-1:R)*:PB+E:CC).
  by rewrite hSegment hEndpoint scaleN1r addrC.
pose hE:=@locally_flat_current_linear_combination R h2 (1+n)%N j.+1
  AU hAU (-1:R) P0 P1 hP0 hP1.
pose hSum:=@locally_flat_current_linear_combination R h2 (1+n)%N j.+1
  AU hAU (-1:R) PB E hPB hE.
pose hBoundary:=@locally_flat_current_boundary R h2 (1+n)%N j.+1
  AU hAU product product_local.
pose hpE:=@current_proper_support_linear R h2 (1+n)%N nu j.+1
  AU hAU V h image (-1:R) P0 P1 hp0 hp1.
pose hpSum:=@current_proper_support_linear R h2 (1+n)%N nu j.+1
  AU hAU V h image (-1:R) PB E hpB hpE.
pose hpBoundary:=@current_lipschitz_deformation_chain_boundary_proper R h2
  n nu j.+1 A U V f g h hHomotopy T hProper.
have hPushDifference:=@current_lipschitz_pushforward_congruence R h2
  (1+n)%N nu j.+1 AU V hAU hV h image hHomotopy.2
  product_boundary ((-1:R)*:PB+E) hBoundary hSum hpBoundary hpSum hDifference.
have hLinear:=@current_lipschitz_pushforward_linear R h2 (1+n)%N nu j.+1
  AU V hAU hV h image hHomotopy.2 (-1:R) PB E hPB hE hpB hpE hpSum.
have hEndpointLinear:=@current_lipschitz_pushforward_linear R h2 (1+n)%N nu j.+1
  AU V hAU hV h image hHomotopy.2 (-1:R) P0 P1 hP0 hP1 hp0 hp1 hpE.
have hBoundaryEquation:@current_boundary R h2 nu j.+1 V hV chain=
    (G-F)-boundary_chain.
  rewrite (@current_lipschitz_deformation_chain_boundary R h2 n nu j.+1
    A U V f g h hHomotopy T hT hProper) hPushDifference hLinear hEndpointLinear.
  rewrite -(@current_lipschitz_deformation_chain_pushforward R h2 n nu j
      A U V f g h hHomotopy boundary boundary_local boundary_proper)
    (@current_lipschitz_homotopy_initial_point_pushforward R h2 n nu j.+1
      A U V f g h hHomotopy T hT hProper hZero)
    (@current_lipschitz_homotopy_final_point_pushforward R h2 n nu j.+1
      A U V f g h hHomotopy T hT hProper hOne).
  by rewrite !scaleN1r [LHS]addrC [(-F+G)]addrC.
by rewrite hBoundaryEquation subrK.
Qed.
End CurrentLipschitzHomotopyPositiveFormula.
