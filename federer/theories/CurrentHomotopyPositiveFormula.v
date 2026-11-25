(** Federer (1969), 4.1.9, p. 363: the original
    positive-degree current homotopy formula. The
    original cylinder also controls the boundary
    current. Reuse the preceding segment-product
    boundary, proper pushforward and endpoint laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate CurrentSpaces CurrentDirac CurrentBoundary
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentProperSupportLinear CurrentPushforwardSealed
  CurrentPushforwardCongruence CurrentPushforwardLinear OrientedSegmentProductBoundary
  CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopyDomain CurrentHomotopyCylinder
  CurrentHomotopySliceClass CurrentHomotopyTimeSegment CurrentHomotopyEndpointProper CurrentHomotopyPointProduct
  CurrentHomotopyEndpointPushforward CurrentHomotopyProductSupport CurrentHomotopyBoundaryCylinder CurrentDeformationChainSealed CurrentDeformationChainPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentHomotopyPositiveFormula.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation Z := (R_n R (1+n)%N).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:Z->Y).
Hypothesis hHomotopy:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation geometry := hHomotopy.1.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h geometry).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h geometry).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h geometry).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Local Notation CC := (@current_space R h2 (1+n)%N AU hAU j.+1).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h geometry).
Local Notation endpoint_classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hHomotopy).
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j.+1 A U V f g h geometry T.
Local Notation time := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j.+1 AT U hAT hU time T).
Local Notation product_boundary := (@current_boundary R h2 (1+n)%N j.+1 AU hAU product).
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu j.+1 A U V f g h hHomotopy T hProper).
Local Notation initial_proper := (@current_homotopy_start_proper R h2 n nu j.+1 A U V f g h geometry T hProper).
Local Notation final_proper := (@current_homotopy_end_proper R h2 n nu j.+1 A U V f g h geometry T hProper).

Local Notation boundary := (@current_boundary R h2 n j U hU T).
Local Notation boundary_proper := (@current_homotopy_boundary_cylinder_proper R h2 n nu j
  A U V f g h geometry T hProper).
Local Notation boundary_chain := (@CurrentDeformationChain.value R h2 n nu j A U V f g h
  hHomotopy boundary boundary_proper).
Local Notation F := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV T f
  endpoints.1 endpoint_classes.1 initial_proper).
Local Notation G := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV T g
  endpoints.2 endpoint_classes.2 final_proper).

(** Source for [current_homotopy_positive_formula]: g#T-f#T
    equals the boundary of the original deformation
    chain plus the deformation chain of boundary T,
    the first current homotopy formula in Federer
    4.1.9, p. 363. Every positive degree is
    retained, with only the original cylinder properness. *)
Theorem current_homotopy_positive_formula:
  G-F=@current_boundary R h2 nu j.+1 V hV chain+boundary_chain.
Proof.
have hZero:0<=(0:R)<=1 by rewrite lexx ler01.
have hOne:0<=(1:R)<=1 by rewrite ler01 lexx.
pose P0:@current_space R h2 (1+n)%N AU hAU j.+1:=
  @CartesianCurrentProduct.value R h2 1%N n 0%N j.+1 AT U hAT hU
  (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R 0)) T.
pose P1:@current_space R h2 (1+n)%N AU hAU j.+1:=
  @CartesianCurrentProduct.value R h2 1%N n 0%N j.+1 AT U hAT hU
  (@dirac_current R h2 1%N AT hAT (@euclidean_one_embed R 1)) T.
pose PB:@current_space R h2 (1+n)%N AU hAU j.+1:=
  @CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU time boundary.
pose hp0:=@current_homotopy_point_product_proper R h2 n nu j.+1 A U V f g h hHomotopy T hProper 0 hZero.
pose hp1:=@current_homotopy_point_product_proper R h2 n nu j.+1 A U V f g h hHomotopy T hProper 1 hOne.
pose hpB:=@current_homotopy_product_proper R h2 n nu j A U V f g h geometry boundary boundary_proper.
have hSegment:=@oriented_segment_product_boundary_positive R h2 1%N n AT U hAT hU
  (@euclidean_one_embed R 0) (@euclidean_one_embed R 1)
  (@current_homotopy_time_segment_domain R A hInterval) j T.
change (product_boundary=(P1-P0-PB:CC)) in hSegment.
pose E:@current_space R h2 (1+n)%N AU hAU j.+1:=(-1:R)*:P0+P1.
have hEndpoint:E=(P1-P0:CC) by rewrite /E scaleN1r addrC.
have hDifference:product_boundary=((-1:R)*:PB+E:CC).
  by rewrite hSegment hEndpoint scaleN1r addrC.
pose hpE:=@current_proper_support_linear R h2 (1+n)%N nu j.+1 AU hAU V h image
  (-1:R) P0 P1 hp0 hp1.
pose hpSum:=@current_proper_support_linear R h2 (1+n)%N nu j.+1 AU hAU V h image
  (-1:R) PB E hpB hpE.
pose hpBoundary:=@current_deformation_chain_boundary_proper R h2 n nu j.+1 A U V f g h
  hHomotopy T hProper.
have hPushDifference:=@current_pushforward_current_congruence R h2 (1+n)%N nu j.+1 AU V hAU hV
  h image hHomotopy.2 product_boundary ((-1:R)*:PB+E) hpBoundary hpSum hDifference.
have hLinear:=@current_pushforward_linear R h2 (1+n)%N nu j.+1 AU V hAU hV h image hHomotopy.2
  (-1:R) PB E hpB hpE hpSum.
have hEndpointLinear:=@current_pushforward_linear R h2 (1+n)%N nu j.+1 AU V hAU hV h image hHomotopy.2
  (-1:R) P0 P1 hp0 hp1 hpE.
have hBoundaryEquation:@current_boundary R h2 nu j.+1 V hV chain=(G-F)-boundary_chain.
  rewrite (@current_deformation_chain_boundary R h2 n nu j.+1 A U V f g h hHomotopy T hProper)
    hPushDifference hLinear hEndpointLinear.
  rewrite -(@current_deformation_chain_pushforward R h2 n nu j A U V f g h
      hHomotopy boundary boundary_proper)
    (@current_homotopy_initial_point_pushforward R h2 n nu j.+1 A U V f g h
      hHomotopy T hProper hZero)
    (@current_homotopy_final_point_pushforward R h2 n nu j.+1 A U V f g h
      hHomotopy T hProper hOne).
  by rewrite !scaleN1r [LHS]addrC [(-F+G)]addrC.
by rewrite hBoundaryEquation subrK.
Qed.
End CurrentHomotopyPositiveFormula.
