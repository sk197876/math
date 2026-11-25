(** Federer (1969), 4.1.9, p. 363: the actual
    deformation chain is the preceding proper pushforward.
    Its boundary commutes with that pushforward by
    4.1.7, p. 359. All comparisons use public
    laws and uniqueness; the selected witness stays hidden. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentBoundary CurrentBoundarySupport
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentProperSupport CurrentProperSupportRestriction
  CurrentPushforwardExistence CurrentPushforwardSealed CurrentPushforwardBoundary CurrentPushforwardCongruence
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyCylinder CurrentHomotopyTimeSegment
  CurrentHomotopyProductSupport CurrentDeformationChainUP CurrentDeformationChainExistence
  CurrentDeformationChainSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDeformationChainPushforward.
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
Variable T:@current_space R h2 n U hU j.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h geometry T.
Local Notation time := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU time T).
Local Notation image := (@current_homotopy_image R n nu A U V f g h geometry).
Local Notation product_proper := (@current_homotopy_product_proper R h2 n nu j A U V f g h
  geometry T hProper).
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu j A U V f g h hHomotopy T hProper).
Local Notation product_boundary := (@current_boundary R h2 (1+n)%N j AU hAU product).

(** Source for [current_deformation_chain_pushforward]:
    the opaque chain equals h#([0,1] times T),
    the original definition in Federer 4.1.9,
    p. 363. This follows from the two public
    action laws and the preceding uniqueness theorem. *)
Theorem current_deformation_chain_pushforward:
  chain=@CurrentPushforward.value R h2 (1+n)%N nu (1+j)%N AU V hAU hV
    product h image hHomotopy.2 product_proper.
Proof.
apply:(@current_deformation_chain_unique R h2 n nu j A U V f g h hHomotopy T hProper).
- exact:(@CurrentDeformationChain.laws R h2 n nu j A U V f g h hHomotopy T hProper).
- exact:(@CurrentPushforward.laws R h2 (1+n)%N nu (1+j)%N AU V hAU hV
    product h image hHomotopy.2 product_proper).
Qed.

(** Source for [current_deformation_chain_boundary_proper]:
    the boundary of the original product has
    support on which h is proper, supporting
    the boundary computation in Federer 4.1.9,
    p. 363. No further properness is assumed. *)
Theorem current_deformation_chain_boundary_proper:
  @is_current_proper_on_support R h2 (1+n)%N nu j AU hAU V product_boundary h image.
Proof.
exact:(@current_proper_smaller_support R h2 (1+n)%N nu AU hAU V h image (1+j)%N j
  product product_boundary (@current_boundary_support_subset R h2 (1+n)%N j AU hAU product)
  product_proper).
Qed.

(** Source for [current_deformation_chain_boundary]:
    boundary(h#([0,1] times T)) equals h# of
    the product boundary, the first step of the
    original homotopy computation in Federer
    4.1.9, p. 363, by 4.1.7, p. 359.
    This applies also when T has degree zero. *)
Theorem current_deformation_chain_boundary:
  @current_boundary R h2 nu j V hV chain=
    @CurrentPushforward.value R h2 (1+n)%N nu j AU V hAU hV
      product_boundary h image hHomotopy.2 current_deformation_chain_boundary_proper.
Proof.
rewrite current_deformation_chain_pushforward.
have hBoundary:=@current_pushforward_boundary R h2 (1+n)%N nu j AU V hAU hV
  product h image hHomotopy.2 product_proper.
apply:(eq_trans hBoundary).
exact:(@current_pushforward_current_congruence R h2 (1+n)%N nu j AU V hAU hV h image
  hHomotopy.2 product_boundary product_boundary _ current_deformation_chain_boundary_proper
  (erefl product_boundary)).
Qed.
End CurrentDeformationChainPushforward.
