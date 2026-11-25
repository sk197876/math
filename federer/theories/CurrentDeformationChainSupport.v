(** Federer (1969), 4.1.10, p. 364: the original cone is
    supported in the image of the closed time cylinder over spt T.
    This general supporting homotopy law reuses the exact product
    support and original proper-pushforward support theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentPushforwardSealed CurrentPushforwardSupport
  CurrentHomotopyUP CurrentHomotopyDomain CurrentHomotopyTimeSegment CurrentHomotopyCylinder
  CurrentHomotopyProductSupport CurrentDeformationChainSealed CurrentDeformationChainPushforward.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentDeformationChainSupport.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n nu j : nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Variable A : set R.
Variables (U : set X) (V : set Y).
Variables (f g : X -> Y) (h : R_n R (1+n)%N -> Y).
Hypothesis hH : @is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Local Notation hInterval := (@current_homotopy_parameter_interval R n nu A U V f g h hH.1).
Local Notation AT := (@current_homotopy_time_domain R A).
Local Notation hAT := (@current_homotopy_time_domain_open R A hInterval).
Local Notation AU := (@current_homotopy_product_domain R n A U).
Local Notation hAU := (@current_cartesian_domain_open R 1%N n AT U hAT hU).
Variable T : @current_space R h2 n U hU j.
Hypothesis hProper : @is_current_homotopy_proper R h2 n nu j A U V f g h hH.1 T.
Local Notation segment := (@current_homotopy_time_segment R A hInterval h2).
Local Notation product := (@CartesianCurrentProduct.value R h2 1%N n 1%N j AT U hAT hU segment T).

(** Source for [current_deformation_chain_support]: the original
    homotopy current is supported in h([0,1] times spt T), supporting
    the compact cone in Federer 4.1.10, p. 364. Only the original
    closed-cylinder properness is assumed. *)
Theorem current_deformation_chain_support :
  @current_support R h2 nu V hV (1+j)%N
    (@CurrentDeformationChain.value R h2 n nu j A U V f g h hH T hProper)
    `<=` h @` (@current_homotopy_closed_cylinder R h2 n nu j A U V f g h hH.1 T).
Proof.
rewrite (@current_deformation_chain_pushforward R h2 n nu j A U V f g h hH T hProper).
move=> y hy.
have [z hz <-] := @current_pushforward_support_image R h2 (1+n)%N nu (1+j)%N
  AU V hAU hV product h (@current_homotopy_image R n nu A U V f g h hH.1)
  hH.2 (@current_homotopy_product_proper R h2 n nu j A U V f g h hH.1 T hProper) y hy.
exists z; last by [].
exact: (@current_homotopy_product_support R h2 n nu j A U V f g h hH.1 T z hz).
Qed.
End CurrentDeformationChainSupport.
