(** Federer (1969), 4.1.13, pp. 369–370: combine the
    original homotopy identities with the preceding supported
    mass decomposition of the flat seminorm. This supporting
    statement retains a general original smooth homotopy;
    the affine mass estimate is applied separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentBoundarySupport CurrentSupportGeometry
  SmoothCompactSet CurrentPushforwardSealed CurrentHomotopyUP
  CurrentHomotopyGeometry CurrentHomotopyCylinder CurrentHomotopySliceClass
  CurrentHomotopyEndpointProper CurrentHomotopyBoundaryCylinder
  CurrentHomotopyPositiveFormula CurrentHomotopyZeroFormula
  CurrentDeformationChainSealed CurrentDeformationChainSupport
  CurrentFlatNorm CurrentFlatMassComparison CurrentFlatBoundary CurrentMassSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentHomotopyFlatBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:R_n R (1+n)%N->Y).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Local Notation endpoints := (@current_homotopy_endpoint_images R n nu A U V f g h hH.1).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n nu A U V f g h hH).
Variable K:smooth_compact_set hNY V.

Section PositiveDegree.
Variable j:nat.
Variable T:@current_space R h2 n U hU j.+1.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j.+1 A U V f g h hH.1 T.
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n nu j.+1
  A U V f g h hH.1 T).
Hypothesis hImage:h @` cylinder `<=` smooth_compact_carrier K.
Local Notation hpF := (@current_homotopy_start_proper R h2 n nu j.+1
  A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n nu j.+1
  A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV
  T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n nu j.+1 U V hU hV
  T g endpoints.2 classes.2 hpG).
Local Notation S := (@CurrentDeformationChain.value R h2 n nu j.+1
  A U V f g h hH T hProper).
Local Notation boundary := (@current_boundary R h2 n j U hU T).
Local Notation hpB := (@current_homotopy_boundary_cylinder_proper R h2 n nu j
  A U V f g h hH.1 T hProper).
Local Notation B := (@CurrentDeformationChain.value R h2 n nu j
  A U V f g h hH boundary hpB).

(** Source for [current_homotopy_positive_flat_bound]: the
    proof of Federer 4.1.13, p. 370: both original
    deformation chains are supported in C, so their masses
    bound F_C(g#T-f#T). No representation or finite-mass
    premise is needed for this supporting inequality. *)
Theorem current_homotopy_positive_flat_bound:
  (@current_flat_norm R h2 nu j.+1 V hV K (G-F)<=
    @CurrentMass.value R h2 nu j.+2 V hV S+
    @CurrentMass.value R h2 nu j.+1 V hV B)%E.
Proof.
have hS:@current_support R h2 nu V hV j.+2 S `<=` smooth_compact_carrier K.
  move=>y hy;apply:hImage.
  exact:(@current_deformation_chain_support R h2 n nu j.+1
    A U V f g h hH T hProper y hy).
have hB:@current_support R h2 nu V hV j.+1 B `<=` smooth_compact_carrier K.
  move=>y hy.
  have [z hz <-]:=@current_deformation_chain_support R h2 n nu j
    A U V f g h hH boundary hpB y hy.
  apply:hImage;exists z;last by [].
  exact:(@current_homotopy_boundary_cylinder_subset R h2 n nu j
    A U V f g h hH.1 T z hz).
have hFormula:=@current_homotopy_positive_formula R h2 n nu j
  A U V f g h hH T hProper.
have hBoundary:@current_support R h2 nu V hV j.+1
    (@current_boundary R h2 nu j.+1 V hV S) `<=` smooth_compact_carrier K.
  move=>y hy;apply:hS.
  exact:(@current_boundary_support_subset R h2 nu j.+1 V hV S y hy).
have hDifference:@current_support R h2 nu V hV j.+1 (G-F) `<=` smooth_compact_carrier K.
  rewrite hFormula.
  have hSum:=@current_support_linear_subset R h2 nu j.+1 V hV K 1
    (@current_boundary R h2 nu j.+1 V hV S) B hBoundary hB.
  by rewrite scale1r in hSum.
have hCost:=@current_flat_decomposition_lower_bound R h2 nu j.+1 V hV K
  (G-F) S hDifference hS.
have hResidual:(G-F)-@current_boundary R h2 nu j.+1 V hV S=B.
  by rewrite hFormula addrAC subrr add0r.
rewrite hResidual addeC in hCost.
exact:hCost.
Qed.
End PositiveDegree.

Section DegreeZero.
Variable T:@current_space R h2 n U hU 0%N.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu 0%N A U V f g h hH.1 T.
Local Notation cylinder := (@current_homotopy_closed_cylinder R h2 n nu 0%N
  A U V f g h hH.1 T).
Hypothesis hImage:h @` cylinder `<=` smooth_compact_carrier K.
Local Notation hpF := (@current_homotopy_start_proper R h2 n nu 0%N
  A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n nu 0%N
  A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV
  T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n nu 0%N U V hU hV
  T g endpoints.2 classes.2 hpG).
Local Notation S := (@CurrentDeformationChain.value R h2 n nu 0%N
  A U V f g h hH T hProper).

(** Source for [current_homotopy_zero_flat_bound]: the
    degree-zero case in Federer 4.1.13, pp. 369–370.
    The original difference is just the boundary of one
    deformation chain; no negative-degree boundary appears. *)
Theorem current_homotopy_zero_flat_bound:
  (@current_flat_norm R h2 nu 0%N V hV K (G-F)<=
    @CurrentMass.value R h2 nu 1%N V hV S)%E.
Proof.
rewrite (@current_homotopy_zero_formula R h2 n nu
  A U V f g h hH T hProper).
apply:(le_trans (@current_flat_boundary_bound R h2 nu 0%N V hV K S)).
apply:(@current_flat_norm_le_mass R h2 nu 1%N V hV K S)=>y hy.
apply:hImage.
exact:(@current_deformation_chain_support R h2 n nu 0%N
  A U V f g h hH T hProper y hy).
Qed.
End DegreeZero.
End CurrentHomotopyFlatBound.
