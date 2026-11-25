(** Federer (1969), 4.1.10, p. 364: the three original
    current conclusions. Reuse the immediately preceding homotopy
    identity, its two degree cases and the original endpoint actions.
    The cone stays compact in the original star-shaped open sets
    by CurrentOpenConeLaws; no representation or mass premise is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentDirac CurrentCompactSmoothValue
  CurrentOpenRestriction CurrentOpenRestrictionBoundary CurrentCompactInclusionRestriction
  CurrentElementaryPushforwards CurrentAboveDimension CurrentZeroDeformation
  CurrentPushforwardSealed CurrentHomotopyUP CurrentHomotopyGeometry CurrentHomotopySliceClass
  CurrentHomotopyCylinder CurrentHomotopyCompactCylinder CurrentHomotopyEndpointProper
  CurrentHomotopyBoundaryCylinder CurrentHomotopyPositiveFormula CurrentHomotopyZeroFormula
  CurrentDeformationChainSealed CurrentConeHomotopySealed CurrentConeHomotopyClass
  CurrentAmbientCone CurrentOpenConeSealed CurrentOpenConeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section CurrentConeCurrentFormulas.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hOpen : forall x, U x -> norm_domain_interior NX U x.
Variable u : X.
Local Notation V := (fun _:X => True).
Local Notation A := (fun _:R => True).
Local Notation f := (fun _:X => u).
Local Notation g := (fun x:X => x).
Local Notation h := (@CurrentConeHomotopy.value R n u).
Local Notation hH := (@current_cone_ambient_homotopy R n u U hOpen).
Local Notation hU := (@current_homotopy_source_open R n n A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n n A U V f g h hH.1).
Local Notation endpoints := (@current_homotopy_endpoint_images R n n A U V f g h hH.1).
Local Notation classes := (@current_smooth_homotopy_endpoint_classes R n n A U V f g h hH).
Local Notation support := (fun k => @current_support R h2 n U hU k).
Local Notation dU := (fun k => @current_boundary R h2 n k U hU).
Local Notation dV := (fun k => @current_boundary R h2 n k V hV).
Local Notation restriction := (fun k => @current_open_restriction R h2 n k U V hU hV endpoints.2).

Section PositiveDegree.
Variable j : nat.
Variable T : @current_space R h2 n U hU j.+1.
Hypothesis hCompact : @compact (real_norm_metric_space hNX) (support j.+1 T).
Local Notation hProper := (@current_homotopy_compact_support_proper R h2 n n j.+1 A U V f g h hH T hCompact).
Local Notation hpF := (@current_homotopy_start_proper R h2 n n j.+1 A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n n j.+1 A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n n j.+1 U V hU hV T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n n j.+1 U V hU hV T g endpoints.2 classes.2 hpG).
Local Notation S := (@current_ambient_cone R h2 n j.+1 U hOpen u T hCompact).
Local Notation cone := (@CurrentOpenCone.value R h2 n j.+1 U hOpen u T hCompact).
Local Notation B := (dU j T).
Local Notation hpB := (@current_homotopy_boundary_cylinder_proper R h2 n n j A U V f g h hH.1 T hProper).
Local Notation boundary_chain := (@CurrentDeformationChain.value R h2 n n j A U V f g h hH B hpB).

(** Source for [current_compact_closed_cone]: a closed original
    positive-degree compact current equals the boundary of its cone,
    Federer 4.1.10, p. 364, first displayed current conclusion.
    The boundary identity holds for the restricted ambient cone on
    any open U; the original star-shaped hypothesis makes it compact. *)
Theorem current_compact_closed_cone : B=0 -> T=dU j.+1 cone.
Proof.
move=> hClosed.
have hFormula := @current_homotopy_positive_formula R h2 n n j A U V f g h hH T hProper.
change (G-F=dV j.+1 S+boundary_chain) in hFormula.
have hBoundaryZero := @current_deformation_chain_of_zero R h2 n n j A U V f g h hH B hpB hClosed.
rewrite hBoundaryZero addr0 in hFormula.
have hRestriction := congr1 (restriction j.+1) hFormula.
rewrite linearB /=
  (@current_compact_inclusion_restriction R h2 n U V hU hV endpoints.2 j.+1 T hCompact classes.2 hpG)
  (@current_compact_constant_positive_pushforward R h2 n U hU j V hV u T hCompact endpoints.1 classes.1 hpF)
  linear0 subr0 current_open_restriction_boundary
  -(@current_open_cone_restriction R h2 n j.+1 U hOpen u T hCompact) in hRestriction.
exact: hRestriction.
Qed.

(** Source for [current_compact_closed_top]: an original closed
    compact current of positive top degree n is zero, Federer
    4.1.10, p. 364, second displayed current conclusion. The cone
    has degree n+1 and vanishes by the preceding dimension theorem.
    Degree zero has its separate original formula below. *)
Theorem current_compact_closed_top : n=j.+1 -> B=0 -> T=0.
Proof.
move=> hTop hClosed.
have hDegree : (n<(1+j.+1)%N)%N by rewrite hTop ltnSn.
have hConeZero := @current_above_dimension R h2 n (1+j.+1)%N hDegree U hU cone.
have hFormula := current_compact_closed_cone hClosed.
by rewrite hConeZero linear0 in hFormula.
Qed.
End PositiveDegree.

Section DegreeZero.
Variable T : @current_space R h2 n U hU 0%N.
Hypothesis hCompact : @compact (real_norm_metric_space hNX) (support 0%N T).
Local Notation hProper := (@current_homotopy_compact_support_proper R h2 n n 0%N A U V f g h hH T hCompact).
Local Notation hpF := (@current_homotopy_start_proper R h2 n n 0%N A U V f g h hH.1 T hProper).
Local Notation hpG := (@current_homotopy_end_proper R h2 n n 0%N A U V f g h hH.1 T hProper).
Local Notation F := (@CurrentPushforward.value R h2 n n 0%N U V hU hV T f endpoints.1 classes.1 hpF).
Local Notation G := (@CurrentPushforward.value R h2 n n 0%N U V hU hV T g endpoints.2 classes.2 hpG).
Local Notation S := (@current_ambient_cone R h2 n 0%N U hOpen u T hCompact).
Local Notation cone := (@CurrentOpenCone.value R h2 n 0%N U hOpen u T hCompact).
Local Notation total := (@current_compact_total R h2 n U hU T hCompact).
Local Notation point := (@dirac_current R h2 n U hU u).

(** Source for [current_compact_zero_cone]: the exact original
    degree-zero identity T=T(1)delta_u+boundary(cone T), Federer
    4.1.10, p. 364, third displayed current conclusion. T(1) is
    the unique smooth extension on one; no negative-degree boundary
    or representation assumption is introduced, including in R^0. *)
Theorem current_compact_zero_cone : T=total*:point+dU 0%N cone.
Proof.
have hFormula := @current_homotopy_zero_formula R h2 n n A U V f g h hH T hProper.
change (G-F=dV 0%N S) in hFormula.
have hRestriction := congr1 (restriction 0%N) hFormula.
rewrite linearB /=
  (@current_compact_inclusion_restriction R h2 n U V hU hV endpoints.2 0%N T hCompact classes.2 hpG)
  (@current_compact_constant_zero_pushforward R h2 n U hU V hV u T hCompact endpoints.1 classes.1 hpF)
  linearZ /= current_open_restriction_dirac current_open_restriction_boundary
  -(@current_open_cone_restriction R h2 n 0%N U hOpen u T hCompact) in hRestriction.
have hResult := congr1 (fun Q:@current_space R h2 n U hU 0%N => Q+total*:point) hRestriction.
rewrite subrK in hResult.
by rewrite addrC in hResult.
Qed.
End DegreeZero.
End CurrentConeCurrentFormulas.
