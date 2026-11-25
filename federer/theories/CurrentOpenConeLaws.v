(** Federer (1969), 4.1.10, p. 364: the original cone
    in a star-shaped open U has compact support in the segments
    from u to spt T. All proofs use the sealed cone's independent
    test law, original restriction and the compact support criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentEvaluation CurrentSupportGeometry SmoothCompactSet
  CurrentOpenRestriction CurrentOpenRestrictionLocality CurrentHomotopyUP CurrentHomotopyGeometry
  CurrentConeHomotopySealed CurrentConeHomotopyClass CurrentAmbientCone
  CurrentConeSegmentHull CurrentOpenConeUP CurrentOpenConeSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CurrentOpenConeLaws.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n j : nat.
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
Local Notation hUV := (@current_homotopy_endpoint_images R n n A U V f g h hH.1).2.
Variable T : @current_space R h2 n U hU j.
Hypothesis hCompact : @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU j T).
Local Notation ambient := (@current_ambient_cone R h2 n j U hOpen u T hCompact).
Local Notation cone := (@CurrentOpenCone.value R h2 n j U hOpen u T hCompact).
Local Notation hull := (@current_cone_segment_hull R h2 n j U hOpen u T).

(** Source for [current_open_cone_restriction]: the original
    cone on U is the restriction of its ambient cone, supporting
    Federer 4.1.10, p. 364. This consequence uses the public
    defining action, not a private existence witness. *)
Theorem current_open_cone_restriction :
  cone=@current_open_restriction R h2 n (1+j)%N U V hU hV hUV ambient.
Proof.
apply: current_values_extensional => psi.
exact: (eq_trans (@CurrentOpenCone.laws R h2 n j U hOpen u T hCompact psi)
  (esym (@current_open_restriction_evaluation R h2 n (1+j)%N U V hU hV hUV ambient psi))).
Qed.

(** Source for [current_open_cone_support]: the original
    U-cone is supported in the compact union of its original
    segments, supporting Federer 4.1.10, p. 364. The hypothesis
    is exactly the printed star-shaped condition. *)
Theorem current_open_cone_support :
  is_current_star_shaped U u ->
  @current_support R h2 n U hU (1+j)%N cone `<=` hull.
Proof.
move=> hStar.
pose hHull := @current_cone_segment_hull_compact R h2 n j U hOpen u T hCompact.
pose KU := @Build_smooth_compact_set R X NX hNX U hull
  (@current_cone_segment_hull_in_domain R h2 n j U hOpen u T hStar) hHull.
pose KV := @Build_smooth_compact_set R X NX hNX V hull (fun _ _ => Logic.I) hHull.
apply: (current_support_compact_criterion KU cone).2 => psi hPsi.
rewrite current_open_cone_restriction current_open_restriction_evaluation.
apply: ((current_support_compact_criterion KV ambient).1
  (@current_ambient_cone_support R h2 n j U hOpen u T hCompact)).
rewrite CurrentOpenRestrictionLocality.current_open_test_extension_support.
move=> x hx; split; first by [].
exact: (hPsi x hx).2.
Qed.

(** Source for [current_open_cone_compact]: the original cone
    of a compact current on a star-shaped open U is compactly
    supported in U, supporting all three current conclusions of
    Federer 4.1.10, p. 364. No measure or finite-mass assumption is used. *)
Theorem current_open_cone_compact :
  is_current_star_shaped U u ->
  @compact (real_norm_metric_space hNX) (@current_support R h2 n U hU (1+j)%N cone).
Proof.
move=> hStar.
pose K := @Build_smooth_compact_set R X NX hNX U hull
  (@current_cone_segment_hull_in_domain R h2 n j U hOpen u T hStar)
  (@current_cone_segment_hull_compact R h2 n j U hOpen u T hCompact).
exact: (@current_support_compact_bound R h2 n (1+j)%N U hU K cone
  (current_open_cone_support hStar)).
Qed.
End CurrentOpenConeLaws.
