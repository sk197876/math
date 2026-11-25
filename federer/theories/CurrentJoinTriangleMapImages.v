(** Federer (1969), 4.1.11, p. 366: the
    two original maps f and g send the actual
    unit-square current to the same oriented triangle.
    Reuse the preceding point-segment parametrisation,
    quarter-turn square identity and cyclic orientation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  EuclideanOneCoordinate EuclideanBlockCoordinates Biorthogonal CurrentSpaces
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages SmoothFormPullbackComposition
  CurrentAmbientCartesianProduct CurrentJoinDomain CurrentJoinSourceCompact CurrentUnitSquareRotation
  CurrentTimeSquareCoordinates CurrentJoinReverseMapClass CurrentJoinAssociatorMapsSealed
  CurrentJoinTriangleMapsClass CurrentTriangleParameterImage OrientedSimplexCurrentSealed
  OrientedSimplexTriangleCycle.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinTriangleMapImages.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Local Notation e0 := (@coordinate_basis R 3%N ord0).
Local Notation e1 := (@coordinate_basis R 3%N (lift ord0 ord0)).
Local Notation e2 := (@coordinate_basis R 3%N (lift ord0 (lift ord0 ord0))).
Local Notation Triangle := (@OrientedSimplexCurrent.value R h2 3%N 2%N
  (ordinal_cons e0 (ordinal_cons e1 (fun _:'I_1=>e2)))).
Local Notation Cyclic := (@OrientedSimplexCurrent.value R h2 3%N 2%N
  (ordinal_cons e2 (ordinal_cons e0 (fun _:'I_1=>e1)))).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Local Notation f := (@CurrentJoinAssociatorMaps.left_triangle R).
Local Notation g := (@CurrentJoinAssociatorMaps.right_triangle R).
Local Notation fClass := (@current_join_left_triangle_smooth R).
Local Notation gClass := (@current_join_right_triangle_smooth R).
Local Notation Q := (@current_join_reverse_inner_map R 1%N).
Local Notation QClass := (@current_join_reverse_inner_smooth R 1%N).
Local Notation Image := (fun (p:R_n R 2%N) (_:True)=>Logic.I).
Local Notation times := (fun (s t:R)=>@euclidean_block_join R 1%N 1%N
  (@euclidean_one_embed R s,@euclidean_one_embed R t)).
Local Notation CompositeImage := (@current_smooth_composite_image R 2%N 2%N 3%N
  (Full 2%N) (Full 2%N) (Full 3%N) Q f Image Image).
Local Notation CompositeClass := (@current_smooth_composite_class R 2%N 2%N 3%N
  (Full 2%N) (Full 2%N) Q f Image QClass fClass).

(** Source for [current_join_right_triangle_coordinates]: the
    printed g parametrises delta_(v_1) join [v_2,v_3],
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_right_triangle_coordinates s t:
  g (times s t)=(1-s)*:e0+s*:((1-t)*:e1+t*:e2).
Proof.
rewrite CurrentJoinAssociatorMaps.right_triangle_laws
  current_time_square_first current_time_square_last.
by rewrite scalerDr !scalerA addrA.
Qed.

(** Source for [current_join_left_rotated_triangle_coordinates]:
    the preceding positive quarter-turn makes f the
    original parametrisation of delta_(v_3) join [v_1,v_2],
    supporting Federer 4.1.11, p. 366. *)
Lemma current_join_left_rotated_triangle_coordinates s t:
  f (Q (times s t))=(1-s)*:e2+s*:((1-t)*:e0+t*:e1).
Proof.
rewrite current_join_reverse_inner_coordinates CurrentJoinAssociatorMaps.left_triangle_laws
  current_time_square_first current_time_square_last.
have hDouble:1-(1-s)=s by rewrite opprB addrCA subrr addr0.
rewrite hDouble scalerDr !scalerA.
by rewrite [(1-t)*s]mulrC [t*s]mulrC addrC.
Qed.

(** Source for [current_join_right_triangle_image]: the
    original g#([0,1] times [0,1]) equals [v_1,v_2,v_3],
    Federer 4.1.11, p. 366. *)
Lemma current_join_right_triangle_image:
  @current_compact_map_pushforward R h2 2%N 3%N (Full 2%N) (Full 3%N)
    (hFull 2%N) (hFull 3%N) g Image gClass 2%N Square hSquare=Triangle.
Proof.
exact:(@current_triangle_parameter_image R h2 3%N e0 e1 e2 g gClass
  current_join_right_triangle_coordinates).
Qed.

(** Source for [current_join_left_triangle_image]: the
    original f square image is [v_3,v_1,v_2], hence
    [v_1,v_2,v_3] by the original even cyclic
    permutation, Federer 4.1.11, p. 366. *)
Lemma current_join_left_triangle_image:
  @current_compact_map_pushforward R h2 2%N 3%N (Full 2%N) (Full 3%N)
    (hFull 2%N) (hFull 3%N) f Image fClass 2%N Square hSquare=Triangle.
Proof.
pose Rotated:=@current_compact_map_pushforward R h2 2%N 2%N (Full 2%N) (Full 2%N)
  (hFull 2%N) (hFull 2%N) Q Image QClass 2%N Square hSquare.
pose hRotated:=@current_compact_map_image_compact R h2 2%N 2%N (Full 2%N) (Full 2%N)
  (hFull 2%N) (hFull 2%N) Q Image QClass 2%N Square hSquare.
have hQ:=@current_unit_square_rotation R h2.
have hInput:=@current_compact_map_pushforward_congruence R h2 2%N 3%N
  (Full 2%N) (Full 3%N) (hFull 2%N) (hFull 3%N) f Image fClass 2%N
  Rotated Square hRotated hSquare hQ.
have hCompose:=@current_compact_map_images_compose R h2 2%N 2%N 3%N
  (Full 2%N) (Full 2%N) (Full 3%N) (hFull 2%N) (hFull 2%N) (hFull 3%N)
  Q f Image Image QClass fClass 2%N Square hSquare hRotated.
have hTriangle:=@current_triangle_parameter_image R h2 3%N e2 e0 e1
  (fun p=>f (Q p)) CompositeClass current_join_left_rotated_triangle_coordinates.
have hMapImage:=@current_compact_map_images_agree R h2 2%N 3%N
  (Full 2%N) (Full 3%N) (hFull 2%N) (hFull 3%N) (fun p=>f (Q p)) Image CompositeClass
  2%N Square hSquare (fun p=>f (Q p)) CompositeImage CompositeClass hSquare (fun _ _=>erefl).
have hCycle:=@oriented_simplex_triangle_cycle R h2 3%N e0 e1 e2.
exact:(eq_trans (esym hInput) (eq_trans (esym hCompose)
  (eq_trans (esym hMapImage) (eq_trans hTriangle hCycle)))).
Qed.

(** Source for [current_join_triangle_images_equal]: the
    exact original equality f#([0,1] times [0,1])=
    g#([0,1] times [0,1]), Federer 4.1.11,
    p. 366, obtained through their actual common triangle. *)
Lemma current_join_triangle_images_equal:
  @current_compact_map_pushforward R h2 2%N 3%N (Full 2%N) (Full 3%N)
    (hFull 2%N) (hFull 3%N) f Image fClass 2%N Square hSquare=
  @current_compact_map_pushforward R h2 2%N 3%N (Full 2%N) (Full 3%N)
    (hFull 2%N) (hFull 3%N) g Image gClass 2%N Square hSquare.
Proof. by rewrite current_join_left_triangle_image current_join_right_triangle_image. Qed.
End CurrentJoinTriangleMapImages.
