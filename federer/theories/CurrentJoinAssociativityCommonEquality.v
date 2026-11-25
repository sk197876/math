(** Federer (1969), 4.1.11, p. 366: the
    two original square images remain equal beside
    all three spatial currents, and after the original
    H image. Use actual compact images throughout. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages CurrentAmbientCartesianProduct
  CurrentJoinDomain CurrentJoinSourceCompact CurrentJoinAssociatorMapsSealed CurrentJoinTriangleMapsClass
  CurrentJoinTriangleMapImages CurrentJoinAssociativitySquareSlot CurrentJoinAssociativitySlotImage
  CurrentJoinAssociativityCommonMap SmoothFormPullbackComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentJoinAssociativityCommonEquality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n i j k:nat.
Local Notation Full := (fun d:nat=>fun _:R_n R d=>True).
Local Notation hFull := (fun (d:nat) (x:R_n R d) (_:True)=>
  @norm_full_domain_interior R (R_n R d) (inner_norm (@euclidean_inner_productP R d)) x).
Variables (P:@current_space R h2 n (Full n) (hFull n) i)
  (S:@current_space R h2 n (Full n) (hFull n) j)
  (T:@current_space R h2 n (Full n) (hFull n) k).
Hypothesis hP:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) i P).
Hypothesis hS:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) j S).
Hypothesis hT:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n (Full n) (hFull n) k T).
Local Notation I := (@current_join_time_segment R h2).
Local Notation hI := (@current_join_time_segment_compact R h2).
Local Notation Square := (@current_ambient_cartesian_product R h2 1%N 1%N 1%N 1%N I I).
Local Notation hSquare := (@current_ambient_cartesian_product_compact R h2 1%N 1%N 1%N 1%N I I hI hI).
Local Notation SquareT := (@current_ambient_cartesian_product R h2 2%N n 2%N k Square T).
Local Notation hSquareT := (@current_ambient_cartesian_product_compact R h2 2%N n 2%N k Square T hSquare hT).
Local Notation InnerSource := (@current_ambient_cartesian_product R h2 n (2+n)%N j (2+k)%N S SquareT).
Local Notation hInnerSource := (@current_ambient_cartesian_product_compact R h2 n (2+n)%N j (2+k)%N S SquareT hS hSquareT).
Local Notation Common := (@current_ambient_cartesian_product R h2 n (n+(2+n))%N i (j+(2+k))%N P InnerSource).
Local Notation hCommon := (@current_ambient_cartesian_product_compact R h2 n (n+(2+n))%N i (j+(2+k))%N P InnerSource hP hInnerSource).
Local Notation SquareImage := (fun (f:R_n R 2%N->R_n R 3%N) hf=>
  @current_compact_map_pushforward R h2 2%N 3%N (Full 2%N) (Full 3%N)
    (hFull 2%N) (hFull 3%N) f (fun _ _=>Logic.I) hf 2%N Square hSquare).
Local Notation Slot := (@current_join_assoc_square_slot R n).
Local Notation SlotClass := (fun (f0:R_n R 2%N->R_n R 3%N)
  (hf0:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
    (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (Full 2%N) f0)=>
  @current_join_assoc_square_slot_smooth R n f0 hf0).
Local Notation Image := (fun (x:R_n R (n+(n+(2+n)))%N) (_:True)=>Logic.I).
Local Notation SlotImage := (fun (f:R_n R 2%N->R_n R 3%N) hf=>
  @current_compact_map_pushforward R h2 (n+(n+(2+n)))%N (n+(n+(3+n)))%N
    (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N)
    (hFull (n+(n+(2+n)))%N) (hFull (n+(n+(3+n)))%N)
    (Slot f) Image (SlotClass f hf) (i+(j+(2+k)))%N Common hCommon).
Local Notation hSlotImage := (fun (f:R_n R 2%N->R_n R 3%N) hf=>
  @current_compact_map_image_compact R h2 (n+(n+(2+n)))%N (n+(n+(3+n)))%N
    (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N)
    (hFull (n+(n+(2+n)))%N) (hFull (n+(n+(3+n)))%N)
    (Slot f) Image (SlotClass f hf) (i+(j+(2+k)))%N Common hCommon).

(** Source for [current_join_assoc_square_slot_congruence]: equal
    original square images have equal common-current
    images beside all three spatial factors, supporting
    Federer 4.1.11, p. 366. *)
Lemma current_join_assoc_square_slot_congruence (f g:R_n R 2%N->R_n R 3%N)
    (hf:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
      (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (Full 2%N) f)
    (hg:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
      (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (Full 2%N) g):
  SquareImage f hf=SquareImage g hg->SlotImage f hf=SlotImage g hg.
Proof.
move=>hEqual.
have hFirst:=@current_join_assoc_square_slot_image R h2 n i j k P S T hP hS hT f hf.
have hSecond:=@current_join_assoc_square_slot_image R h2 n i j k P S T hP hS hT g hg.
by rewrite hFirst hSecond hEqual.
Qed.

Local Notation f := (@CurrentJoinAssociatorMaps.left_triangle R).
Local Notation g := (@CurrentJoinAssociatorMaps.right_triangle R).
Local Notation hf := (@current_join_left_triangle_smooth R).
Local Notation hg := (@current_join_right_triangle_smooth R).
Local Notation H := (@current_join_assoc_weighted_map R n).
Local Notation hH := (@current_join_assoc_weighted_map_smooth R n).
Local Notation HImage := (fun (x:R_n R (n+(n+(3+n)))%N) (_:True)=>Logic.I).
Local Notation CompositeImage := (fun (f0:R_n R 2%N->R_n R 3%N)=>
  @current_smooth_composite_image R (n+(n+(2+n)))%N (n+(n+(3+n)))%N n
    (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N) (Full n) (Slot f0) H Image HImage).
Local Notation CompositeClass := (fun (f0:R_n R 2%N->R_n R 3%N) hf0=>
  @current_smooth_composite_class R (n+(n+(2+n)))%N (n+(n+(3+n)))%N n
    (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N) (Slot f0) H Image (SlotClass f0 hf0) hH).

(** Source for [current_join_assoc_common_composite_equality]: the
    original H images of the f and g common-current
    images coincide, supporting the arbitrary-current
    associativity proof in Federer 4.1.11, p. 366.
    This follows from the actual common triangle,
    without any representation premise on R,S,T. *)
Lemma current_join_assoc_common_composite_equality:
  @current_compact_map_pushforward R h2 (n+(n+(2+n)))%N n
    (Full (n+(n+(2+n)))%N) (Full n) (hFull (n+(n+(2+n)))%N) (hFull n)
    (fun x=>H (Slot f x)) (CompositeImage f) (CompositeClass f hf)
    (i+(j+(2+k)))%N Common hCommon=
  @current_compact_map_pushforward R h2 (n+(n+(2+n)))%N n
    (Full (n+(n+(2+n)))%N) (Full n) (hFull (n+(n+(2+n)))%N) (hFull n)
    (fun x=>H (Slot g x)) (CompositeImage g) (CompositeClass g hg)
    (i+(j+(2+k)))%N Common hCommon.
Proof.
have hEqual:=@current_join_assoc_square_slot_congruence f g hf hg
  (@current_join_triangle_images_equal R h2).
have hFirst:=@current_compact_map_images_compose R h2 (n+(n+(2+n)))%N (n+(n+(3+n)))%N n
  (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N) (Full n)
  (hFull (n+(n+(2+n)))%N) (hFull (n+(n+(3+n)))%N) (hFull n)
  (Slot f) H Image HImage (SlotClass f hf) hH (i+(j+(2+k)))%N Common hCommon (hSlotImage f hf).
have hSecond:=@current_compact_map_images_compose R h2 (n+(n+(2+n)))%N (n+(n+(3+n)))%N n
  (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N) (Full n)
  (hFull (n+(n+(2+n)))%N) (hFull (n+(n+(3+n)))%N) (hFull n)
  (Slot g) H Image HImage (SlotClass g hg) hH (i+(j+(2+k)))%N Common hCommon (hSlotImage g hg).
have hCompare:=@current_compact_map_pushforward_congruence R h2 (n+(n+(3+n)))%N n
  (Full (n+(n+(3+n)))%N) (Full n) (hFull (n+(n+(3+n)))%N) (hFull n)
  H HImage hH (i+(j+(2+k)))%N (SlotImage f hf) (SlotImage g hg)
  (hSlotImage f hf) (hSlotImage g hg) hEqual.
exact:(eq_trans hFirst (eq_trans hCompare (esym hSecond))).
Qed.
End CurrentJoinAssociativityCommonEquality.
