(** Federer (1969), 4.1.11, p. 366: the
    original common-current image acts on the square
    factor and retains all three arbitrary spatial
    currents. Reuse the preceding exact image equations
    in the two Cartesian factors. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentDegreeTransportIdentity CurrentCompactPushforwardAlgebra CurrentCompactPushforwardImages
  CurrentAmbientCartesianProduct CurrentAmbientFirstImageEquation CurrentAmbientProductImageEquation
  CurrentCartesianMapClass CurrentJoinSliceMapClass CurrentJoinDomain CurrentJoinSourceCompact
  CurrentJoinAssociativitySquareSlot.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentJoinAssociativitySlotImage.
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
Variable h:R_n R 2%N->R_n R 3%N.
Hypothesis hh:norm_class_all_orders (inner_norm_real_norm (@euclidean_inner_productP R 2%N))
  (inner_norm_real_norm (@euclidean_inner_productP R 3%N)) (Full 2%N) h.
Local Notation HImage := (fun (x:R_n R 2%N) (_:True)=>Logic.I).
Local Notation W := (@current_compact_map_pushforward R h2 2%N 3%N
  (Full 2%N) (Full 3%N) (hFull 2%N) (hFull 3%N) h HImage hh 2%N Square hSquare).
Local Notation hW := (@current_compact_map_image_compact R h2 2%N 3%N
  (Full 2%N) (Full 3%N) (hFull 2%N) (hFull 3%N) h HImage hh 2%N Square hSquare).
Local Notation InnerTarget := (@current_ambient_cartesian_product R h2 3%N n 2%N k W T).
Local Notation hInnerTarget := (@current_ambient_cartesian_product_compact R h2 3%N n 2%N k W T hW hT).
Local Notation MiddleTarget := (@current_ambient_cartesian_product R h2 n (3+n)%N j (2+k)%N S InnerTarget).
Local Notation hMiddleTarget := (@current_ambient_cartesian_product_compact R h2 n (3+n)%N j (2+k)%N
  S InnerTarget hS hInnerTarget).
Local Notation Target := (@current_ambient_cartesian_product R h2 n (n+(3+n))%N i (j+(2+k))%N P MiddleTarget).
Local Notation Id := (fun x:R_n R n=>x).
Local Notation IdClass := (@current_join_slice_identity_smooth R n).
Local Notation InnerMap := (@current_join_assoc_square_inner R n h).
Local Notation InnerClass := (@current_join_assoc_square_inner_smooth R n h hh).
Local Notation MiddleMap := (@current_join_assoc_square_middle R n h).
Local Notation MiddleClass := (@current_join_assoc_square_middle_smooth R n h hh).
Local Notation Slot := (@current_join_assoc_square_slot R n h).
Local Notation SlotClass := (@current_join_assoc_square_slot_smooth R n h hh).
Local Notation Image := (fun (x:R_n R (n+(n+(2+n)))%N) (_:True)=>Logic.I).

(** Source for [current_join_assoc_square_slot_image]: the
    original common-current image is R times (S times
    (h#square times T)), supporting the f/g comparison
    in Federer 4.1.11, p. 366. All three spatial
    currents remain arbitrary and compact; only the
    given square map is assumed smooth. *)
Lemma current_join_assoc_square_slot_image:
  @current_compact_map_pushforward R h2 (n+(n+(2+n)))%N (n+(n+(3+n)))%N
    (Full (n+(n+(2+n)))%N) (Full (n+(n+(3+n)))%N)
    (hFull (n+(n+(2+n)))%N) (hFull (n+(n+(3+n)))%N)
    Slot Image SlotClass (i+(j+(2+k)))%N Common hCommon=Target.
Proof.
have hBase:=esym (scale1r W).
have hInner:=@current_ambient_product_first_image_equation R h2 2%N 3%N n h hh
  2%N k Square T hSquare hT 2%N (erefl 2%N) (1:R) W hW hBase.
rewrite current_degree_transport_identity scale1r in hInner.
have hInnerClass:(@current_cartesian_map_smooth R 2%N n 3%N n h Id hh IdClass)=InnerClass:=Prop_irrelevance _ _.
rewrite hInnerClass in hInner.
have hInnerCoefficient:=eq_trans hInner (esym (scale1r InnerTarget)).
have hMiddle:=@current_ambient_product_second_image_equation R h2 n (2+n)%N (3+n)%N
  InnerMap InnerClass j (2+k)%N S SquareT hS hSquareT (2+k)%N (erefl (2+k)%N)
  (1:R) InnerTarget hInnerTarget hInnerCoefficient.
rewrite current_degree_transport_identity scale1r in hMiddle.
have hMiddleClass:(@current_cartesian_map_smooth R n (2+n)%N n (3+n)%N
  Id InnerMap IdClass InnerClass)=MiddleClass:=Prop_irrelevance _ _.
rewrite hMiddleClass in hMiddle.
have hMiddleCoefficient:=eq_trans hMiddle (esym (scale1r MiddleTarget)).
have hOuter:=@current_ambient_product_second_image_equation R h2 n (n+(2+n))%N (n+(3+n))%N
  MiddleMap MiddleClass i (j+(2+k))%N P InnerSource hP hInnerSource
  (j+(2+k))%N (erefl (j+(2+k))%N) (1:R) MiddleTarget hMiddleTarget hMiddleCoefficient.
rewrite current_degree_transport_identity scale1r in hOuter.
have hSlotClass:(@current_cartesian_map_smooth R n (n+(2+n))%N n (n+(3+n))%N
  Id MiddleMap IdClass MiddleClass)=SlotClass:=Prop_irrelevance _ _.
by rewrite hSlotClass in hOuter.
Qed.
End CurrentJoinAssociativitySlotImage.
