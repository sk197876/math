(** Actual-space endpoint checks for Federer (1969),
    4.1.16, pp. 373–374: the nearest map on the
    full, possibly unbounded Euclidean space, the empty
    support of the actual zero current, and the nonzero
    R^0 Dirac current with convex-hull flat norm one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric InnerConvex HilbertFormCompactness NormMetric
  NormOpenDomainLaws NormDifferentialUP SmoothCompactSet CurrentSpaces
  CurrentDirac CurrentSupportExtensionality CurrentFlatNorm
  FlatCurrentsUP FlatCurrentUnion EuclideanConvexNearestMapSealed
  EuclideanConvexNearestMapLaws EuclideanFlatConvexHullIndex EuclideanFlatConvexHull.
From FedererTests Require Import FlatCurrentEndpointExamples AffineCurrentEndpointExamples.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section ConvexNearestFullEndpoint.
Variable R : realType.
Variable n : nat.
Local Notation X := (R_n R n).
Local Notation hB := (@euclidean_inner_productP R n).
Local Notation IT := (inner_metric_space hB).
Local Notation C := (setT : set IT).
(** Source for [nearest_full_closed]: the full Euclidean
    space is a closed choice of C in the nearest-map
    endpoint regression for Federer 4.1.16, p. 373. *)
Local Lemma nearest_full_closed : closed C.
Proof. exact: closedT. Qed.
(** Source for [nearest_full_nonempty]: zero supplies a
    point of the full Euclidean C in the nearest-map
    regression for Federer 4.1.16, p. 373, including n=0. *)
Local Lemma nearest_full_nonempty : C !=set0.
Proof. exists (0:X); by []. Qed.
(** Source for [nearest_full_convex]: the full Euclidean
    C is convex, supporting the actual nearest-map
    endpoint regression for Federer 4.1.16, p. 373. *)
Local Lemma nearest_full_convex : is_inner_convex C.
Proof. by move=> x y _ _ t _ _. Qed.

(** Source for [convex_nearest_full_space_identity]: the
    actual opaque map of the original nearest relation
    fixes every point of C, Federer 4.1.16, p. 373.
    Taking C=R^n permits unbounded C and also n=0;
    no compactness restriction is hidden in the map API. *)
Example convex_nearest_full_space_identity :
  @EuclideanConvexNearestMap.value R n C nearest_full_closed
    nearest_full_nonempty nearest_full_convex=(fun x:X=>x).
Proof.
apply: funext=> x.
exact: (@euclidean_convex_nearest_map_fixed R n C
  (@EuclideanConvexNearestMap.value R n C nearest_full_closed
    nearest_full_nonempty nearest_full_convex)
  (@EuclideanConvexNearestMap.laws R n C nearest_full_closed
    nearest_full_nonempty nearest_full_convex) x Logic.I).
Qed.
End ConvexNearestFullEndpoint.

Section ConvexZeroCurrentEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation U := (fun _:X=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior N x).
Local Notation T := (0 : @current_space R h2 n U hU m).
Local Notation hFlat := (@flat_current_zero R h2 n m U hU).
Local Notation C := (@current_flat_convex_hull_index R h2 n m hU T hFlat).

(** Source for [convex_flat_zero_empty_hull]: the full
    flat-current conclusion of 4.1.16, p. 374, applied
    to the actual zero current with empty convex hull.
    The final theorem supplies its membership and every
    compact-index equality, without selecting a nearest point
    of an empty set. All n and m are retained. *)
Example convex_flat_zero_empty_hull :
  smooth_compact_carrier C=set0 /\
  @is_flat_current_supported_in R h2 n m U hU C T /\
  forall K:smooth_compact_set hN U,
    @current_flat_norm R h2 n m U hU K T=
      @current_flat_norm R h2 n m U hU C T.
Proof.
have hEmptySupport := (@current_empty_support_iff_zero R h2 n m U hU T).2 (erefl T).
have hEmpty := (@current_flat_convex_hull_index_empty R h2 n m hU T hFlat
  hEmptySupport).2.
have [hMember hNorm] := @federer_4_1_16 R h2 n m hU T hFlat.
split; first exact: hEmpty.
split; first exact: hMember.
move=> K; apply: hNorm.
by rewrite hEmpty; move=> x [].
Qed.
End ConvexZeroCurrentEndpoint.

Section ConvexNonzeroPointEndpoint.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Local Notation X := (R_n R 0%N).
Local Notation N := (inner_norm (@euclidean_inner_productP R 0%N)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R 0%N)).
Local Notation U := (fun _:X=>True).
Local Notation hU := (fun (x:X) (_:True)=>norm_full_domain_interior N x).
Local Notation T := (@dirac_current R h2 0%N U hU (0:X)).
Local Notation K := (@flat_point_singleton_index R).
(** Source for [convex_point_flat]: reuse the proved
    actual R^0 flat point current from 4.1.12, p. 368,
    for the convex-hull regression of 4.1.16, p. 374. *)
Local Lemma convex_point_flat : @is_flat_current R h2 0%N 0%N U hU T.
Proof. exists K; exact: (@zero_dimensional_point_flat R h2). Qed.
Local Notation C := (@current_flat_convex_hull_index R h2 0%N 0%N hU T convex_point_flat).

(** Source for [convex_flat_nonzero_zero_dimensional_point]:
    the original flat and exact-norm conclusions of
    Federer 4.1.16, p. 374, preserve the nonzero
    degree-zero Dirac current in R^0. The actual
    convex-hull flat norm remains one. *)
Example convex_flat_nonzero_zero_dimensional_point :
  T<>0 /\ @is_flat_current_supported_in R h2 0%N 0%N U hU C T /\
  @current_flat_norm R h2 0%N 0%N U hU C T= 1%:E.
Proof.
have hCK : smooth_compact_carrier C `<=` smooth_compact_carrier K.
  move=> x _; change (x=0).
  apply/ffunP=> i; by have := ltn_ord i; rewrite ltn0.
have [hMember hNorm] := @federer_4_1_16 R h2 0%N 0%N hU T convex_point_flat.
split; first exact: (@affine_zero_dimensional_point_nonzero R h2).
split; first exact: hMember.
have h := hNorm K hCK.
rewrite (@zero_dimensional_point_flat_norm_one R h2) in h.
exact: esym h.
Qed.
End ConvexNonzeroPointEndpoint.
