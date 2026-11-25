(** Federer (1969), 4.1.11, p. 366: reversing the
    first pair reverses the oriented simplex. Follow
    Federer's lower-face cancellation and the preceding
    compact top-degree uniqueness of 4.1.10, p. 364.
    The one-dimensional case is the existing segment reversal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentCompactCurrentArithmetic CurrentCompactTopUniqueness
  OrientedSegmentCurrentReversal OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentLowDegrees OrientedSimplexCurrentBoundary
  CurrentSimplexFirstSwap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexFirstSwapBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->X)=>@OrientedSimplexCurrent.value R h2 n d w).
Local Notation Boundary := (fun d=>@current_boundary R h2 n d Full hFull).

(** Source for [oriented_simplex_first_swap_pair]: the
    original [u_1,u_0]=-[u_0,u_1], Federer 4.1.11,
    p. 366, by the segment reversal of 4.1.8, p. 362.
    Repeated points and dimension zero are included. *)
Theorem oriented_simplex_first_swap_pair (v:'I_2->X):
  F 1%N (current_simplex_first_swap v)= -F 1%N v.
Proof.
cbn beta.
pose hSegment:=fun (t:R) (_:t \in `[0,1])=>Logic.I.
rewrite (@oriented_simplex_current_segment R h2 n (current_simplex_first_swap v) hSegment)
  (@oriented_simplex_current_segment R h2 n v hSegment)
  current_simplex_first_swap_head current_simplex_first_swap_second.
exact:(@oriented_segment_current_reversal R h2 n Full hFull
  (v ord0) (v (lift ord0 ord0)) hSegment hSegment).
Qed.

(** Source for [oriented_simplex_current_boundary_first_two]:
    separate the first two faces from the already proved
    original boundary sum, supporting the cancellation in
    Federer 4.1.11, p. 366. No orientation law is used. *)
Theorem oriented_simplex_current_boundary_first_two m (v:'I_(m.+3)->X):
  Boundary m.+1 (F m.+2 v)=
    F m.+1 (current_simplex_face v ord0)-F m.+1 (current_simplex_face v (lift ord0 ord0))+
    \sum_(k:'I_(m.+1)) (-1:R)^+(k:nat).+2*:
      F m.+1 (current_simplex_face v (lift ord0 (lift ord0 k))).
Proof.
cbn beta.
by rewrite oriented_simplex_current_boundary big_ord_recl big_ord_recl
  !lift0 expr0 expr1 scale1r scaleN1r addrA.
Qed.

Variable m:nat.
Hypothesis hPrevious:forall p (w:'I_(m.+2)->R_n R p),
  @OrientedSimplexCurrent.value R h2 p m.+1 (current_simplex_first_swap w)=
    -@OrientedSimplexCurrent.value R h2 p m.+1 w.
Arguments hPrevious : clear implicits.

(** Source for [oriented_simplex_first_swap_boundary]:
    the exchanged simplex has the negative original
    boundary by the preceding lower-dimensional reversal,
    supporting Federer's induction in 4.1.11, p. 366. *)
Theorem oriented_simplex_first_swap_boundary (v:'I_(m.+3)->X):
  Boundary m.+1 (F m.+2 (current_simplex_first_swap v))= -Boundary m.+1 (F m.+2 v).
Proof.
cbn beta.
rewrite !oriented_simplex_current_boundary_first_two
  current_simplex_first_swap_face_zero current_simplex_first_swap_face_one.
have hRest:(\sum_(k:'I_(m.+1)) (-1:R)^+(k:nat).+2*:
    F m.+1 (current_simplex_face (current_simplex_first_swap v) (lift ord0 (lift ord0 k))))=
    -(\sum_(k:'I_(m.+1)) (-1:R)^+(k:nat).+2*:
      F m.+1 (current_simplex_face v (lift ord0 (lift ord0 k)))).
  rewrite -sumrN;apply:eq_bigr=>k _.
  by rewrite current_simplex_first_swap_later_face (hPrevious n _) scalerN.
cbn beta in hRest.
by rewrite hRest opprD opprB.
Qed.

(** Source for [oriented_simplex_first_swap_top]: the
    original reversed top-dimensional simplex is the
    negative simplex because their boundaries agree,
    Federer 4.1.11, p. 366, using the compact
    closed-current theorem of 4.1.10, p. 364. *)
Theorem oriented_simplex_first_swap_top (hDimension:n=m.+2) (v:'I_(m.+3)->X):
  F m.+2 (current_simplex_first_swap v)= -F m.+2 v.
Proof.
pose S:=F m.+2 v.
pose hS:=@oriented_simplex_current_compact R h2 n m.+2 v.
have hNegative:@compact (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    (@current_support R h2 n Full hFull m.+2 (-S)).
  have h:=@current_compact_scaled_support R h2 n m.+2 Full hFull S (-1:R) hS.
  by rewrite scaleN1r in h.
apply:(@current_compact_top_boundary_unique R h2 n m.+1 Full hFull
  (F m.+2 (current_simplex_first_swap v)) (-S)
  (@oriented_simplex_current_compact R h2 n m.+2 (current_simplex_first_swap v)) hNegative hDimension).
rewrite linearN.
exact:oriented_simplex_first_swap_boundary.
Qed.
End OrientedSimplexFirstSwapBoundary.
