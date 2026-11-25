(** Federer (1969), 4.1.11, p. 366: regroup
    the original prisms over all source faces. Reuse
    the preceding full simplex boundary, ordered face
    identities and finite point-join linearity. This is
    the algebraic cancellation in the printed induction. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDirac CurrentBoundary CurrentCompactBoundarySmooth CurrentCompactElementaryPushforwards
  CurrentCompactFiniteSum CurrentJoinSealed CurrentJoinCongruence CurrentJoinFiniteLinearity
  CurrentJoinSecondDifference OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexNonfirstBoundary CurrentSimplexPrismSum
  CurrentPrismNonfirstFace CurrentPrismFaceSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismFaceRecursion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation C := (fun d=>@current_space R h2 p Full hFull d).
Local Notation Compact := (fun d (T:C d)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R p)))
  (@current_support R h2 p Full hFull d T)).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p d w).
Local Notation Boundary := (fun d=>@current_boundary R h2 p d Full hFull).
Variables A B:X->Y.
Local Notation PSum := (fun (d:nat) (w:'I_(d.+1)->X)=>@current_simplex_prism_sum R h2 n p A B d w).
Local Notation Faces := (fun (d:nat) (w:'I_(d.+2)->X)=>@current_prism_face_sum R h2 n p A B d w).
Variable m:nat.
Variable v:'I_(m.+3)->X.
Local Notation P := (@dirac_current R h2 p Full hFull (A (v ord0))).
Local Notation hP := (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I).
Local Notation UT := (F m.+1 (fun r=>B (current_simplex_tail v r))).
Local Notation hUT := (@oriented_simplex_current_compact R h2 p m.+1
  (fun r=>B (current_simplex_tail v r))).
Local Notation UV := (F m.+2 (fun r=>B (v r))).
Local Notation hUV := (@oriented_simplex_current_compact R h2 p m.+2 (fun r=>B (v r))).
Local Notation BV := (Boundary m.+1 UV).
Local Notation hBV := (@current_compact_boundary_compact R h2 p m.+1 Full hFull UV hUV).
Local Notation FT := (Faces m (current_simplex_tail v)).
Local Notation hFT := (@current_prism_face_sum_compact R h2 n p A B m (current_simplex_tail v)).
Local Notation J := (fun (T:C m.+1) (hT:Compact m.+1 T)=>@CurrentJoin.value R h2 p 0%N m.+1 P T hP hT).

(** Source for [current_prism_face_sum_recursion]: the
    original signed face-prism sum is the tail prism,
    minus the first point joined with the upper tail,
    plus that point joined with the upper boundary
    and with the tail face-prism sum. This is the
    original boundary regrouping in Federer 4.1.11,
    p. 366, before using any top-degree uniqueness. *)
Theorem current_prism_face_sum_recursion:
  Faces m.+1 v=PSum m.+1 (current_simplex_tail v)-J UT hUT+J BV hBV+J FT hFT.
Proof.
cbn beta.
pose T:=fun k:'I_(m.+2)=>F m.+1 (fun r=>B (current_simplex_face v (lift ord0 k) r)).
pose U:=fun k:'I_(m.+2)=>PSum m (current_simplex_face (current_simplex_tail v) k).
pose a:=fun k:'I_(m.+2)=>(-1:R)^+k.
pose hT:=fun k:'I_(m.+2)=>@oriented_simplex_current_compact R h2 p m.+1
  (fun r=>B (current_simplex_face v (lift ord0 k) r)).
pose hU:=fun k:'I_(m.+2)=>@current_simplex_prism_sum_compact R h2 n p A B m
  (current_simplex_face (current_simplex_tail v) k).
pose VSum:=\sum_k a k*:T k.
pose hVSum:=@current_compact_weighted_finite_sum R h2 p m.+1 Full hFull m.+2 a T hT.
have hJoinT:=@current_join_second_weighted_sum R h2 p 0%N m.+1 P hP m.+2 a T hT hVSum.
have hJoinU:=@current_join_second_weighted_sum R h2 p 0%N m.+1 P hP m.+2 a U hU hFT.
have hRest:(\sum_(k<m.+2) (-1:R)^+(lift ord0 k:nat)*:
    PSum m.+1 (current_simplex_face v (lift ord0 k)))=
    -(\sum_k a k*:J (T k) (hT k))+(\sum_k a k*:J (U k) (hU k)).
  rewrite -sumrN -big_split;apply:eq_bigr=>k _.
  rewrite (@current_prism_nonfirst_face R h2 n p A B m v k)
    lift0 exprS mulN1r scaleNr scalerBr opprB.
  exact:addrC.
cbn beta in hRest.
have hFaces:Faces m.+1 v=PSum m.+1 (current_simplex_tail v)-J VSum hVSum+J FT hFT.
  rewrite /current_prism_face_sum big_ord_recl expr0 scale1r.
  cbn beta.
  by rewrite hRest -hJoinT -hJoinU addrA.
have hUpper:=@oriented_simplex_nonfirst_boundary_sum R h2 p m.+1 (fun r=>B (v r)).
change (VSum=UT-BV) in hUpper.
have hDifference:Compact m.+1 (UT-BV) by rewrite -hUpper;exact:hVSum.
have hInput:=@current_join_current_congruence R h2 p 0%N m.+1 P P VSum (UT-BV)
  hP hP hVSum hDifference (erefl P) hUpper.
have hSubtract:=@current_join_second_subtract R h2 p 0%N m.+1 P hP UT BV hUT hBV hDifference.
have hJUpper:J VSum hVSum=J UT hUT-J BV hBV:=eq_trans hInput hSubtract.
have hReorder (s t u:C m.+2):s-(t-u)=s-t+u.
  by rewrite opprB addrA addrAC.
cbn beta in hFaces.
cbn beta in hJUpper.
by rewrite hFaces hJUpper hReorder.
Qed.
End CurrentPrismFaceRecursion.
