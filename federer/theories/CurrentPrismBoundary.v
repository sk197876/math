(** Federer (1969), 4.1.11, p. 366: the
    boundary of the original signed prism sum. Follow
    the printed induction, using the preceding point-join
    boundary, all simplex faces and their signed
    regrouping before compact top-degree uniqueness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDirac CurrentBoundary CurrentCompactSmoothAlgebra CurrentCompactBoundarySmooth
  CurrentCompactElementaryPushforwards CurrentDegreeTransportIdentity CurrentJoinSealed
  CurrentJoinSecondDifference CurrentJoinSecondDifferenceInput OrientedSimplexCurrentUP
  OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws CurrentSimplexPrismSum CurrentPrismFaceSum
  CurrentPrismFaceRecursion CurrentPrismBoundaryRecursion CurrentPrismBoundaryLine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPrismBoundary.
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
Local Notation Boundary := (fun d=>@current_boundary R h2 p d Full hFull).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p d w).
Variables A B:X->Y.
Local Notation PSum := (fun (d:nat) (w:'I_(d.+1)->X)=>@current_simplex_prism_sum R h2 n p A B d w).
Local Notation Faces := (fun (d:nat) (w:'I_(d.+2)->X)=>@current_prism_face_sum R h2 n p A B d w).

(** Source for [current_prism_sum_boundary]: the original
    signed prism sum has boundary the upper simplex
    minus the lower simplex minus the signed prisms
    over all source faces, supporting the inductive
    uniqueness proof in Federer 4.1.11, p. 366.
    Arbitrary endpoint maps and repeated vertices are allowed. *)
Theorem current_prism_sum_boundary m:
  forall v:'I_(m.+2)->X,Boundary m.+1 (PSum m.+1 v)=
    F m.+1 (fun r=>B (v r))-F m.+1 (fun r=>A (v r))-Faces m v.
Proof.
elim:m=>[|m ih] v;cbn beta.
- exact:(@current_prism_boundary_line R h2 n p A B v).
- pose P:=@dirac_current R h2 p Full hFull (A (v ord0)).
  pose hP:=@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I.
  pose Tail:=current_simplex_tail v.
  pose UT:=F m.+1 (fun r=>B (Tail r)).
  pose LT:=F m.+1 (fun r=>A (Tail r)).
  pose FT:=Faces m Tail.
  pose hUT:=@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (Tail r)).
  pose hLT:=@oriented_simplex_current_compact R h2 p m.+1 (fun r=>A (Tail r)).
  pose hFT:=@current_prism_face_sum_compact R h2 n p A B m Tail.
  pose PT:=PSum m.+1 Tail.
  pose hPT:=@current_simplex_prism_sum_compact R h2 n p A B m.+1 Tail.
  pose BT:=Boundary m.+1 PT.
  pose hBT:=@current_compact_boundary_compact R h2 p m.+1 Full hFull PT hPT.
  have hTail:BT=UT-LT-FT:=ih Tail.
  have hDifference:Compact m.+1 (UT-LT).
    have h:=@current_compact_linear_support R h2 p m.+1 Full hFull (-1:R) LT UT hLT hUT.
    by rewrite scaleN1r addrC in h.
  have hJoinTail:=@current_join_second_difference_input R h2 p 0%N m.+1 P hP
    (UT-LT) FT BT hDifference hFT hBT hTail.
  have hSubtract:=@current_join_second_subtract R h2 p 0%N m.+1 P hP UT LT hUT hLT hDifference.
  rewrite hSubtract in hJoinTail.
  have hLower:=@oriented_simplex_current_successor R h2 p m.+1 (fun r=>A (v r)) hP hLT.
  rewrite current_degree_transport_identity in hLower.
  have hRec:=@current_prism_sum_boundary_recursion R h2 n p A B m.+1 v.
  cbn beta in hRec.
  rewrite hJoinTail -hLower in hRec.
  have hFaces:=@current_prism_face_sum_recursion R h2 n p A B m v.
  cbn beta in hFaces.
  rewrite hRec hFaces.
  have hAlgebra (x y z u l f:C m.+2):x-y-z+(u-l-f)=x-l-(y-u+z+f).
    rewrite !opprD !opprK !addrA.
    congr (_+_).
    rewrite [x-y-z+u]addrAC [x-y+u]addrAC [x-l-y+u]addrAC [x-l+u]addrAC [LHS]addrAC.
    congr (_+_);exact:addrAC.
  exact:hAlgebra.
Qed.
End CurrentPrismBoundary.
