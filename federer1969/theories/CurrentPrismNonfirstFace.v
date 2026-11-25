(** Federer (1969), 4.1.11, p. 366: apply
    the original prism recursion to every nonfirst
    source face. The existing face and tail identities
    align the compact currents; join congruence handles
    their arbitrary compactness witnesses. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces
  CurrentDirac CurrentCompactElementaryPushforwards CurrentJoinSealed CurrentJoinCongruence
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexFaceIndices CurrentSimplexPrismSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentPrismNonfirstFace.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R p).
Local Notation Full := (fun _:Y=>True).
Local Notation hFull := (fun (x:Y) (_:True)=>@norm_full_domain_interior R Y
  (inner_norm (@euclidean_inner_productP R p)) x).
Local Notation F := (fun (d:nat) (v:'I_(d.+1)->Y)=>@OrientedSimplexCurrent.value R h2 p d v).
Variables A B:X->Y.
Local Notation PSum := (fun (d:nat) (v:'I_(d.+1)->X)=>
  @current_simplex_prism_sum R h2 n p A B d v).
Local Notation hPSum := (fun (d:nat) (v:'I_(d.+1)->X)=>
  @current_simplex_prism_sum_compact R h2 n p A B d v).

(** Source for [current_prism_nonfirst_face]: a later
    source face has the same original first endpoint
    and the corresponding tail face, supporting the
    signed boundary regrouping in Federer 4.1.11,
    p. 366. No prism-current identity is assumed. *)
Theorem current_prism_nonfirst_face m (v:'I_(m.+3)->X) (k:'I_(m.+2)):
  PSum m.+1 (current_simplex_face v (lift ord0 k))=
    @CurrentJoin.value R h2 p 0%N m.+1
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (F m.+1 (fun r=>B (current_simplex_face v (lift ord0 k) r)))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (@oriented_simplex_current_compact R h2 p m.+1
        (fun r=>B (current_simplex_face v (lift ord0 k) r)))-
    @CurrentJoin.value R h2 p 0%N m.+1
      (@dirac_current R h2 p Full hFull (A (v ord0)))
      (PSum m (current_simplex_face (current_simplex_tail v) k))
      (@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I)
      (hPSum m (current_simplex_face (current_simplex_tail v) k)).
Proof.
cbn beta.
pose w:=current_simplex_face v (lift ord0 k).
pose P:=@dirac_current R h2 p Full hFull (A (w ord0)).
pose Q:=@dirac_current R h2 p Full hFull (A (v ord0)).
pose hP:=@current_compact_dirac_support R h2 p Full hFull (A (w ord0)) Logic.I.
pose hQ:=@current_compact_dirac_support R h2 p Full hFull (A (v ord0)) Logic.I.
pose T:=F m.+1 (fun r=>B (w r)).
pose hT:=@oriented_simplex_current_compact R h2 p m.+1 (fun r=>B (w r)).
pose U:=PSum m (current_simplex_tail w).
pose V:=PSum m (current_simplex_face (current_simplex_tail v) k).
pose hU:=hPSum m (current_simplex_tail w).
pose hV:=hPSum m (current_simplex_face (current_simplex_tail v) k).
have hPoint:P=Q:=congr1 (@dirac_current R h2 p Full hFull)
  (congr1 A (@current_simplex_face_head_positive X m v k)).
have hTail:U=V:=congr1 (fun s:'I_(m.+1)->X=>PSum m s)
  (@current_simplex_tail_face_positive X m v k).
have hFirst:=@current_join_current_congruence R h2 p 0%N m.+1 P Q T T
  hP hQ hT hT hPoint (erefl T).
have hSecond:=@current_join_current_congruence R h2 p 0%N m.+1 P Q U V
  hP hQ hU hV hPoint hTail.
have hRec:=@current_simplex_prism_sum_recursion R h2 n p A B m w.
exact:(eq_trans hRec (congr2 (fun S T=>S-T) hFirst hSecond)).
Qed.
End CurrentPrismNonfirstFace.
