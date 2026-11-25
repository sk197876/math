(** Federer (1969), 4.1.11, p. 365: each nonfirst
    face is the join of the original first point with
    its corresponding tail face. This is the original
    simplex recursion and finite deletion bookkeeping,
    before using any boundary or permutation theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransportIdentity CurrentCompactElementaryPushforwards
  CurrentJoinSealed CurrentJoinCongruence OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexFaceIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentNonfirstFace.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->X)=>@OrientedSimplexCurrent.value R h2 n d w).
Variable v:'I_(m.+3)->X.
Variable k:'I_(m.+2).
Local Notation P := (@dirac_current R h2 n Full hFull (v ord0)).
Local Notation hP := (@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I).
Local Notation Q := (F m (current_simplex_face (current_simplex_tail v) k)).
Local Notation hQ := (@oriented_simplex_current_compact R h2 n m
  (current_simplex_face (current_simplex_tail v) k)).

(** Source for [oriented_simplex_current_nonfirst_face]:
    deleting a later vertex leaves the original first
    point joined with the matching tail face, supporting
    the original boundary sum in Federer 4.1.11, p. 365. *)
Theorem oriented_simplex_current_nonfirst_face:
  F m.+1 (current_simplex_face v (lift ord0 k))=
    @CurrentJoin.value R h2 n 0%N m P Q hP hQ.
Proof.
pose w:=current_simplex_face v (lift ord0 k).
pose P':=@dirac_current R h2 n Full hFull (w ord0).
pose hP':=@current_compact_dirac_support R h2 n Full hFull (w ord0) Logic.I.
pose Q':=F m (current_simplex_tail w).
pose hQ':=@oriented_simplex_current_compact R h2 n m (current_simplex_tail w).
have hRec:=@oriented_simplex_current_successor R h2 n m w hP' hQ'.
rewrite current_degree_transport_identity in hRec.
have hPoint:P' = P:=congr1 (@dirac_current R h2 n Full hFull)
  (@current_simplex_face_head_positive X m v k).
have hTail:Q'=Q:=congr1 (fun s:'I_(m.+1)->X=>F m s)
  (@current_simplex_tail_face_positive X m v k).
have hJoin:=@current_join_current_congruence R h2 n 0%N m P' P Q' Q hP' hP hQ' hQ hPoint hTail.
exact:(eq_trans hRec hJoin).
Qed.
End OrientedSimplexCurrentNonfirstFace.
