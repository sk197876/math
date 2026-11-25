(** Federer (1969), 4.1.11, p. 365: the original
    boundary of [u_0,...,u_m] is the alternating sum
    of all its ordered faces. Follow the printed induction:
    the point-join boundary rule, the preceding tail boundary,
    and linearity give the full face sum. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentBoundary CurrentCompactBoundarySmooth CurrentCompactElementaryPushforwards
  CurrentCompactFiniteSum CurrentJoinSealed CurrentJoinCongruence CurrentJoinFiniteLinearity
  OrientedSimplexCurrentUP OrientedSimplexCurrentSealed OrientedSimplexCurrentLaws
  OrientedSimplexFaceIndices OrientedSimplexCurrentNonfirstFace OrientedSimplexCurrentBoundaryRecursion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentBoundary.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (d:nat) (w:'I_(d.+1)->X)=>@OrientedSimplexCurrent.value R h2 n d w).
Local Notation Boundary := (fun d=>@current_boundary R h2 n d Full hFull).

(** Source for [oriented_simplex_current_boundary]: the
    original identity boundary [u_0,...,u_m] equals
    sum_k (-1)^k [u_0,...,omit u_k,...,u_m], Federer
    4.1.11, p. 365. Every positive degree, repeated
    vertex and ambient dimension is retained. *)
Theorem oriented_simplex_current_boundary m (v:'I_(m.+2)->X):
  Boundary m (F m.+1 v)=\sum_(k:'I_(m.+2)) (-1:R)^+(k:nat)*:F m (current_simplex_face v k).
Proof.
elim:m v=>[|m ih] v;cbn beta.
- rewrite oriented_simplex_current_boundary_segment big_ord_recl big_ord1
    lift0 expr0 expr1 scale1r scaleN1r.
  have hLast:(lift ord0 (ord0:'I_1))=(ord_max:'I_2) by apply:val_inj;reflexivity.
  rewrite hLast (@oriented_simplex_current_point R h2 n (current_simplex_face v ord_max))
    current_simplex_pair_last_face.
  reflexivity.
- pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
  pose tail:=current_simplex_tail v.
  pose T:=F m.+1 tail.
  pose hT:=@oriented_simplex_current_compact R h2 n m.+1 tail.
  pose B:=Boundary m T.
  pose hB:=@current_compact_boundary_compact R h2 n m Full hFull T hT.
  pose Q:=fun k:'I_(m.+2)=>F m (current_simplex_face tail k).
  pose a:=fun k:'I_(m.+2)=>(-1:R)^+(k:nat).
  pose hQ:=fun k:'I_(m.+2)=>@oriented_simplex_current_compact R h2 n m (current_simplex_face tail k).
  pose Sum:=\sum_k a k*:Q k.
  pose hSum:=@current_compact_weighted_finite_sum R h2 n m Full hFull (m.+2) a Q hQ.
  have hBoundaryTail:B=Sum:=ih tail.
  have hInput:=@current_join_current_congruence R h2 n 0%N m P P B Sum hP hP hB hSum
    (erefl P) hBoundaryTail.
  have hLinear:=@current_join_second_weighted_sum R h2 n 0%N m P hP (m.+2) a Q hQ hSum.
  have hFaces:(\sum_k a k*:@CurrentJoin.value R h2 n 0%N m P (Q k) hP (hQ k))=
      \sum_(k:'I_(m.+2)) (-1:R)^+(k:nat)*:F m.+1 (current_simplex_face v (lift ord0 k)).
    apply:eq_bigr=>k _.
    by rewrite (@oriented_simplex_current_nonfirst_face R h2 n m v k).
  have hSigns:(\sum_(k:'I_(m.+2)) (-1:R)^+(lift ord0 k:nat)*:
      F m.+1 (current_simplex_face v (lift ord0 k)))=
      -(\sum_(k:'I_(m.+2)) (-1:R)^+(k:nat)*:F m.+1 (current_simplex_face v (lift ord0 k))).
    rewrite -sumrN;apply:eq_bigr=>k _.
    by rewrite lift0 exprS mulN1r scaleNr.
  rewrite (@oriented_simplex_current_boundary_recursion R h2 n m v) hInput hLinear hFaces.
  rewrite [RHS]big_ord_recl expr0 scale1r.
  cbn beta in hSigns.
  cbn beta.
  by rewrite hSigns.
Qed.
End OrientedSimplexCurrentBoundary.
