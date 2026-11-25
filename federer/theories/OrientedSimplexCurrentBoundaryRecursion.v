(** Federer (1969), 4.1.11, p. 365: apply the
    original point-join boundary formula to the opaque
    simplex recursion. The one-dimensional endpoint uses
    the previously proved oriented-segment boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDiracSmooth CurrentBoundary CurrentCompactBoundarySmooth
  CurrentCompactElementaryPushforwards CurrentJoinSealed CurrentJoinBoundaryDegree CurrentJoinBoundaryFirstZero
  OrientedSegmentCurrentBoundary OrientedSimplexCurrentUP OrientedSimplexCurrentSealed
  OrientedSimplexCurrentLaws OrientedSimplexCurrentLowDegrees.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentBoundaryRecursion.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (w:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m w).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).
Local Notation Boundary := (fun m=>@current_boundary R h2 n m Full hFull).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull m T)).

(** Source for [oriented_simplex_current_boundary_segment]:
    the original one-simplex has boundary its last point
    minus its first point, supporting the first endpoint
    of the boundary sum in Federer 4.1.11, p. 365. *)
Theorem oriented_simplex_current_boundary_segment (v:'I_2->X):
  Boundary 0%N (F 1%N v)=F 0%N (current_simplex_tail v)-@dirac_current R h2 n Full hFull (v ord0).
Proof.
cbn beta.
pose hSegment:=fun (t:R) (_:t \in `[0,1])=>Logic.I.
rewrite (@oriented_simplex_current_segment R h2 n v hSegment)
  oriented_segment_current_boundary oriented_simplex_current_point.
reflexivity.
Qed.

(** Source for [oriented_simplex_current_boundary_recursion]:
    boundary [u_0,...,u_m] is [u_1,...,u_m] minus
    [u_0] join boundary [u_1,...,u_m] in every higher
    degree, Federer 4.1.11, p. 365. The original
    simplex and boundary compactness laws supply every witness. *)
Theorem oriented_simplex_current_boundary_recursion m (v:'I_(m.+3)->X):
  Boundary m.+1 (F m.+2 v)=
    F m.+1 (current_simplex_tail v)-
    @CurrentJoin.value R h2 n 0%N m
      (@dirac_current R h2 n Full hFull (v ord0))
      (Boundary m (F m.+1 (current_simplex_tail v)))
      (@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I)
      (@current_compact_boundary_compact R h2 n m Full hFull
        (F m.+1 (current_simplex_tail v))
        (@oriented_simplex_current_compact R h2 n m.+1 (current_simplex_tail v))).
Proof.
cbn beta.
pose P:=@dirac_current R h2 n Full hFull (v ord0).
pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
pose T:=F m.+1 (current_simplex_tail v).
pose hT:=@oriented_simplex_current_compact R h2 n m.+1 (current_simplex_tail v).
have hRec:=@oriented_simplex_current_successor R h2 n m.+1 v hP hT.
have hBoundary:=@current_join_boundary_first_zero R h2 n m P T hP hT.
rewrite (@dirac_current_total R h2 n Full hFull (v ord0) Logic.I hP) scale1r in hBoundary.
rewrite hRec.
exact:hBoundary.
Qed.
End OrientedSimplexCurrentBoundaryRecursion.
