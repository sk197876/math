(** Federer (1969), 4.1.11, p. 365: existence of
    the original oriented-simplex family. A recursive
    compact-current witness proves the independent point
    and join laws. Its compactness data are implementation
    evidence; no boundary or alternation law is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransport CurrentDegreeTransportInverse CurrentDegreeTransportSupport
  CurrentCompactElementaryPushforwards CurrentJoinUP CurrentJoinSealed CurrentJoinLaws
  CurrentJoinBoundaryDegree OrientedSimplexCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).
Local Notation Compact := (fun m (T:C m)=>@compact (real_norm_metric_space hNX)
  (@current_support R h2 n Full hFull m T)).

(** Source for [oriented_simplex_compact_witness]: a
    witness for the original recursion of Federer
    4.1.11, p. 365. The construction serves only the
    following existence theorem and is hidden by the
    subsequent opaque family interface. *)
Fixpoint oriented_simplex_compact_witness (m:nat):
    forall v:'I_(m.+1)->X,{T:C m | Compact m T}.
Proof.
case:m=>[|m] v.
- exists (@dirac_current R h2 n Full hFull (v ord0)).
  exact:(@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I).
- pose tail:=@oriented_simplex_compact_witness m (current_simplex_tail v).
  pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
  pose T:=proj1_sig tail.
  pose hT:=proj2_sig tail.
  pose J:=@CurrentJoin.value R h2 n 0%N m P T hP hT.
  exists (@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
    (current_join_degree_successor 0%N m) J).
  rewrite current_degree_transport_support.
  exact:(@current_join_compact R h2 n 0%N m P T hP hT).
Defined.

(** Source for [oriented_simplex_current_family_exists]:
    the original point and successor join laws have an
    actual family of currents, Federer 4.1.11, p. 365.
    The independent specification supplies the only laws
    of the following opaque interface. *)
Theorem oriented_simplex_current_family_exists:
  exists F:forall m:nat,('I_(m.+1)->X)->C m,
    @is_oriented_simplex_current_family R h2 n F.
Proof.
pose F:=fun m (v:'I_(m.+1)->X)=>proj1_sig (@oriented_simplex_compact_witness m v).
exists F;split;first by move=>v.
move=>m v.
pose tail:=@oriented_simplex_compact_witness m (current_simplex_tail v).
pose P:=@dirac_current R h2 n Full hFull (v ord0).
pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
pose T:=proj1_sig tail.
pose hT:=proj2_sig tail.
pose J:=@CurrentJoin.value R h2 n 0%N m P T hP hT.
change (@is_current_join R h2 n 0%N m P T
  (@current_degree_transport R h2 n Full hFull m.+1 (0+1+m)%N
    (esym (current_join_degree_successor 0%N m))
    (@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
      (current_join_degree_successor 0%N m) J))).
rewrite current_degree_transport_inverse.
exact:(@CurrentJoin.laws R h2 n 0%N m P T hP hT).
Qed.
End OrientedSimplexCurrentExistence.
