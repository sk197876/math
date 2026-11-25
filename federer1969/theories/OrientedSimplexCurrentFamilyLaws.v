(** Federer (1969), 4.1.11, p. 365: the defining
    point and join laws determine the oriented-simplex
    family and imply compact support. Derive these facts
    from the independent specification before sealing the
    family. The recursion construction is not used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransport CurrentDegreeTransportIdentity CurrentDegreeTransportSupport
  CurrentCompactElementaryPushforwards CurrentJoinUP CurrentJoinExistence CurrentJoinSealed CurrentJoinLaws
  CurrentJoinBoundaryDegree OrientedSimplexCurrentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentFamilyLaws.
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
Variable F:forall m:nat,('I_(m.+1)->X)->C m.
Arguments F : clear implicits.
Hypothesis hF:@is_oriented_simplex_current_family R h2 n F.

(** Source for [oriented_simplex_family_compact]: every
    original oriented simplex has compact support,
    Federer 4.1.11, p. 365. The point and original
    compact-join theorems prove this by induction. *)
Theorem oriented_simplex_family_compact m (v:'I_(m.+1)->X):Compact m (F m v).
Proof.
elim:m v=>[|m ih] v.
- rewrite hF.1;exact:(@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I).
- pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
  pose T:=F m (current_simplex_tail v).
  pose hT:=ih (current_simplex_tail v).
  pose J:=@CurrentJoin.value R h2 n 0%N m P T hP hT.
  pose e:=current_join_degree_successor 0%N m.
  have hEqual:=@current_join_unique R h2 n 0%N m P T hP hT _ J
    (hF.2 m v) (@CurrentJoin.laws R h2 n 0%N m P T hP hT).
  have hAligned:=congr1 (@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1 e) hEqual.
  rewrite current_degree_transport_roundtrip in hAligned.
  rewrite hAligned current_degree_transport_support.
  exact:(@current_join_compact R h2 n 0%N m P T hP hT).
Qed.

(** Source for [oriented_simplex_family_successor]: the
    original successor simplex is the actual opaque point
    join, after identifying equal degrees, Federer 4.1.11,
    p. 365. Every compactness proof may be used. *)
Theorem oriented_simplex_family_successor m (v:'I_(m.+2)->X)
    (hP:Compact 0%N (@dirac_current R h2 n Full hFull (v ord0)))
    (hT:Compact m (F m (current_simplex_tail v))):
  F m.+1 v=@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
    (current_join_degree_successor 0%N m)
    (@CurrentJoin.value R h2 n 0%N m (@dirac_current R h2 n Full hFull (v ord0))
      (F m (current_simplex_tail v)) hP hT).
Proof.
have hEqual:=@current_join_unique R h2 n 0%N m
  (@dirac_current R h2 n Full hFull (v ord0)) (F m (current_simplex_tail v)) hP hT _ _
  (hF.2 m v) (@CurrentJoin.laws R h2 n 0%N m
    (@dirac_current R h2 n Full hFull (v ord0)) (F m (current_simplex_tail v)) hP hT).
have hAligned:=congr1 (@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
  (current_join_degree_successor 0%N m)) hEqual.
by rewrite current_degree_transport_roundtrip in hAligned.
Qed.

(** Source for [oriented_simplex_family_unique]: the
    original point and join recursion determines the
    entire oriented-simplex family uniquely, supporting
    Federer 4.1.11, p. 365. No representation of a
    simplex or of an opaque current is opened. *)
Theorem oriented_simplex_family_unique
    (G:forall m:nat,('I_(m.+1)->X)->C m)
    (hG:@is_oriented_simplex_current_family R h2 n G):F=G.
Proof.
have hPointwise:forall m (v:'I_(m.+1)->X),F m v=@G m v.
  elim=>[|m ih] v;first by rewrite hF.1 hG.1.
  pose P:=@dirac_current R h2 n Full hFull (v ord0).
  pose hP:=@current_compact_dirac_support R h2 n Full hFull (v ord0) Logic.I.
  pose T:=F m (current_simplex_tail v).
  pose hT:=@oriented_simplex_family_compact m (current_simplex_tail v).
  have hGrec:=hG.2 m v.
  rewrite -(ih (current_simplex_tail v)) in hGrec.
  have hEqual:=@current_join_unique R h2 n 0%N m P T hP hT _ _ (hF.2 m v) hGrec.
  have hAligned:=congr1 (@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
    (current_join_degree_successor 0%N m)) hEqual.
  by rewrite !current_degree_transport_roundtrip in hAligned.
apply:functional_extensionality_dep=>m;apply:funext=>v;exact:hPointwise.
Qed.
End OrientedSimplexCurrentFamilyLaws.
