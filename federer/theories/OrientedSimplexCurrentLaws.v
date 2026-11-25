(** Federer (1969), 4.1.11, p. 365: public original
    point, compact-support and join laws for the opaque
    oriented-simplex family. Derive them from the independent
    family laws; never use the recursive existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransport CurrentAboveDimension
  CurrentJoinSealed CurrentJoinBoundaryDegree OrientedSimplexCurrentUP
  OrientedSimplexCurrentFamilyLaws OrientedSimplexCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedSimplexCurrentLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation F := (fun (m:nat) (w:'I_(m.+1)->X)=>@OrientedSimplexCurrent.value R h2 n m w).
Local Notation hF := (@OrientedSimplexCurrent.laws R h2 n).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).
Local Notation Compact := (fun m (T:C m)=>@compact
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
  (@current_support R h2 n Full hFull m T)).

(** Source for [oriented_simplex_current_point]: [u]=delta_u,
    the original base of the simplex recursion in Federer
    4.1.11, p. 365. *)
Theorem oriented_simplex_current_point (v:'I_1->X):
  F 0%N v=@dirac_current R h2 n Full hFull (v ord0).
Proof. exact:(hF.1 v). Qed.

(** Source for [oriented_simplex_current_compact]: every
    original ordered simplex is a compact current,
    Federer 4.1.11, p. 365. This follows from the
    abstract family theorem, not its hidden construction. *)
Theorem oriented_simplex_current_compact m (v:'I_(m.+1)->X):Compact m (F m v).
Proof. exact:(@oriented_simplex_family_compact R h2 n F hF m v). Qed.

(** Source for [oriented_simplex_current_successor]: the
    original simplex is the point join with its ordered
    tail, Federer 4.1.11, p. 365. Every compactness
    proof is allowed and equal degrees alone are identified. *)
Theorem oriented_simplex_current_successor m (v:'I_(m.+2)->X)
    (hP:Compact 0%N (@dirac_current R h2 n Full hFull (v ord0)))
    (hT:Compact m (F m (current_simplex_tail v))):
  F m.+1 v=@current_degree_transport R h2 n Full hFull (0+1+m)%N m.+1
    (current_join_degree_successor 0%N m)
    (@CurrentJoin.value R h2 n 0%N m (@dirac_current R h2 n Full hFull (v ord0))
      (F m (current_simplex_tail v)) hP hT).
Proof. exact:(@oriented_simplex_family_successor R h2 n F hF m v hP hT). Qed.

(** Source for [oriented_simplex_current_above_dimension]:
    every original simplex above the ambient dimension is
    zero, supporting Federer 4.1.11, pp. 365–366, by
    the preceding dimension theorem of 4.1.10, p. 364. *)
Theorem oriented_simplex_current_above_dimension m (v:'I_(m.+1)->X):
  (n<m)%N->F m v=0.
Proof. move=>hm;exact:(@current_above_dimension R h2 n m hm Full hFull (F m v)). Qed.
End OrientedSimplexCurrentLaws.
