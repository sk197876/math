(** Federer (1969), 4.1.11, p. 365: independent
    specification of the oriented-simplex currents. The
    zero simplex is the original point current, and each
    successor is the original point join with the tail.
    Boundary, affine and permutation assertions are theorems,
    not defining laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentDirac CurrentDegreeTransport CurrentJoinUP CurrentJoinBoundaryDegree.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_simplex_face]: deleting the kth
    vertex in the original simplex boundary sum, Federer
    4.1.11, p. 365. This is the existing ordinal lift
    applied to the original ordered vertex family. *)
Definition current_simplex_face (X:Type) m (v:'I_(m.+2)->X) (k:'I_(m.+2)):
    'I_(m.+1)->X:=fun i=>v (lift k i).

(** Source for [current_simplex_tail]: the original tail
    (u_1,...,u_m) in the defining point-join recursion,
    Federer 4.1.11, p. 365. *)
Definition current_simplex_tail (X:Type) m (v:'I_(m.+2)->X):
    'I_(m.+1)->X:=current_simplex_face v ord0.

Section OrientedSimplexCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _:X=>True).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X
  (inner_norm (@euclidean_inner_productP R n)) x).
Local Notation C := (fun m=>@current_space R h2 n Full hFull m).

(** Source for [is_oriented_simplex_current_family]:
    [u]=delta_u and [u_0,...,u_m]=[u_0] join [u_1,...,u_m],
    Federer 4.1.11, p. 365. Only the actual point-current
    and independent join action are imposed. Compactness,
    boundary and alternation are not assumed. *)
Definition is_oriented_simplex_current_family
    (F:forall m:nat,('I_(m.+1)->X)->C m):Prop:=
  (forall v:'I_1->X,F 0%N v=@dirac_current R h2 n Full hFull (v ord0)) /\
  (forall m (v:'I_(m.+2)->X),
    @is_current_join R h2 n 0%N m
      (@dirac_current R h2 n Full hFull (v ord0))
      (F m (current_simplex_tail v))
      (@current_degree_transport R h2 n Full hFull m.+1 (0+1+m)%N
        (esym (current_join_degree_successor 0%N m)) (F m.+1 v))).
End OrientedSimplexCurrentUP.
