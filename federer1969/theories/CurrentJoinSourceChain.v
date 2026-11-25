(** Federer (1969), 4.1.11, p. 364: the ordered source
    current S times [0,1] times T. Both products are the original
    opaque Cartesian products. Only the preceding equal-degree
    identification associates the printed degree i+1+j. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentDegreeTransport CurrentJoinDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentJoinSourceChain.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n i j : nat.
Local Notation X := (R_n R n).
Local Notation Full := (fun _ : X => True).
Local Notation Time := (fun _ : R_n R 1%N => True).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NT := (inner_norm (@euclidean_inner_productP R 1%N)).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation hTime := (fun (t : R_n R 1%N) (_ : True) =>
  @norm_full_domain_interior R (R_n R 1%N) NT t).
Local Notation TimeSpace := (@euclidean_cartesian_set R 1%N n Time Full).
Local Notation hTimeSpace :=
  (@current_cartesian_domain_open R 1%N n Time Full hTime hFull).
Local Notation Domain := (@current_join_domain R n).
Local Notation hDomain := (@current_join_domain_open R n).
Variable S : @current_space R h2 n Full hFull i.
Variable T : @current_space R h2 n Full hFull j.
Local Notation Segment := (@current_join_time_segment R h2).
Local Notation Inner :=
  (@CartesianCurrentProduct.value R h2 1%N n 1%N j
    Time Full hTime hFull Segment T).
Local Notation Product :=
  (@CartesianCurrentProduct.value R h2 n (1+n)%N i (1+j)%N
    Full TimeSpace hFull hTimeSpace S Inner).

(** Source for [current_join_source_chain]: the actual original
    product S times [0,1] times T, Federer 4.1.11, p. 364.
    Reassociation of the natural degree uses an existing public
    transport; the mathematical current is not reconstructed. *)
Definition current_join_source_chain :
    @current_space R h2 (n+(1+n))%N Domain hDomain (i+1+j)%N :=
  @current_degree_transport R h2 (n+(1+n))%N Domain hDomain
    (i+(1+j))%N (i+1+j)%N (addnA i 1%N j) Product.
End CurrentJoinSourceChain.
