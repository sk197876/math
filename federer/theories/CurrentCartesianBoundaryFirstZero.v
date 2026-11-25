(** Federer (1969), 4.1.8, p. 360: original mixed tests
    and equal-degree identifications for the product formulas.
    All current and test spaces are the actual opaque spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed
  CurrentCartesianProductTransportedAction CurrentCartesianMixedExtensional
  CurrentCartesianBoundaryTests CurrentBoundary CurrentTestExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianBoundaryFirstZero.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation CC := (fun r=>@current_space R h2 (m+n) AB hAB r).
Local Notation CA := (fun r=>@current_space R h2 m A hA r).
Local Notation CB := (fun r=>@current_space R h2 n B hB r).
Local Notation ec := (fun r=>@current_value R h2 (m+n) AB hAB r).
Local Notation ea := (fun r=>@current_value R h2 m A hA r).
Local Notation eb := (fun r=>@current_value R h2 n B hB r).
Local Notation Tr := (fun a b (e:a=b)=>@current_test_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation CTr := (fun a b (e:a=b)=>@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation Product := (fun i j=>@CartesianCurrentProduct.value R h2 m n i j A B hA hB).

Local Notation bdA := (fun r=>@current_boundary R h2 m r A hA).
Local Notation bdB := (fun r=>@current_boundary R h2 n r B hB).
Local Notation bdC := (fun r=>@current_boundary R h2 (m+n) r AB hAB).
Local Notation dA := (fun r=>@current_test_exterior_derivative R h2 m r A hA).
Local Notation dB := (fun r=>@current_test_exterior_derivative R h2 n r B hB).

(** Source for [current_cartesian_boundary_first_zero]:
    when only S has positive degree, the original
    boundary of S times T is boundary S times T,
    the second boundary case of Federer 4.1.8,
    p. 360. No boundary of a zero-current is introduced. *)
Theorem current_cartesian_boundary_first_zero i (S:CA i.+1) (T:CB 0%N):
  bdC (i+0) (CTr _ _ (addSn i 0) (Product i.+1 0 S T))=
    Product i 0 (bdA i S) T.
Proof.
apply:(@current_cartesian_mixed_values_extensional R h2 m n A B hA hB (i+0)).
move=>k l e a b.
cbn beta.
rewrite (@current_cartesian_boundary_tests R h2 m n A B hA hB (i+0)
  (CTr _ _ (addSn i 0) (Product i.+1 0 S T)) k l e a b).
have hSucc:l.+1<>0%N by discriminate.
have hSecond:=@current_cartesian_product_transported_off_second R h2 m n A B hA hB
  i.+1 0%N (i+0).+1 (addSn i 0) S T k l.+1
  (eq_trans (addnS k l) (congr1 (fun r:nat=>r.+1) e)) hSucc a (dB l b).
case:(pselect (k = i))=>hk.
- subst k.
  have hl:l=0%N.
    apply/eqP;have heq:(i+l == i+0)%N:=introT eqP e.
    by rewrite eqn_add2l in heq.
  subst l.
  have hFirst:=@current_cartesian_product_transported_diagonal R h2 m n A B hA hB
    i.+1 0%N (i+0).+1 (addSn i 0)
    (eq_trans (addSn i 0) (congr1 (fun r:nat=>r.+1) e)) S T (dA i a) b.
  rewrite hFirst hSecond mulr0 addr0 current_test_degree_transport_identity
    ((@CartesianCurrentProduct.laws R h2 m n i 0%N A B hA hB (bdA i S) T).1 a b).
  by rewrite (@current_boundary_evaluation R h2 m i A hA S a).
- have hkSucc:k.+1<>i.+1.
    move=>h;apply:hk;exact:(congr1 predn h).
  have hFirst:=@current_cartesian_product_transported_off_diagonal R h2 m n A B hA hB
    i.+1 0%N (i+0).+1 (addSn i 0) S T k.+1 l
    (eq_trans (addSn k l) (congr1 (fun r:nat=>r.+1) e)) hkSucc (dA k a) b.
  have hRight:=(@CartesianCurrentProduct.laws R h2 m n i 0%N A B hA hB (bdA i S) T).2
    k l e hk a b.
  by rewrite hFirst hSecond hRight mulr0 add0r.
Qed.
End CurrentCartesianBoundaryFirstZero.
