(** Federer (1969), 4.1.8, p. 360: original mixed tests
    and equal-degree identifications for the product formulas.
    All current and test spaces are the actual opaque spaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentDegreeTransport
  CurrentDegreeTransportIdentity CurrentDegreeTransportComposition CurrentEvaluation
  CurrentPointEvaluation CurrentCartesianMixedAnnihilator CurrentCartesianProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestDegreeTransport.
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


(** Source for [current_cartesian_test_product_first_transport]:
    identifying the first test degree identifies exactly
    the resulting total degree, supporting the original
    product associativity in Federer 4.1.8, p. 361. *)
Lemma current_cartesian_test_product_first_transport k l q (e:k=q)
    (alpha:DA k) (beta:DB l):
  Pure q l (@current_test_degree_transport R h2 m A hA k q e alpha) beta=
    Tr _ _ (congr1 (fun r:nat=>(r+l)%N) e) (Pure k l alpha beta).
Proof. by case:q /e. Qed.

(** Source for [current_cartesian_test_product_second_transport]:
    identifying the second test degree identifies exactly
    the resulting total degree, supporting the original
    product associativity in Federer 4.1.8, p. 361. *)
Lemma current_cartesian_test_product_second_transport k l q (e:l=q)
    (alpha:DA k) (beta:DB l):
  Pure k q alpha (@current_test_degree_transport R h2 n B hB l q e beta)=
    Tr _ _ (congr1 (addn k) e) (Pure k l alpha beta).
Proof. by case:q /e. Qed.
End CurrentCartesianTestDegreeTransport.
