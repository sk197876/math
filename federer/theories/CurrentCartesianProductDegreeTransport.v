(** Federer (1969), 4.1.8, pp. 360–362: identifying
    equal degrees in each factor identifies the total
    product degree. This bookkeeping supports finite
    products without altering the original ambient space. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentDegreeTransport CurrentDegreeTransportIdentity
  CurrentCartesianDomain CurrentCartesianProductSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_cartesian_product_degree_transport]: the
    original product respects equal-degree identifications,
    supporting the finite products of Federer 4.1.8,
    p. 362. The equality proofs introduce no
    new mathematical premise or degree. *)
Lemma current_cartesian_product_degree_transport (R:realType) (h2:(1+1:R)!=0) m n
    (A:set (R_n R m)) (B:set (R_n R n))
    (hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a)
    (hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b)
    i j i' j' (ei : i = i') (ej : j = j')
    (S:@current_space R h2 m A hA i) (T:@current_space R h2 n B hB j):
  @current_degree_transport R h2 (m+n) (@euclidean_cartesian_set R m n A B)
    (@current_cartesian_domain_open R m n A B hA hB) (i+j) (i'+j')
    (congr2 addn ei ej) (@CartesianCurrentProduct.value R h2 m n i j A B hA hB S T)=
    @CartesianCurrentProduct.value R h2 m n i' j' A B hA hB
      (@current_degree_transport R h2 m A hA i i' ei S)
      (@current_degree_transport R h2 n B hB j j' ej T).
Proof.
case:i' /ei;case:j' /ej.
by rewrite !current_degree_transport_identity.
Qed.
