(** Federer (1969), 4.1.7, p. 356: equal
    original degrees are identified by inverse maps.
    This is administrative equality transport for
    the printed identities, not an added hypothesis. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportInverse.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.

(** Source for [current_test_degree_transport_inverse]:
    the reverse original test identification inverts
    the forward one, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_test_degree_transport_inverse m q (h:m=q)
    (phi:@current_test_space R h2 n U hU m):
  @current_test_degree_transport R h2 n U hU q m (esym h)
    (@current_test_degree_transport R h2 n U hU m q h phi)=phi.
Proof. by case:q /h. Qed.

(** Source for [current_degree_transport_inverse]:
    the reverse original current identification inverts
    the forward one, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_degree_transport_inverse m q (h:m=q)
    (T:@current_space R h2 n U hU m):
  @current_degree_transport R h2 n U hU q m (esym h)
    (@current_degree_transport R h2 n U hU m q h T)=T.
Proof. by case:q /h. Qed.
End CurrentDegreeTransportInverse.
