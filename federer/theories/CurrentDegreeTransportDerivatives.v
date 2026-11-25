(** Federer (1969), 4.1.7, p. 356: identifying
    equal degrees does not change the original
    directional derivative. These supporting identities
    concern equality transport only. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport CurrentDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportDerivatives.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.

(** Source for [current_degree_transport_directional]:
    equal current dimensions commute with the
    actual derivative, supporting Federer 4.1.7,
    p. 356. *)
Lemma current_degree_transport_directional m q (h:m=q) v
    (T:@current_space R h2 n U hU m):
  @current_directional_derivative R h2 n q U hU v
    (@current_degree_transport R h2 n U hU m q h T)=
  @current_degree_transport R h2 n U hU m q h
    (@current_directional_derivative R h2 n m U hU v T).
Proof. by case:q /h in T *. Qed.

(** Source for [current_test_degree_transport_directional]:
    equal test degrees commute with the actual
    derivative, supporting Federer 4.1.7, p. 356. *)
Lemma current_test_degree_transport_directional m q (h:m=q) v
    (phi:@current_test_space R h2 n U hU m):
  @current_test_directional_derivative R h2 n q U hU v
    (@current_test_degree_transport R h2 n U hU m q h phi)=
  @current_test_degree_transport R h2 n U hU m q h
    (@current_test_directional_derivative R h2 n m U hU v phi).
Proof. by case:q /h in phi *. Qed.
End CurrentDegreeTransportDerivatives.
