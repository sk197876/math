(** Federer (1969), 4.1.8, p. 360: composition of the
    existing equal-degree identifications used for the original
    boundary formulas. These identify equal natural degrees only. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport CurrentTestExteriorDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportExterior.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.


(** Source for [current_test_degree_transport_exterior]:
    exterior differentiation commutes with the existing
    equal-degree identification, supporting the three
    boundary formulas of Federer 4.1.8, p. 360. *)
Lemma current_test_degree_transport_exterior a b (e:a=b)
    (phi:@current_test_space R h2 n U hU a):
  @current_test_exterior_derivative R h2 n b U hU
    (@current_test_degree_transport R h2 n U hU a b e phi)=
  @current_test_degree_transport R h2 n U hU a.+1 b.+1 (congr1 S e)
    (@current_test_exterior_derivative R h2 n a U hU phi).
Proof. by case:b /e. Qed.
End CurrentDegreeTransportExterior.
