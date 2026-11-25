(** Federer (1969), 4.1.12, p. 369: equal
    natural degrees have equal original comass. This
    bookkeeping law supports the separated-test derivative
    bound and reuses the existing degree identification. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentCoefficientNorms
  CurrentDegreeTransport CurrentDegreeTransportIdentity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentTestDegreeComass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.

(** Source for [current_test_degree_transport_comass]:
    identifying equal test degrees preserves pointwise
    comass, supporting the actual separated-test Leibniz
    estimate of Federer 4.1.12, p. 369. *)
Lemma current_test_degree_transport_comass a b (e:a=b)
    (psi:@current_test_space R h2 n U hU a) x:
  @current_form_comass R h2 n b
    (@current_test_value R h2 n U hU b
      (@current_test_degree_transport R h2 n U hU a b e psi) x)=
    @current_form_comass R h2 n a (@current_test_value R h2 n U hU a psi x).
Proof.
case:b /e.
by rewrite current_test_degree_transport_identity.
Qed.
End CurrentTestDegreeComass.
