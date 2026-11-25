(** Federer (1969), 4.1.7, pp. 356–359:
    identifying equal degrees preserves actual
    supports. These supporting identities concern
    equality transport only. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentSupportGeometry CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportSupport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.

(** Source for [current_test_degree_transport_support]:
    equal original test degrees have the
    same support, supporting Federer 4.1.7,
    pp. 356–359. *)
Lemma current_test_degree_transport_support m q (h:m=q)
    (phi:@current_test_space R h2 n U hU m):
  @current_test_support R h2 n q U hU
    (@current_test_degree_transport R h2 n U hU m q h phi)=
    @current_test_support R h2 n m U hU phi.
Proof. by case:q /h in phi *. Qed.

(** Source for [current_degree_transport_support]:
    identifying equal current dimensions preserves
    the original support, supporting Federer
    4.1.7, pp. 356–359. *)
Lemma current_degree_transport_support m q (h:m=q)
    (T:@current_space R h2 n U hU m):
  @current_support R h2 n U hU q (@current_degree_transport R h2 n U hU m q h T)=
    @current_support R h2 n U hU m T.
Proof. by case:q /h in T *. Qed.
End CurrentDegreeTransportSupport.
