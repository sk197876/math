(** Federer (1969), 4.1.8, p. 360: composition of the
    existing equal-degree identifications used for the original
    boundary formulas. These identify equal natural degrees only. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentDegreeTransportComposition.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.


(** Source for [current_test_degree_transport_composition]:
    composing original equal-degree identifications changes
    only the equality witness, supporting the boundary
    product formulas of Federer 4.1.8, p. 360. *)
Lemma current_test_degree_transport_composition a b c (e:a=b) (f:b=c)
    (phi:@current_test_space R h2 n U hU a):
  @current_test_degree_transport R h2 n U hU b c f
    (@current_test_degree_transport R h2 n U hU a b e phi)=
  @current_test_degree_transport R h2 n U hU a c (eq_trans e f) phi.
Proof. by case:b /e in f *;case:c /f. Qed.

(** Source for [current_degree_transport_composition]:
    the same composition law on original currents,
    supporting Federer 4.1.8, p. 360. *)
Lemma current_degree_transport_composition a b c (e:a=b) (f:b=c)
    (T:@current_space R h2 n U hU a):
  @current_degree_transport R h2 n U hU b c f
    (@current_degree_transport R h2 n U hU a b e T)=
  @current_degree_transport R h2 n U hU a c (eq_trans e f) T.
Proof. by case:b /e in f *;case:c /f. Qed.
End CurrentDegreeTransportComposition.
