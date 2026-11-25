(** Federer (1969), 4.1.7, pp. 356–358:
    equal-degree identification preserves integral
    representability. This is equality bookkeeping
    for the original current identities. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces CurrentDegreeTransport CurrentIntegrationCriterion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentRepresentableDegreeTransport.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Arguments hU : clear implicits.

(** Source for [represented_current_degree_transport]:
    equal original current dimensions retain
    exactly the same integral representation,
    supporting Federer 4.1.7, pp. 356–358. *)
Theorem represented_current_degree_transport m q (h:m=q) (T:@current_space R h2 n U hU m):
  @is_integration_representable_current R h2 n m U hU T->
  @is_integration_representable_current R h2 n q U hU
    (@current_degree_transport R h2 n U hU m q h T).
Proof. by case:q /h in T *. Qed.
End CurrentRepresentableDegreeTransport.
