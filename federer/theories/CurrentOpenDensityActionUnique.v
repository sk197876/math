(** Federer (1969), 4.1.18, p. 375: the
    original integration action uniquely determines each density
    current used in q. This consequence of 4.1.7,
    pp. 355–357, retains the actual arbitrary open U
    and original measure and multivector field. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentSpaces CurrentEvaluation
  CurrentIntegrationCriterion DistributionIntegrationRepresentationUP
  MeasureIntegralUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_open_density_action_unique]:
    two actual currents with the same original
    density integral are equal, supporting the L1
    pair map and its smooth approximants in
    Federer 4.1.18, pp. 375–376. No finite
    mass, compact support or smoothness premise is needed. *)
Theorem current_open_density_action_unique (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (mu:set (current_domain R n U)->\bar R)
    (xi:current_domain R n U->exterior_power (R_n R n) m)
    (T S:@current_space R h2 n U hU m):
  @is_current_integration_representation R h2 n m U hU T mu xi->
  @is_current_integration_representation R h2 n m U hU S mu xi->T = S.
Proof.
move=>hT hS;apply:(@current_values_extensional R h2 n m U hU)=>omega.
exact:(EFin_inj (measure_integral_unique
  (distribution_representation_action hT omega)
  (distribution_representation_action hS omega))).
Qed.
