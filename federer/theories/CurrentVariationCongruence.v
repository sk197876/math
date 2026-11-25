(** Federer (1969), 4.1.13, pp. 369–370: equal currents
    have the same original variation measure, with every
    representability witness. This identifies the restriction
    of boundary T with the boundary of restricted T without
    changing the original measures or normalizations of 4.1.7,
    p. 357. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentIntegrationCriterion NormalisedCurrentSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_variation_current_congruence]: the original
    variation is invariant under equality of the actual current,
    supporting the two integrals in Federer 4.1.13, pp. 369–370.
    Proof irrelevance only identifies evidence of representability. *)
Theorem current_variation_current_congruence (R:realType) (h2:(1+1:R)!=0)
    n m (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x)
    (T S:@current_space R h2 n U hU m)
    (hT:@is_integration_representable_current R h2 n m U hU T)
    (hS:@is_integration_representable_current R h2 n m U hU S):
  T=S->@NormalisedCurrent.measure R h2 n m U hU T hT=
    @NormalisedCurrent.measure R h2 n m U hU S hS.
Proof.
move=>hEqual;subst S.
have hProofs:hS=hT:=Prop_irrelevance _ _.
by subst hS.
Qed.
