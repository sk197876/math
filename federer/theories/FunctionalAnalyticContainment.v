(** Federer (1969), 3.4.5, p. 321,
    used in corrected 3.4.8(11), pp. 327, 333:
    every functional analytic submanifold lies in its
    actual defining domain. The original membership
    equation already includes this containment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [functional_analytic_domain_containment]:
    the domain clause of the original functional
    analytic manifold definition, 3.4.5, p. 321,
    retained in the successive-stratum assembly of
    3.4.8(11), p. 333. *)
Lemma functional_analytic_domain_containment (R:realType) n m (U S:set (R_n R n)):
  @is_functional_analytic_submanifold R n m U S ->S `<=` U.
Proof.
move=>[_ [_ [f [g [_ [_ [hEquation _]]]]]]] x hx.
exact:((hEquation x).1 hx).1.
Qed.
