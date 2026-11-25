(** Federer (1969), 2.10.44, printed p. 202, final infimum formula needs a
    nonempty original source when the new ambient space is nonempty. An
    empty cost family has no finite greatest lower bound, though a constant
    Lipschitz extension still exists. This is a local qualification of the
    formula, not an entry in Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import McShaneEnvelopeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [empty_mcshane_costs]: supporting empty-
    source check for the formula in 2.10.44,
    p. 202. There are no prescribed costs. *)
Lemma empty_mcshane_costs (R : realType) (X : metricType R) (f : X -> R) L x :
  mcshane_costs_at set0 f L x=set0.
Proof. by apply/seteqP; split=> r; first move=> [a []]. Qed.

(** Source for [empty_source_no_finite_mcshane_envelope]: local
    counterexample to a finite-valued reading of the
    unqualified infimum formula in 2.10.44, p. 202.
    At any ambient point, every real is a lower
    bound for the empty family, so no finite
    value satisfies its genuine greatest-lower-bound law. *)
Theorem empty_source_no_finite_mcshane_envelope (R : realType) (X : metricType R)
    (f : X -> R) (L : R) (x0 : X) :
  ~ exists g, is_mcshane_envelope set0 f L g.
Proof.
move=> [g hg].
have hh : g x0+1<=g x0.
  apply: (@mcshane_envelope_greatest_law R X set0 f L g hg x0 (g x0+1)).
  by move=> a [].
have hstrict : g x0<g x0+1 by rewrite ltrDl ltr01.
have hfalse := lt_le_trans hstrict hh; by rewrite ltxx in hfalse.
Qed.
