(** Federer (1969), 3.4.5, p. 319:
    the original representative equations for
    analytic germ addition, multiplication and
    negation, in the public ring notation.
    These connections support the actual equations
    of 3.4.8(10), p. 331. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP AnalyticGermSealed AnalyticGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Equations.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable a:X.
Local Notation P:=(@analytic_representative_type R X NX hNX a).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX a)].

(** Source for [analytic_representative_add_ring_equation]:
    functional addition represents ring addition,
    3.4.5, p. 319, applied to
    the equations of 3.4.8(10), p. 331. *)
Lemma analytic_representative_add_ring_equation (f g:P):
  (analytic_germ (@analytic_add_representatives R X NX hNX a f g):G) =
    (analytic_germ f:G)+(analytic_germ g:G).
Proof.
exact:esym (@analytic_germ_add_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a) f g).
Qed.

(** Source for [analytic_representative_multiply_ring_equation]:
    functional multiplication represents ring multiplication,
    3.4.5, p. 319, applied to
    the equations of 3.4.8(10), p. 331. *)
Lemma analytic_representative_multiply_ring_equation (f g:P):
  (analytic_germ (@analytic_multiply_representatives R X NX hNX a f g):G) =
    (analytic_germ f:G)*(analytic_germ g:G).
Proof.
exact:esym (@analytic_germ_multiply_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a) f g).
Qed.

(** Source for [analytic_representative_negate_ring_equation]:
    functional negation represents ring negation,
    3.4.5, p. 319, applied to
    the equations of 3.4.8(10), p. 331. *)
Lemma analytic_representative_negate_ring_equation (f:P):
  (analytic_germ (@analytic_negate_representative R X NX hNX a f):G) = -(analytic_germ f:G).
Proof.
exact:esym (@analytic_germ_negate_equation _ _ _ _ _ _ _ _ (@AnalyticGerms.laws R X NX hNX a) f).
Qed.
End Equations.
