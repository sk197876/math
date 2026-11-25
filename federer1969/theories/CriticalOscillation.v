(** Federer (1969), 3.4.2(4), pp. 310–311: public oscillation laws. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm RealNormUP ExtendedSupremumUP RealPower
  CriticalOscillationUP CriticalOscillationSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_eta]: the original η of 3.4.2(4),
    pp. 310–311, accessed through the opaque supremum interface. *)
Definition critical_eta (R:realType) m (Y:lmodType R) NY Z S C f lambda delta:=
  @CriticalOscillation.eta R m Y NY Z S C f lambda delta.

(** Source for [critical_zeta]: the original ζ of 3.4.2(4),
    p. 311, accessed through the opaque relative-derivative supremum. *)
Definition critical_zeta (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta:=
  @CriticalOscillation.zeta R m Y NY hNY Z S C f lambda delta.

(** Source for [critical_eta_laws]: the least-upper-bound laws of η
    in 3.4.2(4), pp. 310–311, from its public specification. *)
Lemma critical_eta_laws (R:realType) m (Y:lmodType R) NY Z S C f lambda delta:
  is_critical_function_oscillation NY Z S C f lambda delta
    (@critical_eta R m Y NY Z S C f lambda delta).
Proof. exact:CriticalOscillation.eta_laws. Qed.

(** Source for [critical_zeta_laws]: the least-upper-bound laws of ζ
    in 3.4.2(4), p. 311, from its public specification. *)
Lemma critical_zeta_laws (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta:
  is_critical_tangent_oscillation hNY Z S C f lambda delta
    (@critical_zeta R m Y NY hNY Z S C f lambda delta).
Proof. exact:CriticalOscillation.zeta_laws. Qed.

(** Source for [critical_eta_nonnegative]: the adjoined zero makes η
    nonnegative, 3.4.2(4), pp. 310–311, including an empty test family. *)
Lemma critical_eta_nonnegative (R:realType) m (Y:lmodType R) NY Z S C f lambda delta:
  (0<= @critical_eta R m Y NY Z S C f lambda delta)%E.
Proof.
apply:(extended_supremum_nonnegative (@critical_eta_laws R m Y NY Z S C f lambda delta)).
exists 0;split;[by left|exact:lexx].
Qed.

(** Source for [critical_zeta_nonnegative]: the adjoined zero makes ζ
    nonnegative, 3.4.2(4), p. 311, including an empty tangent family. *)
Lemma critical_zeta_nonnegative (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta:
  (0<= @critical_zeta R m Y NY hNY Z S C f lambda delta)%E.
Proof.
apply:(extended_supremum_nonnegative (@critical_zeta_laws R m Y NY hNY Z S C f lambda delta)).
exists 0;split;[by left|exact:lexx].
Qed.

(** Source for [critical_eta_constant]: supporting constant-map case
    of η in 3.4.2(4), pp. 310–311. Every original increment has zero
    numerator, so the supremum is zero at every cutoff. *)
Lemma critical_eta_constant (R:realType) m (Y:lmodType R) (NY:Y->R)
    (hNY:is_real_norm NY) Z S C (c:Y) lambda delta:
  @critical_eta R m Y NY Z S C (fun _=>c) lambda delta=0%E.
Proof.
apply/eqP;rewrite eq_le;apply/andP;split;last exact:critical_eta_nonnegative.
apply:(extended_supremum_least (@critical_eta_laws R m Y NY Z S C (fun _=>c) lambda delta)).
move=>q [->|[x [a [_ [_ [_ [_ ->]]]]]]];first exact:lexx.
by rewrite subrr (real_seminorm_zero hNY.1) mul0r.
Qed.
