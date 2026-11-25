(** Federer (1969), 3.4.2(4), pp. 310–311: opaque oscillation suprema. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient GrassmannAbbreviations RealNormUP
  CriticalOscillationUP CriticalOscillationExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CriticalOscillationSignature.
(** Source for [eta]: the function oscillation supremum of
    3.4.2(4), pp. 310–311, exposed through its defining laws. *)
Parameter eta:forall (R:realType) m (Y:lmodType R),
  (Y->R)->subspace (R_n R m)->set (R_n R m)->set (R_n R m)->
  (R_n R m->Y)->R->R->\bar R.
(** Source for [eta_laws]: the independent least-upper-bound
    specification of η in 3.4.2(4), pp. 310–311. *)
Parameter eta_laws:forall (R:realType) m (Y:lmodType R) NY Z S C f lambda delta,
  is_critical_function_oscillation NY Z S C f lambda delta
    (@eta R m Y NY Z S C f lambda delta).
(** Source for [zeta]: the tangent-derivative oscillation supremum
    of 3.4.2(4), p. 311, with the original relative derivative. *)
Parameter zeta:forall (R:realType) m (Y:lmodType R) (NY:Y->R),
  is_real_norm NY->subspace (R_n R m)->set (R_n R m)->set (R_n R m)->
  (R_n R m->Y)->R->R->\bar R.
(** Source for [zeta_laws]: the independent least-upper-bound
    specification of ζ in 3.4.2(4), p. 311. *)
Parameter zeta_laws:forall (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta,
  is_critical_tangent_oscillation hNY Z S C f lambda delta
    (@zeta R m Y NY hNY Z S C f lambda delta).
End CriticalOscillationSignature.
Module CriticalOscillation:CriticalOscillationSignature.
(** Source for [eta]: a private existence witness for the supremum
    in 3.4.2(4), pp. 310–311, hidden by the signature. *)
Definition eta (R:realType) m (Y:lmodType R) NY Z S C f lambda delta:=
  projT1 (cid (@critical_function_oscillation_exists R m Y NY Z S C f lambda delta)).
(** Source for [eta_laws]: the witness satisfies the independent
    supremum laws of 3.4.2(4), pp. 310–311. *)
Lemma eta_laws (R:realType) m (Y:lmodType R) NY Z S C f lambda delta:
  is_critical_function_oscillation NY Z S C f lambda delta
    (@eta R m Y NY Z S C f lambda delta).
Proof. exact:(projT2 (cid (@critical_function_oscillation_exists R m Y NY Z S C f lambda delta))). Qed.
(** Source for [zeta]: a private existence witness for the supremum
    in 3.4.2(4), p. 311, hidden by the signature. *)
Definition zeta (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta:=
  projT1 (cid (@critical_tangent_oscillation_exists R m Y NY hNY Z S C f lambda delta)).
(** Source for [zeta_laws]: the witness satisfies the independent
    supremum laws of 3.4.2(4), p. 311. *)
Lemma zeta_laws (R:realType) m (Y:lmodType R) NY hNY Z S C f lambda delta:
  is_critical_tangent_oscillation hNY Z S C f lambda delta
    (@zeta R m Y NY hNY Z S C f lambda delta).
Proof. exact:(projT2 (cid (@critical_tangent_oscillation_exists R m Y NY hNY Z S C f lambda delta))). Qed.
End CriticalOscillation.
