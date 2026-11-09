(** Federer (1969), 3.4.5, p. 319: opaque analytic
    germ operations exposed only through their original representative laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermOperationsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type AnalyticGermsSignature.
(** Source for [add]: analytic germ addition, 3.4.5, p. 319. *)
Parameter add:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X),
  analytic_germ_space hNX a->analytic_germ_space hNX a->analytic_germ_space hNX a.
(** Source for [mul]: analytic germ multiplication, 3.4.5, p. 319. *)
Parameter mul:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X),
  analytic_germ_space hNX a->analytic_germ_space hNX a->analytic_germ_space hNX a.
(** Source for [opp]: analytic germ negation, 3.4.5, p. 319. *)
Parameter opp:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X),
  analytic_germ_space hNX a->analytic_germ_space hNX a.
(** Source for [laws]: the representative equations for the
    induced ring operations, 3.4.5, p. 319. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X),
  is_analytic_germ_operations (@add R X NX hNX a) (@mul R X NX hNX a) (@opp R X NX hNX a).
End AnalyticGermsSignature.
Module AnalyticGerms:AnalyticGermsSignature.
(** Source for [add]: private addition witness from proved
    existence, 3.4.5, p. 319. *)
Definition add (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (@analytic_germ_operations_exists R X NX hNX a)).
(** Source for [mul]: private multiplication witness from the
    same existence proof, 3.4.5, p. 319. *)
Definition mul (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (projT2 (cid (@analytic_germ_operations_exists R X NX hNX a)))).
(** Source for [opp]: private negation witness from the
    same existence proof, 3.4.5, p. 319. *)
Definition opp (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X):=
  projT1 (cid (projT2 (cid (projT2 (cid (@analytic_germ_operations_exists R X NX hNX a)))))).
(** Source for [laws]: selected operations satisfy the
    independent original equations, 3.4.5, p. 319. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX) (a:X):
  is_analytic_germ_operations (@add R X NX hNX a) (@mul R X NX hNX a) (@opp R X NX hNX a).
Proof.
exact:(projT2 (cid (projT2 (cid (projT2 (cid (@analytic_germ_operations_exists R X NX hNX a))))))).
Qed.
End AnalyticGerms.
