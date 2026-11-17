(** Federer (1969), 3.4.11, p. 338:
    existence and uniqueness of the original cusp
    after its independent equation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations AnalyticCuspUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_cusp_exists]: the original
    polynomial equation defines the plane set printed
    in 3.4.11, p. 338. *)
Theorem analytic_cusp_exists (R:realType):
  exists S:set (R_n R 2),is_analytic_cusp S.
Proof. exists [set v:R_n R 2|(v ord0)^+3=(v ord_max)^+2];by move=>v. Qed.

(** Source for [analytic_cusp_unique]: the independent
    original membership law determines the cusp uniquely,
    supporting opaque use in 3.4.11, p. 338. *)
Theorem analytic_cusp_unique (R:realType) (S T:set (R_n R 2)):
  is_analytic_cusp S ->is_analytic_cusp T ->S=T.
Proof. move=>hS hT;apply:funext=>v;apply:propext;by rewrite hS hT. Qed.
