(** Federer (1969), 2.5.9, p. 100: the norm-one linear extension to total
    L1. The erratum p. 2, book p. 100 lines 21–24, fixes the total-domain
    convention and the positive-density argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeSeminormUP TotalScalarLpUP TotalScalarLpFiniteSeminorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_dominated_lone_extension]: abstract specification
    of mu_1 in the proof of Federer 2.5.9, p. 100.
    Linearity, agreement on L, and the unit L1 bound are laws
    that an existence proof must establish, not project axioms. *)
Definition is_dominated_lone_extension (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A S : (X -> R) -> R) :=
  is_linear_functional_on_functions (total_scalar_lp mu 1) S /\
  (forall f, L f -> S f=A f) /\
  (forall f, total_scalar_lp mu 1 f -> (`|S f| <= finite_total_scalar_lp_norm mu 1 f)%R).
