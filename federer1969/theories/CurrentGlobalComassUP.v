(** Federer (1969), 4.1.7, p. 358: the
    comass of a differential form on U
    is the supremum of its pointwise comasses.
    The independent least-upper-bound laws retain
    infinite values and the empty domain. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP GrassmannAbbreviations AlternatingForms CurrentCoefficientNorms
  ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [current_global_comass_values]: the
    pointwise value set in the first displayed
    mass definition of Federer 4.1.7, p. 358.
    This definition requires no field regularity. *)
Definition current_global_comass_values (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m):set R:=
  [set a|exists x:R_n R n,U x /\@current_form_comass R h2 n m (phi x)=a].

(** Source for [is_current_global_comass]: the
    original global comass is the least extended
    upper bound of all pointwise comasses,
    Federer 4.1.7, p. 358. *)
Definition is_current_global_comass (R:realType) (h2:(1+1:R)!=0) n m
    (U:set (R_n R n)) (phi:R_n R n->A_m (R_n R n) R^o m) (c: \bar R):Prop:=
  is_extended_supremum (@current_global_comass_values R h2 n m U phi) c.
