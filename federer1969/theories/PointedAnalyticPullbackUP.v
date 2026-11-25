(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    coordinate maps induce actual maps of analytic germs
    at their stated centres. The original representative
    equation specifies the map before existence or selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_pointed_analytic_germ_pullback]: the
    original pullback of every representative is composition
    with the actual coordinate map, supporting 3.4.8(1),(5),
    pp. 326, 328. Both original centres are stated
    explicitly; no representative or implementation is selected. *)
Definition is_pointed_analytic_germ_pullback (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (u:X->Y)
    (P:analytic_germ_space hNY b->analytic_germ_space hNX a):Prop:=
  forall f:analytic_representative_type hNY b,
    exists g:analytic_representative_type hNX a,
      P (analytic_germ f)=analytic_germ g /\
      forall x,analytic_representative_value g x=analytic_representative_value f (u x).
