(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate germs gamma_j are specified
    by every actual representative of omega_j.
    The published correction at book p. 326 line 3
    places omega_j in the dual one-form space.
    The project's proved one-form identification exposes
    these covectors as Hom(X,R). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP AnalyticGermUP AnalyticGermRing AnalyticGermRepresentatives.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_analytic_coordinate_germs]: every
    actual linear-coordinate representative gives the
    original gamma_j, 3.4.8(1), p. 326, with
    the published dual-space correction. No image,
    depth or dimension conclusion is included. *)
Definition is_analytic_coordinate_germs (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (omega:'I_n->Hom X R^o)
  (gamma:'I_n->@analytic_germ_ring R X NX hNX 0):Prop:=
  forall j (f:@analytic_representative_type R X NX hNX 0),
    (forall x,analytic_representative_value f x = omega j x) ->analytic_germ f = gamma j.
