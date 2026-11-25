(** Federer (1969), 3.4.7, p. 325: a
    finitely generated module over a Noetherian ring has
    finitely generated submodules. The module property is
    specified independently of the proof of this assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import RingSubmoduleUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_noetherian_ring_module]: every submodule
    has finite generators, the module property used for
    M intersect I in 3.4.7, p. 325. *)
Definition is_noetherian_ring_module (A:nzRingType) (V:lmodType A):Prop:=
  forall M:set V,is_ring_submodule M ->is_finitely_generated_ring_submodule M.
