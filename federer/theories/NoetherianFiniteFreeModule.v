(** Federer (1969), 3.4.7, p. 325: finite
    free modules over a Noetherian ring are Noetherian.
    The proof expands the finite-module appeal in the book
    by induction on the number of scalar coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions.
From Federer Require Import CommutativeIdealUP RingSubmoduleUP NoetherianModuleUP
  NoetherianScalarModule RingCoordinateMaps NoetherianModuleExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [noetherian_finite_free_module]: supporting
    finite-module assertion of 3.4.7, p. 325. Every
    submodule of the actual finite scalar-coordinate module
    has finite generators, including the zero-coordinate case. *)
Theorem noetherian_finite_free_module (A:comNzRingType):
  is_noetherian_commutative_ring A ->forall n,
  is_noetherian_ring_module [the lmodType A of {ffun 'I_n->A^o}].
Proof.
move=>hA;elim=>[|n ih].
- move=>N hN;exists [::];constructor;first exact:hN.
  + move=>x;change (x \in [::] ->N x);by rewrite in_nil.
  + move=>S hS hEmpty x hx.
    have hx0:x = 0 by apply/ffunP=>j;have:=ltn_ord j;rewrite ltn0.
    rewrite hx0;exact:ring_submodule_zero hS.
- exact:(@noetherian_module_extension A
    [the lmodType A of {ffun 'I_n->A^o}]
    [the lmodType A of {ffun 'I_n.+1->A^o}] A^o
    (GRing.Linear.clone _ _ _ _ (@ring_coordinate_zero_extend A n) _)
    (GRing.Linear.clone _ _ _ _ (@ring_coordinate_last A n) _)
    (@ring_coordinate_last_kernel A n) ih (noetherian_scalar_module hA)).
Qed.
