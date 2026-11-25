(** Supporting algebra for Federer (1969), 3.4.8(8),
    p. 329: surjective coefficient maps preserve
    the original simple generated ring. Compare
    the exact generator predicates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [generated_ring_surjective_coefficients]: the
    original coefficient carrier may be replaced
    by an equivalent carrier in the simple
    extension of 3.4.8(8), p. 329. *)
Theorem generated_ring_surjective_coefficients (A B C:comNzRingType)
  (original:{rmorphism A->C}) (factor:{rmorphism A->B}) (scalar:{rmorphism B->C}) (z:C):
  (forall a:A,scalar (factor a) = original a) ->(forall b:B,exists a:A,factor a = b) ->
  is_generated_commutative_subring (fun y:C=>y = z \/exists b:B,y = scalar b) setT ->
  is_generated_commutative_subring (fun y:C=>y = z \/exists a:A,y = original a) setT.
Proof.
move=>hTriangle hOnto hGenerated.
have hSets:(fun y:C=>y = z \/exists b:B,y = scalar b) =
    (fun y:C=>y = z \/exists a:A,y = original a).
  apply:funext=>y;apply:propext;split.
  - move=>[hZ|[b hB]];first by left.
    have [a hA]:=hOnto b;right;exists a;by rewrite -hTriangle hA.
  - move=>[hZ|[a hA]];first by left.
    right;exists (factor a);by rewrite hTriangle.
by rewrite -hSets.
Qed.
