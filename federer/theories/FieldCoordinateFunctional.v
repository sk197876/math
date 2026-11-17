(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: actual coordinate functionals over the original
    field. The finite-coordinate space and basis are reused. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [field_coordinate_functional]: the original
    coordinate x_i as a linear functional, 3.4.8(1), p. 326. *)
Definition field_coordinate_functional (K:fieldType) n (i:'I_n):Hom (coordinate_space K n) K^o.
Proof.
apply:(@HomMap K (coordinate_space K n) K^o (fun x=>x i)).
apply/asboolP=>c x y;by rewrite !ffunE.
Defined.
Arguments field_coordinate_functional {K n} i.
