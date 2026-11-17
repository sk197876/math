(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),
    p. 326: the original scalar coordinate evaluations are linear
    over their original field. This connects the existing finite
    coordinate space to the original dual coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom FiniteCoordinates.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [field_scalar_coordinate_map]: evaluation of one
    original coordinate, supporting 3.4.12, p. 339. *)
Definition field_scalar_coordinate_map (K:fieldType) n (i:'I_n):Hom (coordinate_space K n) K^o.
Proof.
apply:(@HomMap K (coordinate_space K n) K^o (fun v=>v i)).
apply/asboolP=>c v w;by rewrite !ffunE.
Defined.
