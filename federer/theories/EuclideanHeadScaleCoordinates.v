(** Actual diagonal-coordinate laws of Federer (1969),
    2.7.16(1), p. 135, supporting the
    section comparison in 3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_head_scale_tail]: supporting
    diagonal-coordinate connection for the coefficient comparison
    in Federer 3.2.45, pp. 279–280.
    The actual diagonal map of 2.7.16,
    p. 135, scales the scalar head
    and fixes every tail coordinate. The
    tail may be empty and the scalar
    may vanish or be negative. *)
Lemma euclidean_head_scale_tail (R : realType) n (a : R) (x : R_n R n.+1) :
  coordinate_tail (@euclidean_diagonal_map R n.+1 (fun i => if i==ord0 then a else 1) x)=
    coordinate_tail x.
Proof.
apply/ffunP=> i.
by rewrite /coordinate_tail /euclidean_diagonal_map /euclidean_diagonal !ffunE lift_eqF mul1r.
Qed.

(** Source for [euclidean_head_scale_head]: supporting
    exact scalar-head equation for the same
    original diagonal map, Federer 2.7.16,
    p. 135, used in 3.2.45,
    pp. 279–280. No sign or
    nonzero restriction is added to the scalar. *)
Lemma euclidean_head_scale_head (R : realType) n (a : R) (x : R_n R n.+1) :
  coordinate_head (@euclidean_diagonal_map R n.+1 (fun i => if i==ord0 then a else 1) x)=
    a*coordinate_head x.
Proof.
by rewrite /coordinate_head /euclidean_diagonal_map /euclidean_diagonal !ffunE eqxx.
Qed.
