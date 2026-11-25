(** Federer (1969), 3.4.7, p. 325: finite
    free modules used to prove the submodule assertion.
    The coordinate maps split off the last scalar coordinate.
    These are supporting linear-algebra constructions, not extra
    hypotheses of the analytic-ring theorem. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import InfiniteSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [ring_coordinate_last]: the last coordinate
    in the finite-module induction supporting 3.4.7, p. 325. *)
Definition ring_coordinate_last (A:nzRingType) n (x:{ffun 'I_n.+1->A^o}):A^o:=x ord_max.

(** Source for [ring_coordinate_last_linear]: linearity
    of the last-coordinate map supporting 3.4.7, p. 325. *)
Lemma ring_coordinate_last_linear (A:nzRingType) n:linear (@ring_coordinate_last A n).
Proof. by move=>a x y;rewrite /ring_coordinate_last !ffunE. Qed.
HB.instance Definition _ (A:nzRingType) n:=GRing.isLinear.Build A
  {ffun 'I_n.+1->A^o} A^o *:%R (@ring_coordinate_last A n) (@ring_coordinate_last_linear A n).

(** Source for [ring_coordinate_zero_extend]: adjoining
    a zero final coordinate in the module induction of
    3.4.7, p. 325. The construction supplies a local
    linear map; it does not define the generated module. *)
Definition ring_coordinate_zero_extend (A:nzRingType) n (x:{ffun 'I_n->A^o}):{ffun 'I_n.+1->A^o}:=
  [ffun j=>ordinal_snoc x 0 j].

(** Source for [ring_coordinate_zero_extend_linear]: the
    zero-coordinate inclusion is linear, supporting 3.4.7, p. 325. *)
Lemma ring_coordinate_zero_extend_linear (A:nzRingType) n:
  linear (@ring_coordinate_zero_extend A n).
Proof.
move=>a x y;apply/ffunP=>j;case:(unliftP ord_max j)=>[u ->|->].
- by rewrite /ring_coordinate_zero_extend !ffunE !ordinal_snoc_lift !ffunE.
- by rewrite /ring_coordinate_zero_extend !ffunE !ordinal_snoc_last scaler0 addr0.
Qed.
HB.instance Definition _ (A:nzRingType) n:=GRing.isLinear.Build A
  {ffun 'I_n->A^o} {ffun 'I_n.+1->A^o} *:%R (@ring_coordinate_zero_extend A n)
  (@ring_coordinate_zero_extend_linear A n).

(** Source for [ring_coordinate_last_kernel]: a vector
    with zero last coordinate comes from the preceding
    coordinate module, supporting 3.4.7, p. 325. *)
Lemma ring_coordinate_last_kernel (A:nzRingType) n (x:{ffun 'I_n.+1->A^o}):
  ring_coordinate_last x = 0 ->exists y:{ffun 'I_n->A^o},ring_coordinate_zero_extend y = x.
Proof.
move=>h;exists [ffun j=>x (lift ord_max j)];apply/ffunP=>j.
case:(unliftP ord_max j)=>[u ->|->].
- by rewrite /ring_coordinate_zero_extend !ffunE ordinal_snoc_lift ffunE.
- by rewrite /ring_coordinate_zero_extend ffunE ordinal_snoc_last;exact:esym h.
Qed.
