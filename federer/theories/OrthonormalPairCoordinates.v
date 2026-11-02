(** Federer (1969), 1.7.3, p. 29: the alternating-form normal form is
    immediate in dimension at most two. This spells out the two-dimensional
    coordinate step used by that assertion. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP OrthonormalFamilies
  InnerFiniteSynthesis LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthonormal_pair_coordinates]: Federer
    1.7.3, p. 29, supporting expansion in an orthonormal basis
    of a two-dimensional space. *)
Theorem orthonormal_pair_coordinates (R : rcfType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (e : 'I_2 -> V) (he : is_basis e) (ho : orthonormal_family B e) x :
  x = B x (e ord0) *: e ord0 + B x (e ord_max) *: e ord_max.
Proof.
have h := @inner_finite_synthesis_coordinates R V B hB 2 e he ho x.
rewrite /inner_finite_synthesis big_ord_recr big_ord1 in h.
have hi : widen_ord (leqnSn 1) ord0 = (ord0 : 'I_2) by exact: val_inj.
rewrite hi !inner_coordinateE in h; exact: esym h.
Qed.
