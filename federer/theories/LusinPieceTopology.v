(** General-topology steps of Federer (1969), 2.3.5, p. 77: finite disjoint
    closed pieces are relatively open in their union. Source context:
    LusinPiecesUP.v. This is the reason the printed finite-step
    approximations are continuous. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP LusinPiecesUP SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [closed_sequence_prefix]: supporting finite-union
    closedness of D_i in Federer 2.3.5, pp. 76–77. *)
Lemma closed_sequence_prefix (X : topologicalType) (E : nat -> set X) N :
  (forall n, (n < N)%N -> closed (E n)) -> closed (set_sequence_prefix E N).
Proof.
elim: N=> [|N IH] hE; first by rewrite set_sequence_prefix_zero; exact: closed0.
rewrite set_sequence_prefix_succ; apply: closedU.
- apply: IH=> n hn; apply: hE; exact: ltn_trans hn (ltnSn N).
- apply: hE; exact: ltnSn.
Qed.

(** Source for [lusin_piece_relative_neighborhood]: supporting
    relative openness of a finite closed piece in Federer 2.3.5,
    p. 77. Removing all the other pieces gives an ambient open
    neighborhood, on which the finite-step approximation is constant. *)
Lemma lusin_piece_relative_neighborhood (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (A : set X)
    (f : partial_function X Y) eta delta N E :
  is_lusin_piece_system mu A f eta delta N E ->
  forall n x, (n < N)%N -> E n x -> exists V, open V /\ V x /\
    forall z, V z -> set_sequence_prefix E N z -> E n z.
Proof.
move=> hs n x hn hx.
pose F k := if k == n then set0 else E k.
have hF k : (k < N)%N -> closed (F k).
  move=> hk; rewrite /F; case: ifP=> _; first exact: closed0.
  exact: (@lusin_piece_closed R X Y mu A f eta delta N E hs k hk).
exists (~` set_sequence_prefix F N); split.
- exact: closed_openC (closed_sequence_prefix hF).
- split.
  + move=> [k hk hfk]; move: hfk; rewrite /F; case: ifP=> hkn // hkx.
    have hneq : k != n by rewrite hkn.
    exact (@lusin_piece_disjoint R X Y mu A f eta delta N E hs k n hk hn hneq x hkx hx).
  + move=> z hv [k hk hek]; case: (eqVneq k n)=> hkn; first by rewrite -hkn.
    exfalso; apply: hv; exists k=> //; by rewrite /F (negPf hkn).
Qed.
