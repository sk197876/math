(** Federer (1969), 2.2.12, p. 69, last paragraph: sufficiently long finite
    coordinate bounds force a sequence into every open neighborhood W of the
    compact box K. We prove the finite-prefix version of the printed
    positive- distance argument: a finite cover of K by open cylinders gives
    a common prefix length, and truncation to ones provides the point of K
    to which that length is applied. This keeps the compactness and
    truncation steps explicit. Source context: SequenceBoxes.v. *)
From mathcomp Require Import all_boot finmap boolp classical_sets reals topology.
From Federer Require Import SequenceSpace SequenceProductTopology SequenceBoxes
  SequenceFiniteBounds CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [compact_box_prefix_neighborhood]: supporting
    uniform neighborhood estimate for K in Federer 2.2.12,
    p. 69. This is the finite-prefix counterpart of the
    printed positive distance from K to the complement of W;
    it uses the same truncation and the exact sequence topology. *)
Theorem compact_box_prefix_neighborhood (R : realType) (b : nat -> nat)
    (W : set (positive_sequence_space R)) :
  open W -> sequence_coordinate_box b `<=` W ->
  exists k, sequence_box_prefix b k `<=` W.
Proof.
move=> ho hKW.
pose P (p : positive_sequence_space R * nat) := positive_sequence_prefix p.1 p.2.
pose D := [set p : positive_sequence_space R * nat |
  sequence_coordinate_box b p.1 /\ P p `<=` W].
have hcover : sequence_coordinate_box b `<=` \bigcup_(p in D) P p.
  move=> n hn.
  have hnb : nbhs n W by rewrite openE in ho; exact: ho n (hKW n hn).
  have [k hk] := proj1 (positive_sequence_product_neighborhoods n W) hnb.
  exists (n,k); first by split.
  by move=> i hi.
have hop p : D p -> open (P p) by move=> _; exact: sequence_finite_prefix_open.
have [F hF hc] := compact_open_finite_cover (@sequence_coordinate_box_compact R b) hop hcover.
pose k := \max_(p <- F) p.2.
have hk p : p \in F -> (p.2 <= k)%N.
  move=> hp; apply: leq_bigmax_seq; first exact: hp.
  by [].
exists k=> n hn.
pose z := sequence_box_truncate n k.
have hz : sequence_coordinate_box b z := sequence_box_truncate_member hn.
have [p hp hpz] := hc z hz.
have hd : D p := set_mem (hF p hp).
apply: hd.2=> i hi.
have hik : (i < k)%N := leq_trans hi (hk p hp).
have hzEq := @sequence_box_truncate_prefix R n k i hik.
rewrite -hzEq; exact: hpz i hi.
Qed.
