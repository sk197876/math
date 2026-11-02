(** Finite-prefix identities for the binary-cylinder counterexample to
    Federer (1969), 2.3.8, p. 78. These are set-theoretic facts supporting
    the local covering construction, not separately stated claims in the
    book. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import BinarySequenceCylinders.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [binary_sequence_prefix]: the first n coordinates
    of a binary sequence, supporting the example for Federer
    2.3.8, p. 78. *)
Definition binary_sequence_prefix n (x : binary_sequence_space) : n.-tuple bool :=
  Tuple (introT eqP (size_mkseq x n)).

(** Source for [binary_sequence_in_prefix]: every sequence lies
    in its own length-n cylinder, supporting the cylinder cover
    for Federer 2.3.8, p. 78. *)
Lemma binary_sequence_in_prefix n (x : binary_sequence_space) :
  binary_cylinder (binary_sequence_prefix n x) x.
Proof.
move=> k hk; change (x k = nth false (mkseq x n) k).
by rewrite nth_mkseq //; move: hk; rewrite size_tuple.
Qed.

(** Source for [binary_cylinder_prefix_subset]: extending a
    word shrinks its cylinder, supporting the refinement proof for
    the local counterexample in Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_prefix_subset w v : prefix w v ->
  binary_cylinder v `<=` binary_cylinder w.
Proof.
move=> /prefixP [z ->] x hx k hk.
have hk' : k < size (w++z) by rewrite size_cat; exact: leq_trans hk (leq_addr _ _).
have h := hx k hk'; by rewrite nth_cat hk in h.
Qed.

(** Source for [binary_cylinder_meet_prefix]: intersecting
    cylinders have compatible prefixes; a shorter word prefixes
    the longer word. Supporting finite splitting for the local
    example in Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_meet_prefix w v x : size w <= size v ->
  binary_cylinder w x -> binary_cylinder v x -> prefix w v.
Proof.
move=> hw hcw hcv; have hmin : minn (size w) (size v) = size w by apply/minn_idPl.
 rewrite prefixE; apply/eqP; apply: (@eq_from_nth _ false).
- by rewrite size_take_min hmin.
- move=> k hk; have hkw : k < size w by move: hk; rewrite size_take_min hmin.
  rewrite nth_take // -(hcw k hkw).
  exact: esym (hcv k (leq_trans hkw hw)).
Qed.

(** Source for [binary_cylinder_finite_refinement]: all length-n
    extensions of w cover its cylinder when size w is at most
    n. Supporting the local example for Federer 2.3.8, p. 78. *)
Lemma binary_cylinder_finite_refinement n w : size w <= n ->
  binary_cylinder w `<=` \bigcup_(u in [set u : n.-tuple bool | prefix w u]) binary_cylinder u.
Proof.
move=> hw x hx; exists (binary_sequence_prefix n x); last exact: binary_sequence_in_prefix.
have hlen : size w <= size (binary_sequence_prefix n x) by rewrite size_tuple.
exact (@binary_cylinder_meet_prefix w (binary_sequence_prefix n x) x hlen hx (@binary_sequence_in_prefix n x)).
Qed.
