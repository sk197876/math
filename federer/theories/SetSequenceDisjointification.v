(** Federer (1969), 2.1.3, pp. 55-56: finite initial unions and disjoint
    differences in the proofs of (3),(4),(2). These are set-theoretic
    supporting constructions, not additional measure axioms. Natural indices
    start at zero. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [set_sequence_prefix]: Federer 2.1.3,
    p. 55, B_j in the proof of (3), and p. 56, B_j in the proof
    of (2); the union of the first n members, empty at n zero. *)
Definition set_sequence_prefix (I : Type) (F : nat -> set I) n :=
  \bigcup_(k in [set k | (k < n)%N]) F k.

(** Source for [set_sequence_prefix_zero]: Federer 2.1.3,
    p. 55; supporting empty-prefix convention for finite induction. *)
Lemma set_sequence_prefix_zero (I : Type) (F : nat -> set I) :
  set_sequence_prefix F 0 = set0.
Proof. by apply/seteqP; split=> [x [k hk _]|x []]; rewrite /= ltn0 in hk. Qed.

(** Source for [set_sequence_prefix_succ]: Federer 2.1.3,
    p. 55, finite-union induction in the proof of (3). *)
Lemma set_sequence_prefix_succ (I : Type) (F : nat -> set I) n :
  set_sequence_prefix F n.+1 = set_sequence_prefix F n `|` F n.
Proof.
apply/seteqP; split.
- move=> x [k hk hx]; move: hk; rewrite /= ltnS leq_eqVlt=> /orP[/eqP hkn|hk].
  + right; by rewrite -hkn.
  + left; by exists k.
- move=> x [[k hk hx]|hx].
  + exists k=> //; exact: ltn_trans hk (ltnSn n).
  + exists n=> //; exact: ltnSn.
Qed.

(** Source for [set_sequence_prefix_mono]: Federer 2.1.3,
    p. 56, the finite unions B_j form an increasing sequence. *)
Lemma set_sequence_prefix_mono (I : Type) (F : nat -> set I) n m :
  (n <= m)%N -> set_sequence_prefix F n `<=` set_sequence_prefix F m.
Proof.
move=> hnm x [k hk hx]; exists k=> //; exact: leq_trans hk hnm.
Qed.

(** Source for [set_sequence_disjointify]: Federer 2.1.3,
    p. 55, disjoint increments in the proof of (4). Supporting
    generalisation to an arbitrary sequence: subtract every earlier
    member. For an increasing sequence this is exactly the printed
    first member followed by successive differences. *)
Definition set_sequence_disjointify (I : Type) (F : nat -> set I) n :=
  F n `\` set_sequence_prefix F n.

(** Source for [set_sequence_disjointify_disjoint]: Federer
    2.1.3, p. 55, supporting disjointness of the successive increments. *)
Lemma set_sequence_disjointify_disjoint (I : Type) (F : nat -> set I) n m :
  n != m -> forall x, set_sequence_disjointify F n x ->
    set_sequence_disjointify F m x -> False.
Proof.
move=> hne x [hn hpn] [hm hpm]; have [hnm|hmn|he] := ltngtP n m.
- apply: hpm; by exists n.
- apply: hpn; by exists m.
- by move: hne; rewrite he eqxx.
Qed.

(** Source for [set_sequence_disjointify_prefix]: Federer
    2.1.3, p. 55, the first j disjoint increments have union B_j.
    This supporting identity also holds before assuming the original
    sequence increasing. *)
Lemma set_sequence_disjointify_prefix (I : Type) (F : nat -> set I) n :
  set_sequence_prefix (set_sequence_disjointify F) n = set_sequence_prefix F n.
Proof.
elim: n=> [|n IH]; first by rewrite !set_sequence_prefix_zero.
rewrite !set_sequence_prefix_succ IH /set_sequence_disjointify.
apply/seteqP; split.
- by move=> x [hx|[hx _]]; [left|right].
- move=> x [hx|hx]; first by left.
  case: (pselect (set_sequence_prefix F n x))=> hp; first by left.
  right; by split.
Qed.

(** Source for [set_sequence_disjointify_union]: Federer
    2.1.3, p. 55, the disjoint increments exhaust the same union. *)
Lemma set_sequence_disjointify_union (I : Type) (F : nat -> set I) :
  (\bigcup_n set_sequence_disjointify F n) = \bigcup_n F n.
Proof.
apply/seteqP; split.
- move=> x [n _ [hx _]]; by exists n.
- move=> x [n _ hx].
  have hp : set_sequence_prefix F n.+1 x by exists n=> //; exact: ltnSn.
  rewrite -set_sequence_disjointify_prefix in hp.
  have [k hk hxk] := hp; by exists k.
Qed.

(** Source for [set_sequence_prefix_increasing]: Federer
    2.1.3, p. 55, proof of (4): for an increasing sequence, the
    first n+1 members have union the member with index n. *)
Lemma set_sequence_prefix_increasing (I : Type) (F : nat -> set I) :
  (forall n m, (n <= m)%N -> F n `<=` F m) ->
  forall n, set_sequence_prefix F n.+1 = F n.
Proof.
move=> h n; apply/seteqP; split.
- move=> x [k hk hx]; apply: (h k n _ x hx); by move: hk; rewrite /= ltnS.
- move=> x hx; exists n=> //; exact: ltnSn.
Qed.
