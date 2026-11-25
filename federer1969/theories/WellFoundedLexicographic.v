(** General set-theoretic background for Federer (1969), 2.5.11, p. 102: the
    cardinal arithmetic (card Y_1) times aleph-one equals aleph-one. Kelley,
    General Topology, Appendix, Definitions 175-176 and Theorems 177-180,
    pp. 279-280 (Dover 2017 reprint of 1955), treat products of infinite
    cardinals by a well ordering of pairs. Here the lexicographic product of
    two well-founded relations is proved well founded; it orders the pairs
    along which a transfinite selection is made. *)
From Corelib Require Import Init.Wf.
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [lexicographic_relation]: supporting order on pairs
    for the transfinite argument behind Federer 2.5.11, p. 102:
    compare the first coordinates, and the second coordinates
    only when the first coordinates agree. *)
Definition lexicographic_relation (A B : Type) (r1 : A -> A -> Prop)
    (r2 : B -> B -> Prop) (p q : A * B) : Prop :=
  r1 p.1 q.1 \/ (p.1 = q.1 /\ r2 p.2 q.2).

(** Source for [lexicographic_well_founded]: supporting background
    for Federer 2.5.11, p. 102: the lexicographic product of two
    well-founded relations is well founded. Kelley, Appendix,
    Theorem 128, pp. 270-271, supplies the recursion background.
    The proof is a nested accessibility induction. *)
Lemma lexicographic_well_founded (A B : Type) (r1 : A -> A -> Prop)
    (r2 : B -> B -> Prop) :
  well_founded r1 -> well_founded r2 -> well_founded (lexicographic_relation r1 r2).
Proof.
move=> h1 h2 [a b].
elim: (h1 a) b => {}a _ iha b.
elim: (h2 b) => {}b _ ihb.
constructor=> [[a' b']]; rewrite /lexicographic_relation /=; move=> [hr|[-> hr]].
- exact: iha.
- exact: ihb.
Qed.

(** Source for [well_founded_subrelation]: supporting background
    for Federer 2.5.11, p. 102: a relation contained in a
    well-founded relation is well founded. *)
Lemma well_founded_subrelation (A : Type) (r s : A -> A -> Prop) :
  (forall x y, s x y -> r x y) -> well_founded r -> well_founded s.
Proof.
move=> hsub hr x; elim: (hr x) => {}x _ ih.
constructor=> y hy; exact: ih (hsub _ _ hy).
Qed.
