(** Federer (1969), 2.4.17, p. 90: continuity deduced from sequence limits.
    This supporting general-topology criterion is proved from countable-base
    laws; it imposes no metrizability assumption on the target. The local
    choices prove existence of a contradicting sequence and do not add any
    project axiom. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import CountableOpenBaseUP CountableNeighborhoodSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_sequential_relative_limit]: supporting
    passage from limits of sequences in a subset to neighborhoods relative
    to that subset, for Federer 2.4.17, p. 90 The limit point need not
    belong to the subset, so closure endpoints are included. *)
Theorem countable_base_sequential_relative_limit (T Z : topologicalType)
    (U : nat -> set T) (hU : is_countable_open_base U)
    (A : set T) (f : T -> Z) (x : T) :
  (forall p : nat -> T, (forall n, A (p n)) -> p @ \oo --> x -> (f \o p) @ \oo --> f x) ->
  forall B, nbhs (f x) B -> exists W, nbhs x W /\ forall y, A y -> W y -> B (f y).
Proof.
move=> hseq B hB.
have [he|he] := pselect (exists W, nbhs x W /\ forall y, A y -> W y -> B (f y)); first exact he.
exfalso; have [V [hVo [hVx hVr]]] := @countable_base_neighborhood_sequence_exists T U hU x.
have hbad n : exists y, A y /\ V n y /\ ~ B (f y).
  have [hh|hh] := pselect (exists y, A y /\ V n y /\ ~ B (f y)); first exact hh.
  exfalso; apply: he; exists (V n); split.
  - have ho := hVo n; rewrite openE in ho; exact: ho x (hVx n).
  - move=> y hy hVy; apply: contrapT=> hn; apply: hh; exists y; by split=> //; split.
pose p n := projT1 (cid (hbad n)).
have hp n : A (p n) /\ V n (p n) /\ ~ B (f (p n)) := projT2 (cid (hbad n)).
have hlim : p @ \oo --> x.
  move=> C hC; have [k hk] := hVr C hC; exists k; first exact Logic.I.
  move=> n hn; exact: hk n hn (p n) (hp n).2.1.
have hh := hseq p (fun n => (hp n).1) hlim.
have [k _ hk] := hh B hB.
apply: (hp k).2.2; exact: hk k (leqnn k).
Qed.
