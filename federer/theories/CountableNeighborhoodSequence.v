(** Federer (1969), 2.4.17, p. 90: passing from sequence limits to
    continuity on the exponent domain. This supporting general-topology
    existence proof constructs shrinking neighborhoods from an abstract
    countable open base. Later arguments use only the stated neighborhood
    laws. This is background, not a separately printed book claim. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [countable_base_neighborhood_sequence_exists]: supporting
    first-countability consequence for the sequential continuity argument of
    Federer 2.4.17, p. 90 The concrete finite intersections are local
    witnesses of these abstract laws. *)
Lemma countable_base_neighborhood_sequence_exists (T : topologicalType)
    (U : nat -> set T) (hU : is_countable_open_base U) (x : T) :
  exists V : nat -> set T,
    (forall n, open (V n)) /\ (forall n, V n x) /\
    (forall B, nbhs x B -> exists k, forall n, (k <= n)%N -> V n `<=` B).
Proof.
pose V := fix V (n : nat) : set T :=
  if n is m.+1 then V m `&` (if asbool (U m x) then U m else setT) else setT.
have hVo n : open (V n).
  elim: n=> [|n ih]; first exact: openT.
  apply: openI ih _; case: ifP=> h; first exact: (@countable_base_open T U hU n).
  exact: openT.
have hVx n : V n x.
  elim: n=> [|n ih] //=; split=> //; case: ifP=> h //; by move/asboolP: h.
have hVU n i : (i < n)%N -> U i x -> V n `<=` U i.
  elim: n=> [|n ih] //= hi hix y [hy hz].
  have [hin|hin] := eqVneq i n.
  - have he : asbool (U i x) by apply/asboolP.
    by move: hz; rewrite -hin he.
  - have hil : (i < n)%N by move: hi; rewrite ltnS leq_eqVlt (negbTE hin).
    exact: (ih hil hix y hy).
exists V; split=> //; split=> // B hB.
rewrite nbhsE in hB; have [O [hOo hOx] hOB] := hB.
have [i [hix hiO]] := @countable_base_refines T U hU O hOo x hOx.
exists i.+1=> n hn y hy; apply: hOB; apply: hiO; exact: (hVU n i hn hix y hy).
Qed.
