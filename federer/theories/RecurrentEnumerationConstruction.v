(** Private existence proof for the recurrent sequence used in Federer
    (1969), 2.8.2, p. 142 Enumerate P times the naturals. A second
    coordinate larger than those in any given finite prefix forces a later
    occurrence of each first coordinate. This spells out the set-theoretic
    choice; it is not attributed as a separate argument to either source.
    Edition details: RecurrentEnumerationUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality.
From Federer Require Import CountableDefaultEnumeration RecurrentEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope nat_scope.

(** Source for [recurrent_enumeration_exists]: supporting
    existence of B_j in Federer 2.8.2, p. 142. A nonempty
    family is necessary for a total sequence of eligible terms;
    the theorem's empty-family case is treated by empty-target
    adequacy instead. No infinitude of P is assumed. *)
Theorem recurrent_enumeration_exists (J : choiceType) (P : set J) :
  countable P -> (exists j, P j) ->
  exists u : nat -> J, is_recurrent_enumeration P u.
Proof.
move=> hc [j0 hj0].
have hp : countable (P `*` (@setT nat)).
  apply: countableX=> //; exact: countableP.
have [u [hu hs]] := @countable_default_enumeration [the choiceType of (J*nat)%type]
  (P `*` (@setT nat)) (j0,0%N) hp.
exists (fun n => (u n).1); constructor.
- move=> n; case: (hu n)=> [[hj _]|he]; first exact hj.
  by rewrite he.
- move=> j hj N.
  pose M := (\max_(i < N) (u i).2)%N.
  have [n hn] := hs (j,M.+1) (conj hj Logic.I).
  have hN : N <= n.
    rewrite leqNgt; apply/negP=> hlt.
    have hle := @leq_bigmax 'I_N (fun i : 'I_N => (u i).2) (Ordinal hlt).
    have hle' : (u n).2 <= M := hle.
    have hbad : M < M by move: hle'; rewrite hn /=.
    by rewrite ltnn in hbad.
  exists n; split=> //; by rewrite hn.
Qed.
