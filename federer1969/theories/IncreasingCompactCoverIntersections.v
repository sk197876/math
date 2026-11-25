(** Supporting Federer (1969), 3.4.8(5), p. 328:
    finite intersections of the original compact-countable-union
    descriptions remain countable compact unions. No closure under
    differences is asserted. *)
From mathcomp Require Import all_boot all_order boolp classical_sets topology.
From Federer Require Import IncreasingCompactCoverUP IncreasingCompactCoverLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [increasing_compact_cover_finite_intersection]: supporting
    the original finite reduction-set intersections in Federer
    3.4.8(5), p. 328. Compact Hausdorff ambient space also covers
    the empty intersection; a common index covers each finite family. *)
Theorem increasing_compact_cover_finite_intersection (T:topologicalType)
    (I:finType) (D:set I) (S:I->set T) (K:I->nat->set T):
  compact [set:T] ->hausdorff_space T ->
  (forall i,is_increasing_compact_cover (S i) (K i)) ->
  is_increasing_compact_cover [set x:T|forall i,D i ->S i x]
    (fun n=>[set x:T|forall i,D i ->K i n x]).
Proof.
move=>hCompact hHausdorff hK;constructor.
- move=>n.
  have hClosed:closed [set x:T|forall i,D i ->K i n x].
    change (closed (\bigcap_(i in D) K i n)).
    apply:closed_bigI=>i _;apply:compact_closed;first exact:hHausdorff.
    exact:increasing_compact_cover_compact (hK i) n.
  have hh:=compact_closedI hCompact hClosed.
  by rewrite setTI in hh.
- move=>n x hx i hi;exact:(@increasing_compact_cover_contained T _ _ (hK i) n x (hx i hi)).
- move=>m n hMN x hx i hi.
  exact:(@increasing_compact_cover_monotone T _ _ (hK i) m n hMN x (hx i hi)).
- move=>x hx.
  have hEach i:exists n,D i ->K i n x.
    case:(pselect (D i))=>hD.
    + have [n hn]:=increasing_compact_cover_covers (hK i) (hx i hD).
      exists n;by move=>_.
    + exists 0%N;by move=>h;case:(hD h).
  have [N hN]:=choice hEach.
  exists (\max_i N i)=>i hD.
  exact:(@increasing_compact_cover_monotone T _ _ (hK i) (N i) (\max_j N j)
    (leq_bigmax i) x (hN i hD)).
Qed.
