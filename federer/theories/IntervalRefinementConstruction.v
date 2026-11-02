(** Federer (1969), 2.2.9, p. 65: prove the interval refinement with
    countable loss. The two reflected scalar ladders supply intervals
    indexed by boolean-natural pairs; a bijective enumeration preserves
    their disjointness. Source context: NoIsolatedPoints.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals topology.
From Federer Require Import RealMetricBackground RealOpenIntervals
  IntervalLadderUP IntervalLadderSealed IntervalLadderPieces
  CountablyInfiniteEnumeration IntervalRefinementUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_interval_refinement_exists]: supporting interval choice
    for Federer 2.2.9, p. 65. The scalar witnesses stay sealed; only their
    abstract order, gap and smallness laws are used. *)
Theorem real_interval_refinement_exists (R : realType) (a b e : R) :
  a < b -> 0 < e -> exists F,
    is_real_interval_refinement (real_open_interval a b) e F.
Proof.
move=> hab he.
have hh : 0 < (b-a)/2 by rewrite divr_gt0 ?subr_gt0 ?ltr0n.
pose d := @IntervalLadder.value R ((b-a)/2) e hh he.
have hd : is_small_interval_ladder ((b-a)/2) e d := @IntervalLadder.laws R _ _ hh he.
have hi : injective (fun n : nat => (true,n)) by move=> i j; case.
have hcnt : countable (@setT (bool * nat)) by exact: countableP.
have [encode [decode [henc hdec]]] := countably_infinite_enumeration hcnt hi.
pose F n := interval_ladder_endpoints a b d (decode n).
exists F; constructor.
- move=> n; exact: (@interval_ladder_piece_ordered R a b e d hd (decode n)).
- move=> n x hx.
  have [ha hb] := @interval_ladder_piece_inside R a b e d hd (decode n) hab.
  have [hl hu] := real_open_interval_closure_bounds hx.
  split; [exact: lt_le_trans ha hl | exact: le_lt_trans hu hb].
- move=> n; exact: (@interval_ladder_piece_length R a b e d hd (decode n)).
- move=> i j hij; apply: (@interval_ladder_pieces_disjoint R a b e d hd (decode i) (decode j)).
  move=> heq; apply: hij; have heqnat := congr1 encode heq; by rewrite !hdec in heqnat.
- apply: sub_countable _ (interval_ladder_endpoint_countable a b d).
  apply: subset_card_le=> x [hx hn]; apply: contrapT=> hne; apply: hn.
  have [p hp] := @interval_ladder_pieces_cover_off_endpoints R a b e d hd x hx hne.
  exists (encode p)=> //; by rewrite /F henc.
Qed.
