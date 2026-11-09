(** Federer (1969), 3.3.2, pp. 287–288: the open cone is
    exhausted by compact subsets before applying 2.1.3(4).
    This supporting general metric lemma needs only compact closed
    balls and measurability of closed sets, not Borel regularity
    or local finiteness of the outer measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MetricClosedBalls MetricOpenClosedCover
  LipschitzFunctionCompact NullFibresProperSource CountableFamilySequence
  SetSequenceDisjointification MeasureUP MeasureBasic MeasureContinuityBelow
  ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_open_compact_inner_strict]: supporting
    the increasing compact exhaustion in Federer 3.3.2,
    pp. 287–288. Every finite strict lower bound on the mass
    of an open set is exceeded by an actual compact subset.
    Infinite mass and empty open sets are retained. *)
Theorem structure_open_compact_inner_strict (R:realType) (X:metricType R)
    (mu:set X->\bar R) (a:X) (U:set X) (b:R):
  is_measure mu ->metric_boundedly_compact X ->
  (forall C,closed C->measure_measurable mu C) ->
  open U ->b%:E<mu U ->
  exists K,compact K /\ K `<=` U /\ b%:E<mu K.
Proof.
move=>hm hX hClosed hU hLower.
have [C [hC hUnion]]:=metric_open_countable_closed_cover hU.
pose D (p:nat*nat):=C p.1 `&` metric_closed_ball a (p.2%:R:R).
have hD p:compact (D p).
  rewrite /D setIC; exact:(compact_closedI (hX a _ (@ler0n R p.2)) (hC p.1).1).
have hDU:(\bigcup_p D p)=U.
  apply/seteqP; split.
  - move=>x [p _ [hx _]]; exact:((hC p.1).2 x hx).
  - move=>x hx; have hCx:(\bigcup_i C i) x by rewrite -hUnion.
    have [i _ hi]:=hCx.
    have [j _ hj]:=@metric_natural_closed_balls_cover R X a x Logic.I.
    exists (i,j)=>//; by split.
have [E [hE hEU]]:=@countable_family_as_sequence X
  [the choiceType of ((nat*nat)%type:Type)] setT D (countableP _).
have hEc i:compact (E i).
  case:(hE i)=>[->|[p [_ ->]]]; [exact:compact0|exact:hD].
pose K i:=set_sequence_prefix E i.
have hKc i:compact (K i).
  elim:i=>[|i IH]; first by rewrite /K set_sequence_prefix_zero; exact:compact0.
  rewrite /K set_sequence_prefix_succ; exact:(compactU IH (hEc i)).
have hKU:(\bigcup_i K i)=U.
  rewrite -hDU -hEU; apply/seteqP; split.
  - move=>x [i _ [j _ hx]]; by exists j.
  - move=>x [i _ hx]; exists i.+1=>//; exists i=>//; exact:ltnSn.
have hKm i:measure_measurable mu (K i).
  exact:(hClosed _ (compact_closed (@metric_hausdorff R X) (hKc i))).
have hKi i j (hij:(i<=j)%N):K i `<=` K j.
  exact:(set_sequence_prefix_mono hij).
have hLimit:=@measure_continuity_below R X mu hm K hKm hKi.
case:(pselect (exists i,b%:E<mu (K i)))=>[[i hi]|hNone].
- exists (K i); split; first exact:hKc.
  split; last exact:hi.
  move=>x hx; rewrite -hKU; by exists i.
- exfalso; have hUpper:mu U<=b%:E.
    rewrite -hKU; apply:(extended_order_limit_upper_bound hLimit.2)=>i.
    rewrite leNgt; apply/negP=>hi; apply:hNone; by exists i.
  by have:=lt_le_trans hLower hUpper; rewrite ltxx.
Qed.
