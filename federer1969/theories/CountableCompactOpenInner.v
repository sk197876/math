(** Federer (1969), 4.1.7, p. 358: inner
    regularity of the locally finite norm-density
    measure on the original open U. This supporting
    lemma combines the metric closed exhaustion of
    2.2.1, p. 60, with the compact exhaustion
    already used in 4.1.1, p. 344. It does
    not require closed balls in U to be compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MetricOpenClosedCover CountableFamilySequence
  SetSequenceDisjointification MeasureUP MeasureBasic MeasureContinuityBelow
  ExtendedRealLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [countable_compact_open_inner_strict]:
    compact inner approximation on the original open
    domain, supporting Federer 4.1.7, p. 358,
    by 2.2.1–2.2.2, pp. 60–61. The given
    compact cover retains empty domains and infinite
    open-set masses. Only closed-set measurability is
    needed; local finiteness is not assumed here. *)
Theorem countable_compact_open_inner_strict (R:realType) (X:metricType R)
    (mu:set X->\bar R) (C:nat->set X) (V:set X) (b:R):
  is_measure mu ->(forall j,compact (C j)) ->setT `<=` \bigcup_j C j ->
  (forall F,closed F ->measure_measurable mu F) ->
  open V ->b%:E<mu V ->
  exists K,compact K /\ K `<=` V /\ b%:E<mu K.
Proof.
move=>hm hC hCover hClosed hV hLower.
have [F [hF hFV]]:=metric_open_countable_closed_cover hV.
pose D (p:nat*nat):=F p.1 `&` C p.2.
have hD p:compact (D p).
  rewrite /D setIC; exact:(compact_closedI (hC p.2) (hF p.1).1).
have hDV:(\bigcup_p D p)=V.
  apply/seteqP; split.
  - move=>x [p _ [hx _]]; exact:(hF p.1).2 x hx.
  - move=>x hx.
    have [i _ hi]:(\bigcup_i F i) x by rewrite -hFV.
    have [j _ hj]:=hCover x Logic.I.
    exists (i,j)=>//; by split.
have [E [hE hEU]]:=@countable_family_as_sequence X
  [the choiceType of ((nat*nat)%type:Type)] setT D (countableP _).
have hEc i:compact (E i).
  case:(hE i)=>[->|[p [_ ->]]]; [exact:compact0|exact:hD].
pose K i:=set_sequence_prefix E i.
have hKc i:compact (K i).
  elim:i=>[|i IH]; first by rewrite /K set_sequence_prefix_zero; exact:compact0.
  rewrite /K set_sequence_prefix_succ; exact:(compactU IH (hEc i)).
have hKV:(\bigcup_i K i)=V.
  rewrite -hDV -hEU; apply/seteqP; split.
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
  move=>x hx; rewrite -hKV; by exists i.
- exfalso; have hUpper:mu V<=b%:E.
    rewrite -hKV; apply:(extended_order_limit_upper_bound hLimit.2)=>i.
    rewrite leNgt; apply/negP=>hi; apply:hNone; by exists i.
  by have:=lt_le_trans hLower hUpper; rewrite ltxx.
Qed.
