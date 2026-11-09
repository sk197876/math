(** Federer (1969), 3.4.5, p. 319: a
    countable compact cover of a metric space gives a
    countable dense set. This supporting topology argument
    chooses finite reciprocal-scale nets inside each compact. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import FiniteSeparatedMetricNetUP MetricClosedBalls ExtendedRealReciprocalBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [countable_compact_cover_separable]: the
    separability inference in 3.4.5, p. 319.
    All finite nets lie in the actual compact members;
    their countable union meets every nonempty open set. *)
Theorem countable_compact_cover_separable (R:realType) (X:metricType R)
    (x0:X) (I:countType) (K:I->set X):
  (forall i,compact (K i)) ->(forall x,exists i,K i x) ->
  exists D:set X,countable D /\dense D.
Proof.
move=>hK hCover.
have hex i k:exists B:{fset X},is_finite_separated_metric_net (K i) ((k.+1)%:R^-1:R) B.
  apply:(@compact_finite_separated_metric_net_exists R X x0 (K i) _ (hK i)).
  by rewrite invr_gt0 ltr0n.
pose B i k:=projT1 (cid (hex i k)).
have hB i k:=projT2 (cid (hex i k)).
pose D:set X:=\bigcup_(i in @setT I) \bigcup_k [set` B i k].
exists D;split.
- apply:bigcup_countable;first exact:(countableP setT).
  move=>i _;apply:bigcup_countable;first exact:(countableP setT).
  move=>k _;apply:finite_set_countable;exact:finite_fset.
- move=>U [x hx] hOpen.
  have hNear:nbhs x U by rewrite openE in hOpen;exact:hOpen x hx.
  have [r hr hBall]:=proj1 (metricType_numDomainType.nbhs_mdistP x U) hNear.
  have [k hSmall]:=@positive_reciprocal_nat_small R r hr.
  have [i hi]:=hCover x.
  have [b hb hClose]:=(@finite_metric_net_covers R X (K i) ((k.+1)%:R^-1:R) (B i k) (hB i k)) x hi.
  exists b;split.
  + apply:hBall.
    change (is_true (mdist x b<r)).
    rewrite metric_sym;exact:le_lt_trans hClose hSmall.
  + exists i;first exact:Logic.I.
    exists k;first exact:Logic.I.
    exact:hb.
Qed.
