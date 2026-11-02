(** Federer (1969), 3.1.12, p. 224:
    the disjoint-ball volume comparison behind the
    cardinal estimate. Finiteness is proved from compactness
    and uniform separation before using finite additivity. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal topology ring.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanClosedBallCompact EuclideanClosedBallVolume EuclideanBallVolume
  CompactSeparatedCardinality MetricClosedBalls MeasureUP MeasureBasic
  MeasureFiniteAdditivity BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.

Section BallPacking.
Variable R : realType.
Variable m : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m)).
Variable S : set X.
Variable h : X->R.
Variables x : X.
Variables l H : R.
Hypothesis hl : 0<l.
Hypothesis hH : 0<=H.
Hypothesis hsmall : forall s, S s -> l<=h s.
Hypothesis hcontain : forall s, S s ->
  metric_closed_ball s (h s) `<=` metric_closed_ball x H.
Hypothesis hdisjoint : forall s t, S s -> S t -> s!=t ->
  forall y, metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.

(** Source for [euclidean_uniform_ball_packing_finite]:
    finiteness of S_x implicit in the volume sum in
    Federer 3.1.12, p. 224. Uniformly positive
    disjoint balls have uniformly separated centers in
    the compact containing ball. *)
Lemma euclidean_uniform_ball_packing_finite : finite_set S.
Proof.
have hS : S `<=` metric_closed_ball x H.
  move=> s hs.
  have hss : metric_closed_ball s (h s) s.
    change (is_true (mdist s s<=h s)); rewrite mdistxx.
    exact (le_trans (ltW hl) (@hsmall s hs)).
  exact (@hcontain s hs s hss).
have hsep s t : S s -> S t -> s<>t -> l<=mdist s t.
  move=> hs ht hst.
  case: (leP l (mdist s t))=>[hgood|hbad]; first by [].
  exfalso.
  have hsball : metric_closed_ball s (h s) t.
    exact: ltW (lt_le_trans hbad (@hsmall s hs)).
  have htball : metric_closed_ball t (h t) t.
    change (is_true (mdist t t<=h t)); rewrite mdistxx.
    exact: le_trans (ltW hl) (@hsmall t ht).
  have hne : s!=t by apply/eqP.
  exact (@hdisjoint s t hs ht hne t hsball htball).
have [n [_ hn]] := @compact_separated_cardinal_bound R
  [the metricType R of X] x (metric_closed_ball x H) l
  (@euclidean_closed_metric_ball_compact R m x H) hl.
exact: card_le_finite (hn S hS hsep) (@finite_finset _ (@setT 'I_n)).
Qed.

(** Source for [euclidean_uniform_ball_packing_bound]:
    cardinal times the least ball volume is at most
    the containing-ball volume, Federer 3.1.12, p. 224.
    Cancelling the positive unit-ball volume leaves
    card(S) l^m <= H^m. Dimension zero and the empty
    family are included. *)
Theorem euclidean_uniform_ball_packing_bound :
  ((#|` fset_set S|)%:R : R)* l^+m<=H^+m.
Proof.
have hfin := euclidean_uniform_ball_packing_finite.
pose F := fset_set S.
have hFS s : s \in F -> S s.
  by rewrite /F in_fset_set //; exact: set_mem.
pose mu := @euclidean_lebesgue_measure R m.
pose hm := euclidean_lebesgue_is_measure R m.
pose a := euclidean_unit_ball_volume R m.
have ha : 0<a := (euclidean_unit_ball_volumeE R m).2.
have hmeas s : measure_measurable mu (metric_closed_ball s (h s)).
  apply: (borel_regular_borel_measurable hm (euclidean_lebesgue_borel_regular R m)).
  apply: closed_borel_set; exact: metric_closed_ball_closed.
have hdis s t : s \in F -> t \in F -> s!=t -> forall y,
    metric_closed_ball s (h s) y -> metric_closed_ball t (h t) y -> False.
  move=> hs ht; exact (@hdisjoint s t (hFS s hs) (hFS t ht)).
have hadd := @measure_finite_disjoint_additivity R [the choiceType of X]
  [the choiceType of X] mu hm (fun s=>metric_closed_ball s (h s)) F
  (fun s _=>hmeas s) hdis.
have hsub : (\bigcup_(s in [set` F]) metric_closed_ball s (h s)) `<=`
    metric_closed_ball x H.
  move=> y [s hs hy]; exact (@hcontain s (hFS s hs) y hy).
have hmass := measure_mono hm hsub.
rewrite /mu in hadd.
rewrite hadd (@euclidean_closed_ball_normalized_volume R m x H hH) in hmass.
have hvalues : (\sum_(s <- F) mu (metric_closed_ball s (h s)))%E=
    (\sum_(s <- F) a*(h s)^+m)%:E.
  rewrite -sumEFin; apply: eq_big_seq=> s hs.
  exact (@euclidean_closed_ball_normalized_volume R m s (h s)
    (le_trans (ltW hl) (@hsmall s (hFS s hs)))).
rewrite /mu in hvalues.
rewrite hvalues lee_fin in hmass.
have hterms : (\sum_(s <- F) a* l^+m)<=\sum_(s <- F) a*(h s)^+m.
  rewrite !big_seq; apply: ler_sum=> s hs; apply: ler_wpM2l; first exact: ltW ha.
  apply: lerXn2r; [exact: ltW hl| |exact: @hsmall s (hFS s hs)].
  exact: le_trans (ltW hl) (@hsmall s (hFS s hs)).
have hconst : (\sum_(s <- F) a* l^+m)=((#|` F|)%:R : R)*(a* l^+m).
  by rewrite big_seq_fsetE /= sumr_const -cardfE [RHS]mulr_natl.
have hb := le_trans hterms hmass; rewrite hconst in hb.
have hid : ((#|` F|)%:R : R)*(a* l^+m)=a*(((#|` F|)%:R : R)* l^+m) by ring.
by rewrite hid (ler_pM2l ha) in hb.
Qed.
End BallPacking.
