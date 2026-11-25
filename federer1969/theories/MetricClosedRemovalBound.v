(** Federer (1969), 2.10.22, p. 185: replace finitely many open
    neighbourhoods by their compact sets, using reciprocal distance
    neighbourhoods and regular continuity below. This supporting general
    metric lemma permits any closed set, including the empty set. The
    measure theory is the project's 2.1.5(1), not an external theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology.
From Federer Require Import MetricOpenThickening MeasureUP MeasureBasic RegularMeasureUP
  RegularMeasureContinuity ExtendedFiniteIncreasingBounds ArchimedeanReciprocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_closed_reciprocal_neighborhoods]: supporting
    shrinking neighbourhood identity in 2.10.22,
    p. 185. The empty closed set is included,
    without assigning it a finite distance profile. *)
Lemma metric_closed_reciprocal_neighborhoods (R : realType) (X : metricType R) (K : set X) :
  closed K -> (\bigcap_n metric_open_thickening K (n.+1%:R : R)^-1)=K.
Proof.
move=> hK; apply/seteqP; split.
- move=> x hx; apply: hK=> V hV.
  have [e he hb] := (metricType_numDomainType.nbhs_mdistP x V).1 hV.
  have [n hn] := real_reciprocal_below he.
  have [a ha hax] := hx n Logic.I.
  exists a; split=> //; apply: hb; change (is_true (mdist x a<e)); rewrite (metric_sym x a).
  exact: lt_trans hax hn.
- move=> x hx n _; apply: metric_open_thickening_includes hx.
  by rewrite invr_gt0 ltr0n.
Qed.

(** Source for [regular_measure_closed_removal_bound]: supporting
    finite-neighbourhood removal in 2.10.22,
    p. 185. The auxiliary set T and target B
    need not be measurable; the fixed addend is
    nonnegative and may have an infinite value. *)
Theorem regular_measure_closed_removal_bound (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (B K T : set X) (p s : \bar R) :
  is_measure mu -> is_regular_measure mu -> closed K -> (0<=p)%E ->
  (forall U, open U -> K `<=` U -> (mu (B `\` (U `|` T))+p<=s)%E) ->
  (mu (B `\` (K `|` T))+p<=s)%E.
Proof.
move=> hm hr hK hp hbound.
pose U n := metric_open_thickening K (n.+1%:R : R)^-1.
have hU n : open (U n) := metric_open_thickening_open K _.
have hKU n : K `<=` U n.
  apply: metric_open_thickening_includes; by rewrite invr_gt0 ltr0n.
have hdec n m (hnm : (n<=m)%N) : U m `<=` U n.
  move=> x [a ha hax]; exists a=> //.
  have hn : (0<n.+1%:R :> R) by rewrite ltr0n.
  have hmp : (0<m.+1%:R :> R) by rewrite ltr0n.
  have hinv : (m.+1%:R^-1<=n.+1%:R^-1 :> R) by rewrite (lef_pV2 hmp hn) ler_nat.
  exact: lt_le_trans hax hinv.
pose A n := B `\` (U n `|` T).
have hinc n m (hnm : (n<=m)%N) : A n `<=` A m.
  move=> x [hx hxU]; split=> //; move=> [hxm|hxT]; apply: hxU.
  - left; exact: hdec n m hnm x hxm.
  - by right.
have hlim := regular_measure_continuity_below hm hr hinc.
have htotal := @extended_nonnegative_limit_add_bound R (fun n=>mu (A n)) (mu (\bigcup_n A n)) p s
  (fun n=>measure_nonnegative hm (A n)) hlim.2 hp (fun n=>hbound (U n) (hU n) (hKU n)).
have heq : (\bigcup_n A n)=B `\` (K `|` T).
  apply/seteqP; split.
  - move=> x [n _ [hx hxU]]; split=> //; move=> [hxK|hxT]; apply: hxU.
    + left; exact: hKU n x hxK.
    + by right.
  - move=> x [hx hxKT].
    have hnot : ~K x by move=> hxK; apply: hxKT; by left.
    have [n hn] : exists n, ~U n x.
      apply: contrapT=> hnone; apply: hnot.
      rewrite -(metric_closed_reciprocal_neighborhoods hK); move=> n _.
      apply: contrapT=> hn; apply: hnone; by exists n.
    exists n=> //; split=> //; move=> [hxU|hxT]; [exact: hn hxU|apply: hxKT; by right].
by rewrite heq in htotal.
Qed.
