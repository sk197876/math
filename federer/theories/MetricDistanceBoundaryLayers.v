(** Federer (1969), 3.2.42, printed p. 278:
    identify the printed strict positive distance strips and
    closed inner cores with actual open-ball tubes, closure
    and interior. These identities use only independent
    metric distance laws, without any selected nearest point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import MetricSetDistanceUP MetricSetDistanceBasic
  MetricSetDistanceClosure MetricOpenThickening MetricOpenThickeningClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_positive_distance_strip]: direct outer
    strip in Federer 3.2.42, p. 278. The zero-distance locus
    is the actual closure of the original source. No source
    measurability, boundedness or closedness is added. *)
Lemma metric_positive_distance_strip (R:realType) (X:metricType R)
    (S:set X) (d:X->R) (r:R):
  is_metric_set_distance S d ->
  [set x | 0<d x<r]=metric_open_thickening S r `\` closure S.
Proof.
move=>hD; rewrite (@metric_open_thickening_distance R X S d r hD).
apply/seteqP; split=>x.
- move=>/andP[hPos hSmall]; split; first exact hSmall.
  move=>hClosure.
  have hZero: d x=0:=(metric_set_distance_zero_closure hD x).2 hClosure.
  by rewrite hZero ltxx in hPos.
- move=>[hSmall hOutside]; apply/andP; split; last exact hSmall.
  rewrite lt_neqAle (metric_set_distance_nonnegative hD x) andbT.
  apply/negP=>/eqP hZero; apply:hOutside.
  exact:(metric_set_distance_zero_closure hD x).1 (esym hZero).
Qed.

(** Source for [metric_distance_inner_core]: direct set T in
    the second proof paragraph of Federer 3.2.42, p. 278.
    A non-strict positive-distance core is the complement
    of the actual strict tube of the original complement. *)
Lemma metric_distance_inner_core (R:realType) (X:metricType R)
    (S:set X) (d:X->R) (r:R):
  is_metric_set_distance (~`S) d ->
  [set x | r<=d x]=~`metric_open_thickening (~`S) r.
Proof.
move=>hD; rewrite (@metric_open_thickening_distance R X (~`S) d r hD).
apply/seteqP; split=>x.
- move=>hLarge hSmall; have hBad:=lt_le_trans hSmall hLarge.
  by rewrite ltxx in hBad.
- move=>hNoSmall; change (is_true (r<=d x)); rewrite leNgt; apply/negP; exact hNoSmall.
Qed.

(** Source for [metric_complement_positive_strip]: direct inner
    strip in Federer 3.2.42, p. 278. The positive-distance
    locus of the original complement is exactly Int(S).
    The core cutoff remains non-strict at radius r. *)
Lemma metric_complement_positive_strip (R:realType) (X:metricType R)
    (S:set X) (d:X->R) (r:R):
  is_metric_set_distance (~`S) d ->
  [set x | 0<d x<r]=interior S `\` (~`metric_open_thickening (~`S) r).
Proof.
move=>hD.
have hComplement:interior S=~`closure (~`S).
  rewrite -interiorC setCK; reflexivity.
rewrite (@metric_positive_distance_strip R X (~`S) d r hD) hComplement.
apply/seteqP; split=>x.
- move=>[hTube hNoClosure]; split; first exact hNoClosure.
  by move=>hNoTube; exact:hNoTube hTube.
- move=>[hNoClosure hNotNoTube]; split; last exact hNoClosure.
  exact:contrapT hNotNoTube.
Qed.
