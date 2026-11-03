(** Federer (1969), 3.2.41, printed p. 278:
    measurable original sets follow from the compact case by
    inner approximation, with zero and infinite factor volumes
    treated directly through translates of the original sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanVolumeRootSum EuclideanBrunnMinkowskiBoundary FiniteMeasureBrunnMinkowski
  CompactBrunnMinkowski MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [measurable_brunn_minkowski]: direct measurable-set
    approximation step of Federer 3.2.41, p. 278. Neither
    finite factor volume nor measurability of the actual sum
    is added. The actual original nonempty factors are retained. *)
Theorem measurable_brunn_minkowski (R:realType) n
    (A B:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<n)%N ->
  measure_measurable (@euclidean_lebesgue_measure R n) A ->
  measure_measurable (@euclidean_lebesgue_measure R n) B ->
  A !=set0 ->B !=set0 ->euclidean_volume_root_sum_bound A B.
Proof.
move=> hn hA hB hANe hBNe.
pose mu:=@euclidean_lebesgue_measure R n.
have hm:=euclidean_lebesgue_is_measure R n.
case hMA:(mu A)=>[a| |].
- have ha:0<=a.
    have h:(0<=mu A)%E:=measure_nonnegative hm A; by rewrite hMA lee_fin in h.
  case hMB:(mu B)=>[b| |].
  + have hb:0<=b.
      have h:(0<=mu B)%E:=measure_nonnegative hm B; by rewrite hMB lee_fin in h.
    have [ha0|ha0]:=eqVneq a 0.
    * apply:(@brunn_minkowski_zero_left R n A B hn hANe).
      by rewrite /mu in hMA; rewrite hMA ha0.
    have [hb0|hb0]:=eqVneq b 0.
    * apply:(@euclidean_volume_root_sum_symmetric R n A B).2.
      apply:(@brunn_minkowski_zero_left R n B A hn hBNe).
      by rewrite /mu in hMB; rewrite hMB hb0.
    have hap:0<a by rewrite lt_neqAle eq_sym ha0 ha.
    have hbp:0<b by rewrite lt_neqAle eq_sym hb0 hb.
    apply:(@finite_positive_brunn_minkowski_compact_reduction R n A B a b hn).
    * move=> K L hK hL hKNe hLNe.
      exact:(@compact_brunn_minkowski R n K L hn hK hL hKNe hLNe).
    * exact hA.
    * exact hB.
    * exact hMA.
    * exact hMB.
    * exact hap.
    * exact hbp.
  + apply:(@euclidean_volume_root_sum_symmetric R n A B).2.
    exact:(@brunn_minkowski_infinite_left R n B A hANe hMB).
  + have h:(0<=mu B)%E:=measure_nonnegative hm B.
    by rewrite hMB leNgt ltNyr in h.
- exact:(@brunn_minkowski_infinite_left R n A B hBNe hMA).
- have h:(0<=mu A)%E:=measure_nonnegative hm A.
  by rewrite hMA leNgt ltNyr in h.
Qed.
