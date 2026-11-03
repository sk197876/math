(** Federer (1969), 3.2.41, printed p. 278, first proof
    sentence: the finite disjoint-box theorem bounds every
    small tube of the actual sum of the original compact sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra ring.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions VectorSetSum MetricOpenThickening EuclideanVectorSumTubes
  CompactOpenBoxApproximation FiniteOpenBoxBrunnMinkowski EuclideanVolumeRootSum
  ExtendedPositivePower MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_sum_tube_root_bound]: supporting actual
    approximation inequality in Federer 3.2.41, p. 278.
    Open grid boxes retain at least each original compact volume.
    Their actual paired sum lies in the prescribed tube; monotonicity
    of outer volume and its positive root gives this bound at
    every positive real radius. No tube finiteness is assumed. *)
Theorem compact_sum_tube_root_bound (R:realType) n
    (K L:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  (0<n)%N ->compact K ->compact L ->K !=set0 ->L !=set0 ->0<r ->
  (extended_positive_power (@euclidean_lebesgue_measure R n K) (n%:R)^-1+
    extended_positive_power (@euclidean_lebesgue_measure R n L) (n%:R)^-1<=
    extended_positive_power (@euclidean_lebesgue_measure R n
      (metric_open_thickening (vector_set_sum K L) r)) (n%:R)^-1)%E.
Proof.
move=> hn hK hL hKNe hLNe hr.
have hHalf:(0<r/2)%R by rewrite divr_gt0 // ltr0n.
have hDouble:(r/2+r/2=r)%R by field.
have [I [a [b [G [hG [hGNe [hKMass hGNear]]]]]]]:=
  @compact_open_box_approximation_exists R n K (r/2)%R hK hKNe hHalf.
have [J [c [d [H [hH [hHNe [hLMass hHNear]]]]]]]:=
  @compact_open_box_approximation_exists R n L (r/2)%R hL hLNe hHalf.
have hBox:=@finite_open_box_brunn_minkowski R n hn I J a b c d G H hG hH hGNe hHNe.
rewrite /euclidean_volume_root_sum_bound in hBox.
have hp:(0<(n%:R:R)^-1)%R by rewrite invr_gt0 ltr0n.
have hm:=euclidean_lebesgue_is_measure R n.
have hRootK:=@extended_positive_power_monotone R _ _ (n%:R)^-1
  (measure_nonnegative hm K) hKMass hp.
have hRootL:=@extended_positive_power_monotone R _ _ (n%:R)^-1
  (measure_nonnegative hm L) hLMass hp.
have hMiddle:=le_trans (leeD hRootK hRootL) hBox.
have hSub:vector_set_sum (\bigcup_i G i) (\bigcup_j H j) `<=`
    metric_open_thickening (vector_set_sum K L) r.
  move=> z /vector_set_sum_membership [x [y [hx [hy ->]]]].
  have hPair:vector_set_sum (metric_open_thickening K (r/2)%R)
      (metric_open_thickening L (r/2)%R) (x+y).
    exact:vector_set_sum_contains (hGNear x hx) (hHNear y hy).
  have h:=@euclidean_vector_sum_open_tubes R n K L (r/2)%R (r/2)%R (x+y) hPair.
  by rewrite hDouble in h.
have hTarget:=@extended_positive_power_monotone R _ _ (n%:R)^-1
  (measure_nonnegative hm (vector_set_sum (\bigcup_i G i) (\bigcup_j H j)))
  (@measure_mono R _ _ hm _ _ hSub) hp.
exact:le_trans hMiddle hTarget.
Qed.
