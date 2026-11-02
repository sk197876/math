(** Federer (1969), 2.10.45, printed p. 203, final double covering sum: a
    common finite positive coefficient factors out before taking the
    covering infimum on the second factor. This supporting comparison
    normalises a measure by that coefficient and applies the existing
    abstract infimum comparison. No attainment of a minimum covering cost is
    asserted. Source context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology MeasureUP FiniteMeasureScaling
  MetricDiameter MetricScaleEnvelopeUP MetricScaleMeasureBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_bounded_by_scaled_metric_envelope]: supporting
    passage from the common coefficient times
    covering costs to the cutoff infimum in
    2.10.45, p. 203. The coefficient
    is finite and strictly positive; targets
    and envelope values may be infinite. *)
Theorem measure_bounded_by_scaled_metric_envelope (R : realType) (X : metricType R)
    (J : choiceType) (S : J -> set X) (cost : J -> \bar R)
    delta (nu mu : set X -> \bar R) (K : R) :
  (0<K)%R -> is_metric_scale_envelope S cost delta nu -> is_measure mu ->
  (forall j, extended_metric_diameter (S j)<=delta -> mu (S j)<=K%:E*cost j) ->
    forall A, mu A<=K%:E*nu A.
Proof.
move=> hK hn hm hgen A.
have hne : (K!=0)%R := lt0r_neq0 hK.
have hinv : (0<=K^-1)%R by rewrite invr_ge0; exact: ltW hK.
have hinvE : 0<=K^-1%:E by rewrite lee_fin.
have hs : is_measure (fun B=>K^-1%:E*mu B) := @finite_scale_is_measure R X mu hm K^-1 hinv.
have hj j (hd : extended_metric_diameter (S j)<=delta) : K^-1%:E*mu (S j)<=cost j.
  have hh := lee_wpmul2l hinvE (hgen j hd).
  by rewrite muleA -EFinM mulVf // mul1e in hh.
have hb := @measure_bounded_by_metric_scale_envelope R X J S cost delta nu
  (fun B=>K^-1%:E*mu B) hn hs hj A.
have hKE : 0<=K%:E by rewrite lee_fin; exact: ltW hK.
have hh := lee_wpmul2l hKE hb.
by rewrite muleA -EFinM mulfV // mul1e in hh.
Qed.
