(** Federer (1969), 2.3.8, p. 79: the scalar bound |cf|_mu <= max(|f|_mu,
    |c| |f|_mu). Source context: MeasureGauge.v. The project's extended
    arithmetic uses this same convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureBasic MeasureGauge MeasureGaugeAttainment.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_scaled_superlevel_cover]: supporting exceptional-set
    inclusion for Federer 2.3.8, p. 79 It includes c=0. *)
Lemma partial_scaled_superlevel_cover (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (c : R)
    (f : partial_function X V) r :
  partial_norm_superlevel N (partial_vector_scale c f) (Order.max r ((`|c|%R)%:E*r)) `<=`
    partial_norm_superlevel N f r.
Proof.
move=> x [z [hz hlt]].
have [a [ha he]] := proj1 (partial_vector_scale_graph c f x z) hz.
exists a; split=> //.
change (r < (N a)%:E); rewrite ltNge; apply/negP=> hra.
have hc : 0 <= (`|c|%R)%:E by rewrite lee_fin normr_ge0.
have hmul := @lee_wpmul2l R (`|c|%R)%:E hc (N a)%:E r hra.
have hle : (N z)%:E <= Order.max r ((`|c|%R)%:E*r).
  rewrite he (real_seminorm_scale hN) EFinM.
  apply: le_trans hmul _; by rewrite le_max lexx orbT.
have hlt' : Order.max r ((`|c|%R)%:E*r) < (N z)%:E := hlt.
by move: hlt'; rewrite ltNge hle.
Qed.

(** Source for [measure_gauge_scale_feasible]: feasible scalar
    threshold in Federer 2.3.8, p. 79, valid before taking
    the infimum. *)
Lemma measure_gauge_scale_feasible (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R)
    (hN : is_real_seminorm N) (c : R) (f : partial_function X V) r :
  measure_gauge_feasible mu N f r ->
  measure_gauge_feasible mu N (partial_vector_scale c f) (Order.max r ((`|c|%R)%:E*r)).
Proof.
move=> [hr hb]; split; first by rewrite le_max hr.
apply: le_trans (@measure_mono R X mu hm _ _
  (@partial_scaled_superlevel_cover R X V N hN c f r)) _.
apply: le_trans hb _; by rewrite le_max lexx.
Qed.

(** Source for [measure_gauge_scale_bound]: direct scalar inequality in
    Federer 2.3.8, p. 79 The gauge may be infinite. *)
Theorem measure_gauge_scale_bound (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R)
    (hN : is_real_seminorm N) (c : R) (f : partial_function X V) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  measure_gauge mu N (partial_vector_scale c f) <=
    Order.max (measure_gauge mu N f) ((`|c|%R)%:E * measure_gauge mu N f).
Proof.
move=> hf; apply: measure_gauge_bound.
exact (@measure_gauge_scale_feasible R X V mu hm N hN c f _
  (@measure_gauge_attained R X V mu hm N f hf)).
Qed.
