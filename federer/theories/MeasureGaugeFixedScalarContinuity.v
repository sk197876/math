(** Federer (1969), 2.3.8, p. 79: for fixed c, cf tends to zero as f tends
    to zero in measure. Source context: MeasureGauge.v. The epsilon-delta
    estimate below states full continuity at zero, not merely a sequential
    test. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureGauge MeasureGaugeScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [fixed_scalar_gauge_budget]: supporting scalar
    neighborhood for the continuity consequence in Federer 2.3.8,
    p. 79. The positive budget e/(1+|c|) controls both
    terms in the printed maximum bound. *)
Lemma fixed_scalar_gauge_budget (R : realType) (c e : R) : (0 < e)%R ->
  exists d : R, (0 < d)%R /\ (d <= e)%R /\ (`|c|*d < e)%R.
Proof.
move=> he; pose d := (e/(1+`|c|))%R.
have hp : (0 < 1+`|c|)%R by rewrite ltr_pwDl // normr_ge0.
have hd : (0 < d)%R by rewrite /d divr_gt0.
have heq : ((1+`|c|)*d)%R = e.
  rewrite /d mulrC divfK //; exact: lt0r_neq0 hp.
exists d; split=> //; split.
- rewrite -heq mulrDl mul1r lerDl; exact: mulr_ge0 (normr_ge0 c) (ltW hd).
- by rewrite -heq mulrDl mul1r ltrDr.
Qed.

(** Source for [measure_gauge_fixed_scalar_continuity]: direct fixed-scalar
    continuity conclusion in Federer 2.3.8, p. 79 The estimate is uniform
    over all functions with measurable norm superlevels. *)
Theorem measure_gauge_fixed_scalar_continuity (R : realType) (X : choiceType)
    (V : lmodType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (N : V -> R) (hN : is_real_seminorm N) (c e : R) : (0 < e)%R ->
  exists d : R, (0 < d)%R /\ forall f : partial_function X V,
    (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
    measure_gauge mu N f < d%:E -> measure_gauge mu N (partial_vector_scale c f) < e%:E.
Proof.
move=> he; have [d [hd [hde hce]]] := fixed_scalar_gauge_budget c he.
exists d; split=> // f hf hfd.
apply: le_lt_trans (@measure_gauge_scale_bound R X V mu hm N hN c f hf) _.
rewrite gt_max; apply/andP; split.
- apply: lt_le_trans hfd _; exact hde.
- have hc : 0 <= (`|c|%R)%:E by rewrite lee_fin normr_ge0.
  have hmul := @lee_wpmul2l R (`|c|%R)%:E hc _ d%:E (ltW hfd).
  apply: le_lt_trans hmul _; by rewrite -EFinM lte_fin.
Qed.
