(** Federer (1969), 2.3.8, p. 79, last paragraph: cf tends to zero as c
    tends to zero when f has a nonzero locus of finite measure. Source
    editions: MeasureGauge.v. The proof uses a high norm tail of small
    measure and the explicit scalar neighborhood prescribed by Federer. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import RealNormUP PartialFunctionUP PartialNormedArithmetic
  MeasureUP MeasureBasic MeasureGauge MeasureNormTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [small_scalar_superlevel_cover]: supporting
    inclusion in Federer 2.3.8, p. 79, final paragraph:
    if |c|<e/b, then |cf|>e implies |f|>b. *)
Lemma small_scalar_superlevel_cover (R : realType) (X : Type) (V : lmodType R)
    (N : V -> R) (hN : is_real_seminorm N) (c e b : R)
    (f : partial_function X V) : (0 < b)%R -> (`|c| < e/b)%R ->
  partial_norm_superlevel N (partial_vector_scale c f) e%:E `<=`
    partial_norm_superlevel N f b%:E.
Proof.
move=> hb hc x [z [hz hzbig]].
have [a [ha he]] := proj1 (partial_vector_scale_graph c f x z) hz.
exists a; split=> //; change (b < N a)%R.
rewrite ltNge; apply/negP=> hab.
have hs : (`|c|*N a <= `|c|*b)%R := ler_wpM2l (normr_ge0 c) hab.
have ht : (`|c|*b < e)%R by move: hc; rewrite ltr_pdivlMr.
have hz' : (e < N z)%R := hzbig.
rewrite he (real_seminorm_scale hN) in hz'.
have hh := lt_trans hz' (le_lt_trans hs ht); by move: hh; rewrite ltxx.
Qed.

(** Source for [measure_gauge_scalar_continuity]: direct scalar- continuity
    conclusion in Federer 2.3.8, p. 79 The finite nonzero-norm locus is
    explicit, and the gauge can otherwise take infinite values. *)
Theorem measure_gauge_scalar_continuity (R : realType) (X : choiceType) (V : lmodType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (N : V -> R)
    (hN : is_real_seminorm N) (f : partial_function X V) (e : R) :
  (forall t : R, measure_measurable mu (partial_norm_superlevel N f t%:E)) ->
  mu (partial_norm_superlevel N f 0) < +oo -> (0 < e)%R ->
  exists d : R, (0 < d)%R /\ forall c : R, (`|c| < d)%R ->
    measure_gauge mu N (partial_vector_scale c f) < e%:E.
Proof.
move=> hme hfin he.
have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
have [n hn] := @measure_norm_tail_small R X V mu hm N f (e/2)%R
  (real_seminorm_nonnegative hN) hme hfin he2.
have hb : (0 < n.+1%:R :> R)%R by rewrite ltr0n.
exists ((e/2)/n.+1%:R)%R; split; first by rewrite divr_gt0.
move=> c hc.
have hfeas : measure_gauge_feasible mu N (partial_vector_scale c f) (e/2)%:E.
  split; first exact: ltW he2.
  apply: le_trans (@measure_mono R X mu hm _ _
    (@small_scalar_superlevel_cover R X V N hN c (e/2)%R n.+1%:R f hb hc)) _.
  exact: ltW hn.
apply: le_lt_trans (@measure_gauge_bound R X V mu N _ _ hfeas) _.
rewrite lte_fin ltr_pdivrMr ?ltr0n // mulr_natr.
by rewrite ltrDl.
Qed.
