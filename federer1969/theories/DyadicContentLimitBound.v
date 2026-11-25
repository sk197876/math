(** Federer (1969), 2.10.47, pp. 204–205: the cutoffs sqrt(n) 2^(-i) tend to
    zero, so a common upper bound on all sufficiently fine dyadic contents
    bounds the limiting power-gauge measure. This is the upper-bound step in
    the last paragraph on p. 205. Source context:
    DyadicContentCutoffLower.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicScaleBounds DyadicContentCutoffLower RefiningCoverContent
  MetricDiameter MetricRealPowerCost MetricRealPowerMeasureUP CaratheodoryLimitUP
  HausdorffLengthUP MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_diameter_cutoffs_cofinal]: supporting
    convergence of the dyadic diameter cutoffs in the
    final paragraph of 2.10.47, p. 205. An
    arbitrary initial level h may be omitted. *)
Lemma dyadic_diameter_cutoffs_cofinal (R : realType) n h (d : R) :
  (0<d)%R -> exists j, (Num.sqrt n%:R/((2^(h+j))%N)%:R<d)%R.
Proof.
move=> hd.
have hs : (0<=Num.sqrt n%:R :> R)%R := sqrtr_ge0 _.
have hs1 : (0<Num.sqrt n%:R+1 :> R)%R by nra.
have hd' : (0<d/(Num.sqrt n%:R+1))%R by apply: divr_gt0.
have [j hj] := dyadic_sides_arbitrarily_small hd'.
exists j.
have hside := @dyadic_side_antitone R j (h+j)%N (leq_addl h j).
have hmul : ((Num.sqrt n%:R : R)*((2^(h+j))%N)%:R^-1<=Num.sqrt n%:R*((2^j)%N)%:R^-1)%R.
  apply: ler_wpM2l; [exact hs | exact hside].
have hpos := dyadic_side_positive R j.
have hb : ((Num.sqrt n%:R+1)*((2^j)%N)%:R^-1<d)%R.
  by move: hj; rewrite ltr_pdivlMr // mulrC.
nra.
Qed.

(** Source for [dyadic_contents_bound_power_measure]: the
    inequality H^m(B)<=lim gamma_i(B) in 2.10.47,
    p. 205, stated as its upper-bound property. It
    follows from the defining cutoff supremum, without
    assuming convergence or measurability of the contents. *)
Theorem dyadic_contents_bound_power_measure (R : realType) n (a : R_n R n) Q c p
    (gamma : nat -> set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    mu h (E : set (inner_metric_space (@euclidean_inner_productP R n))) b :
  is_dyadic_cube_grid a Q ->
  (forall i, is_refining_cover_content (dyadic_cube_level Q) (metric_real_diameter_cost c p) i (gamma i)) ->
  is_metric_real_power_measure c p mu -> (0<=c)%R ->
  (forall j, gamma (h+j)%N E<=b) -> mu E<=b.
Proof.
move=> hQ hg hmu hc hb.
pose X := inner_metric_space (@euclidean_inner_productP R n).
pose S := fun T : @nonempty_metric_sets R X=>val T.
pose cost := fun T : @nonempty_metric_sets R X=>metric_real_diameter_cost c p (val T).
have hcost (T : set X) : 0<=metric_real_diameter_cost c p T :=
  @metric_real_power_cost_nonnegative R c p (extended_metric_diameter T) hc.
apply: (caratheodory_limit_least hmu)=> delta nu hd hn.
have [j hj] : exists j, (Num.sqrt n%:R/((2^(h+j))%N)%:R)%:E<=delta.
  case: delta hd hn=> [d| |] hd hn.
  - have hdR : (0<d)%R by move: hd; rewrite lte_fin.
    have [j hj] := @dyadic_diameter_cutoffs_cofinal R n h d hdR.
    exists j; rewrite lee_fin; exact: ltW hj.
  - exists 0%N; exact: leey.
  - by move: hd; rewrite ltNge leNye.
pose eta := metric_scale_envelope S cost (Num.sqrt n%:R/((2^(h+j))%N)%:R)%:E.
have he := metric_scale_envelope_specification S cost (Num.sqrt n%:R/((2^(h+j))%N)%:R)%:E.
apply: le_trans (@metric_scale_envelope_antitone_cutoff R X _ S cost _ _ eta nu he hn hj E) _.
apply: le_trans _ (hb j).
exact: (@dyadic_content_cutoff_lower_bound R n a Q _ (h+j)%N (gamma (h+j)%N) eta
  hQ (hg _) he (fun T _=>hcost T) E).
Qed.
