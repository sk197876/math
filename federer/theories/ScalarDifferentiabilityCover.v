(** Federer (1969), 3.2.7, p. 246, third
    example: prove the null-image property of the signed
    square root using finite derivatives off zero and
    countably many actual Lipschitz restrictions. The
    argument expands 3.1.8–3.1.9 and 2.10.13. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground RealLineSeparability RealCurveDerivativeUP RealDerivativeIncrementBounds
  MetricLocalLipschitzCenters MetricClosedSmallCover ExtendedRealReciprocalBounds RealLatticeTruncationLimits
  LipschitzUP HausdorffMeasure HausdorffRestrictedLipschitz HausdorffLengthCompatibility HausdorffLengthReal
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_point_growth_natural_center]: supporting
    countable finite-growth choice for the third example
    of Federer 3.2.7, p. 246, by the closed
    growth-centre argument of 3.1.9, p. 218. *)
Lemma metric_point_growth_natural_center (R:realType) (X Y:metricType R)
    (f:X->Y) (a:X) (M d:R):
  0<M -> 0<d ->
  (forall x,mdist a x<d -> mdist (f x) (f a)<=M*mdist x a) ->
  exists j:nat,metric_local_lipschitz_centers setT f (j.+1%:R) ((j.+1%:R)^-1) a.
Proof.
move=>hM hd hb.
have [p hp]:=positive_reciprocal_nat_small hd.
pose N:=Num.bound M.
pose j:=maxn N p.
have hMj:M<j.+1%:R.
  apply:lt_le_trans (archi_boundP (ltW hM)) _.
  rewrite ler_nat; exact:leq_trans (leq_maxl N p) (leqnSn j).
have hr:(j.+1%:R:R)^-1<d.
  exact:le_lt_trans (@positive_reciprocal_nat_antitone R p j (leq_maxr N p)) hp.
exists j; split=>// x hx; split=>//.
apply:le_trans (hb x (lt_trans hx hr)) _.
apply:ler_wpM2r; [exact:mdist_ge0|exact:ltW hMj].
Qed.

(** Source for [scalar_derivative_growth_center]: a finite
    actual scalar derivative supplies a finite growth
    centre, supporting the null-image argument in the
    third example of Federer 3.2.7, p. 246. *)
Lemma scalar_derivative_growth_center (R:realType) (f:R->R) (a v:R):
  has_real_curve_derivative f a v -> exists j:nat,
    metric_local_lipschitz_centers setT (f:real_line_metric R->real_line_metric R)
      (j.+1%:R) ((j.+1%:R)^-1) a.
Proof.
move=>hD; pose M:=`|v|+1.
have hM:0<M by rewrite /M; have hn:=normr_ge0 v; lra.
have [d [hd hError]]:=real_derivative_small_displacement_error hD (@ltr01 R).
apply:(@metric_point_growth_natural_center R [the metricType R of real_line_metric R]
  [the metricType R of real_line_metric R] f a M d hM hd)=>y hy.
change (is_true (`|a-y|<d)) in hy.
have hSmall:`|y-a|<d by rewrite distrC.
have hErr:=hError (y-a) hSmall.
rewrite (addrC a (y-a)) subrK mul1r in hErr.
have hTri:=ler_normD (f y-f a-v*(y-a)) (v*(y-a)).
rewrite subrK normrM in hTri.
change (is_true (`|f y-f a|<=M*`|y-a|)).
rewrite /M mulrDl mul1r; lra.
Qed.

(** Source for [scalar_differentiability_lipschitz_cover]:
    countable closed Lipschitz cover of the actual
    finite derivative domain, supporting the third
    example of Federer 3.2.7, p. 246. No
    continuity, measurability or global derivative bound
    is added to this supporting lemma. *)
Theorem scalar_differentiability_lipschitz_cover (R:realType) (f:R->R):
  exists F:(nat*nat)->set (real_line_metric R),
    (forall q,closed (F q) /\ is_metric_lipschitz (F q) (f:real_line_metric R->real_line_metric R)) /\
    forall a,(exists v,has_real_curve_derivative f a v) -> (\bigcup_q F q) a.
Proof.
pose X:=real_line_metric R.
pose C j:=metric_local_lipschitz_centers setT (f:X->X) (j.+1%:R) ((j.+1%:R)^-1).
have [D [hc hd]]:=@real_line_countable_dense R.
have hex j:exists E:nat->set X,
    (forall k,closed (E k) /\ E k `<=` C j /\
      forall x y,E k x -> E k y -> mdist x y<=((j.+1%:R)^-1/2)) /\ C j=\bigcup_k E k.
  apply:(separable_closed_small_cover_allow_empty hc hd).
  - apply:metric_local_lipschitz_centers_closed; by rewrite ?ler0n ?invr_gt0 ?ltr0n.
  - by rewrite divr_gt0 ?invr_gt0 ?ltr0n.
have [E hE]:=choice hex.
exists (fun q=>E q.1 q.2); split.
- move=>[j k]; split; first exact ((hE j).1 k).1.
  apply:(@metric_local_lipschitz_centers_small_piece R [the metricType R of X] [the metricType R of X]
    setT (E j k) f (j.+1%:R) ((j.+1%:R)^-1)).
  + by rewrite ltr0n.
  + exact ((hE j).1 k).2.1.
  + move=>x y hx hy; apply:le_lt_trans (((hE j).1 k).2.2 x y hx hy) _.
    have hp:0<(j.+1%:R:R)^-1 by rewrite invr_gt0 ltr0n.
    by rewrite (ltr_pdivrMr _ _ (_:0<(2:R))) ?ltr0n // mulr_natr ltrDl.
- move=>a [v hv]; have [j hj]:=scalar_derivative_growth_center hv.
  change (C j a) in hj; rewrite (hE j).2 in hj.
  have [k _ hk]:=hj; by exists (j,k).
Qed.
