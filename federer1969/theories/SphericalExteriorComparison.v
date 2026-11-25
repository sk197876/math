(** Federer (1969), 2.10.39, printed p. 199: pass the finite box-cover cost
    to spherical and exterior-diameter measures. This theorem treats
    positive degree m at most the ambient dimension. The above-ambient case
    is supplied separately before the numbered public statement. Different
    source and ball cutoffs are compared through the proved infimum and
    supremum specifications. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffLengthUP HausdorffMeasureUP HausdorffMeasure
  HausdorffDiameterCost MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleCutoffCost MetricScaleWeightedBound CaratheodoryLimitUP CaratheodoryBorelRegular
  ExteriorMeasure ExteriorMeasureGauge ExteriorCompactCoverUP ExteriorCompactCoverAgreement
  CompactExteriorSphericalCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_spherical_exterior_comparison]: direct
    corollary 2.10.39, p. 199, for m=p+1<=n.
    The coefficient n^(m/2) is written as sqrt(n)^m,
    using natural degree m. Arbitrary targets, infinite
    mass, nonconvex compact generators and zero side
    widths are included. *)
Theorem euclidean_spherical_exterior_comparison (R : realType) n p (hp : (p<n)%N)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) :
  (@spherical_measure R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] p.+1 A<=
    ((Num.sqrt n%:R)^+p.+1*2^+p)%:E*@exterior_diameter_measure R n p.+1 A)%E.
Proof.
pose E := inner_metric_space (@euclidean_inner_productP R n).
pose J := @positive_closed_metric_balls R [the metricType R of E].
pose F := fun j : J=>val j.
pose cost := fun j : J=>hausdorff_diameter_cost p.+1 (val j).
pose C : R := (Num.sqrt n%:R)^+p.+1*2^+p.
have hn0 : (0<n)%N := leq_ltn_trans (leq0n p) hp.
have hs : 0<Num.sqrt n%:R :> R by rewrite sqrtr_gt0 ltr0n.
have hC : 0<C by apply: mulr_gt0; apply: exprn_gt0; [exact hs|exact: ltr0n].
have hCE : (0<=C%:E)%E by rewrite lee_fin; exact: ltW hC.
have hS := @spherical_measure_specification R [the metricType R of E] p.+1.
have hT := @exterior_measure_compact_cover_specification R n p.+1.
apply: (caratheodory_limit_least hS)=> delta nu hdelta hn.
have [k hkd] := reciprocal_metric_cutoffs_cofinal hdelta.
pose d : R := ((k.+1)%:R)^-1.
have hd : 0<d by rewrite /d invr_gt0 ltr0n.
pose phi := metric_scale_envelope F cost d%:E.
have hphi := metric_scale_envelope_specification F cost d%:E.
have hlo : (nu A<=phi A)%E := metric_scale_envelope_antitone_cutoff hphi hn hkd A.
pose t : R := d/(Num.sqrt n%:R+1).
have hden : 0<Num.sqrt n%:R+1 :> R by lra.
have hden0 : (Num.sqrt n%:R+1!=0 :> R) by rewrite (gt_eqF hden).
have ht : 0<t by rewrite /t divr_gt0.
have hcap : Num.sqrt n%:R*t<d.
  have hmul : Num.sqrt n%:R*t<(Num.sqrt n%:R+1)*t.
    rewrite (ltr_pM2r ht); lra.
  have he : (Num.sqrt n%:R+1)*t=d.
    by rewrite /t mulrCA mulfV // mulr1.
  rewrite he in hmul; exact hmul.
pose K := @nonempty_compact_metric_sets R [the metricType R of E].
pose G := fun j : K=>val j.
pose g := fun j : K=>exterior_diameter_cost p.+1 (val j).
pose eta := metric_scale_envelope G g t%:E.
have heta := metric_scale_envelope_specification G g t%:E.
have hphim := metric_scale_envelope_is_measure hphi
  (fun j=>hausdorff_diameter_cost_nonnegative p.+1 (val j)).
have hb : (phi A<=C%:E*eta A)%E.
  apply: (@measure_bounded_by_scaled_metric_envelope R [the metricType R of E] K G g
    t%:E eta phi C heta hphim hC)=> j hj.
  exact (@compact_exterior_spherical_cutoff_bound R n p hp (val j) t d phi
    (set_valP j).1 (set_valP j).2 hj hcap hphi).
have he := @caratheodory_limit_upper R [the metricType R of E] K G g
  (@exterior_diameter_measure R n p.+1) hT A t%:E eta ht heta.
exact: le_trans hlo (le_trans hb (lee_wpmul2l hCE he)).
Qed.
