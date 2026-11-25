(** Federer (1969), 4.1.7, p. 358: an
    actual smooth coefficient operation preserves
    finite original compact-test gauges. Its weight
    is the continuous coefficient norm times
    the proved bilinear bound; it need not
    be bounded on all of U. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology functions.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormMetric RealMetricBackground NormDifferentialUP
  NormBoundedBilinearUP SmoothFunctionSpaceUP SmoothFieldNormContinuity DistributionVariationDomain
  DistributionFiniteVariationUP FiniteCompactGaugeTranspose MetricSubsetBackground.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Section SmoothBilinearTransposeFiniteGauge.
Variable R:realType.
Variables X A Y0 Y1:lmodType R.
Variables (NX:X->R) (NA:A->R) (N0:Y0->R) (N1:Y1->R).
Hypotheses (hNX:is_real_norm NX) (hNA:is_real_norm NA)
  (hN0:is_real_norm N0) (hN1:is_real_norm N1).
Variable U:set X.
Local Notation XT := (real_norm_metric_space hNX).
Local Notation UT := (metric_subset (U:set XT)).
Variable EA:lmodType R.
Variable av:EA->X->A.
Hypothesis hA:is_smooth_function_space hNX hNA U av.
Variable a:EA.
Variables E0 E1:lmodType R.
Variables (v0:Hom E0 (GRing.Lmodule.clone R (X->Y0) _))
  (v1:Hom E1 (GRing.Lmodule.clone R (X->Y1) _)).
Variable B:A->Y0->Y1.
Hypothesis hB:norm_bounded_bilinear NA N0 N1 B.
Variable P:Hom E0 E1.
Hypothesis hPoint:forall (phi:E0) x,U x->v1 (P phi) x=B (av a x) (v0 phi x).
Variable S:Hom E1 R^o.
Local Notation d0 := (@distribution_domain_values R XT U Y0 E0 v0).
Local Notation d1 := (@distribution_domain_values R XT U Y1 E1 v1).

(** Source for [smooth_bilinear_transpose_finite_gauge]:
    the original smooth test transpose preserves
    finite compact scalar gauges, supporting
    the current multiplication and local normality
    assertions in Federer 4.1.7, p. 358.
    Every coefficient bound is proved separately. *)
Theorem smooth_bilinear_transpose_finite_gauge:
  @is_finite_distribution_variation R XT U Y1 N1 E1 v1 S->
  @is_finite_distribution_variation R XT U Y0 N0 E0 v0 (hom_comp S P).
Proof.
move=>hFinite.
have[_ [C [hC hNorm]]]:=hB.
pose w:=fun x:UT=>C*NA (av a (set_val x)).
have hW:continuous (w:UT->real_line_metric R).
  move=>x.
  exact (@continuousM R UT (fun _=>C) (fun z:UT=>NA (av a (set_val z))) x
    (@cvg_cst [the topologicalType of R^o] C UT _
      (@nbhs_filter [the topologicalType of UT] x))
    (@smooth_field_norm_continuity R X A NX NA hNX hNA U EA av hA a x)).
have hWNonnegative:forall x:UT,0<=w x.
  move=>x;exact:mulr_ge0 hC (real_seminorm_nonnegative hNA.1 _).
have hActual (phi:E0) (x:UT):N1 (d1 (P phi) x)<=w x*N0 (d0 phi x).
  change (N1 (v1 (P phi) (set_val x))<=C*NA (av a (set_val x))*N0 (v0 phi (set_val x))).
  rewrite (@hPoint phi (set_val x) (set_valP x)).
  have h:=hNorm (av a (set_val x)) (v0 phi (set_val x));by rewrite mulrA in h.
exact:(@finite_compact_gauge_transpose R UT Y0 Y1 N0 N1 hN0 hN1 E0 E1 d0 d1 P
  w hW hWNonnegative hActual S hFinite).
Qed.
End SmoothBilinearTransposeFiniteGauge.
