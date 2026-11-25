(** Federer (1969), 2.10.3, p. 172: compact
    covers give the same final measure. At a finite
    cutoff, close each bounded generator; its closure
    is compact with unchanged diameter and exterior
    gauge. Finite cofinal cutoffs suffice even when
    the target cutoff or measure is infinite. Source
    editions and proof ingredients: ExteriorDiameterUP.v,
    ExteriorDiameterClosure.v and EuclideanBoundedClosure.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  HausdorffLengthUP ExteriorMeasureGauge ExteriorMeasureUP ExteriorMeasure
  ExteriorCompactCoverUP ExteriorDiameterClosure EuclideanBoundedClosure
  MetricDiameter MetricDiameterClosure MetricScaleEnvelopeUP MetricScaleEnvelope
  MetricScaleEnvelopeLaws MetricScaleCutoffCost MetricScaleMeasureBound MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryMeasure CaratheodoryFamilyReplacement CaratheodoryBorelRegular
  MeasureUP BorelRegularMeasureUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [exterior_compact_cover_agreement]: direct
    compact-cover equality in Federer 2.10.3, p. 172,
    for independently specified measures. Targets may be
    arbitrary and unbounded; boundedness is required
    only of generators at finite intermediate cutoffs. *)
Theorem exterior_compact_cover_agreement (R : realType) (n m : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  is_exterior_diameter_measure m mu -> is_compact_exterior_diameter_measure m nu ->
  forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hlo : mu A<=nu A.
  apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
    (@nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (fun j => val j) (fun j => val j)
    (fun j => exterior_diameter_cost m (val j))
    (fun j => exterior_diameter_cost m (val j)) nu mu hn hm _ _ A).
  - move=> j; exact: exterior_diameter_cost_nonnegative.
  - move=> j.
    pose k : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
      @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) => B \in [set B | B !=set0])
        (val j) (mem_set (set_valP j).2).
    exists k; split; first by move=> x hx.
    by split.
apply/eqP; rewrite eq_le hlo /=.
apply: (caratheodory_limit_least hn)=> tau xi htau hxi.
have [ell hell] := reciprocal_metric_cutoffs_cofinal htau.
pose t : R := (((ell.+1)%:R)^-1)%R.
have ht : (0<t)%R by rewrite /t invr_gt0 ltr0n.
pose phi := metric_scale_envelope
  (fun j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
  (fun j => exterior_diameter_cost m (val j)) t%:E.
have hphi := @metric_scale_envelope_specification R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) t%:E.
have hxi_measure : is_measure xi := metric_scale_envelope_is_measure hxi
  (fun j => exterior_diameter_cost_nonnegative m (val j)).
have hgen (j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))) :
    extended_metric_diameter (val j)<=t%:E -> xi (val j)<=exterior_diameter_cost m (val j).
  move=> hd.
  have hc := @euclidean_bounded_set_closure_compact R n (val j) t (set_valP j) hd.
  have hne : closure (val j) !=set0.
    have [x hx] := set_valP j; exists x; exact: subset_closure hx.
  pose k : @nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
    @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) =>
      B \in [set B | compact B /\ B !=set0]) (closure (val j)) (mem_set (conj hc hne)).
  have hsize : extended_metric_diameter (val k)<=tau.
    change (extended_metric_diameter (closure (val j))<=tau).
    rewrite extended_metric_diameter_closure; exact: le_trans hd hell.
  have hb := @metric_scale_generator_bound R (inner_metric_space (@euclidean_inner_productP R n))
    (@nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (fun j => val j) (fun j => exterior_diameter_cost m (val j)) tau xi k hxi
    (exterior_diameter_cost_nonnegative m (val k)) hsize.
  change (is_true (xi (closure (val j))<=exterior_diameter_cost m (closure (val j)))) in hb.
  rewrite exterior_diameter_cost_closure in hb.
  apply: le_trans _ hb.
  exact (@metric_scale_envelope_mono R (inner_metric_space (@euclidean_inner_productP R n))
    (@nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
    (fun j => val j) (fun j => exterior_diameter_cost m (val j)) tau xi hxi
    (val j) (closure (val j)) (@subset_closure _ (val j))).
apply: le_trans (@measure_bounded_by_metric_scale_envelope R
  (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) t%:E phi xi
  hphi hxi_measure hgen A) _.
exact (@caratheodory_limit_upper R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) mu hm A t%:E phi ht hphi).
Qed.

(** Source for [exterior_measure_compact_cover_specification]:
    direct assertion that selected T^m is obtained from
    compact generators in Federer 2.10.3, p. 172.
    Construct the competing measure by the existing
    sealed Caratheodory operator and use the proved equality. *)
Theorem exterior_measure_compact_cover_specification (R : realType) (n m : nat) :
  is_compact_exterior_diameter_measure m (@exterior_diameter_measure R n m).
Proof.
pose S := fun j : @nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j.
pose c := fun j : @nonempty_compact_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) =>
  exterior_diameter_cost m (val j).
pose nu := caratheodory_measure S c.
have hn : is_compact_exterior_diameter_measure m nu := caratheodory_measure_specification S c.
have he : @exterior_diameter_measure R n m=nu.
  apply: funext=> A; exact (@exterior_compact_cover_agreement R n m _ _
    (@exterior_diameter_measure_specification R n m) hn A).
by rewrite he.
Qed.

(** Source for [exterior_diameter_measure_borel_regular]:
    supporting consequence of the compact-cover assertion
    in Federer 2.10.3, p. 172, and the Borel-
    generator theorem of 2.10.1, p. 170. Metric
    compact generators are closed, hence Borel. *)
Theorem exterior_diameter_measure_borel_regular (R : realType) (n m : nat) :
  is_borel_regular_measure (@exterior_diameter_measure R n m).
Proof.
apply: (caratheodory_limit_borel_regular (@exterior_measure_compact_cover_specification R n m)).
- move=> j; exact: exterior_diameter_cost_nonnegative.
- move=> j; apply: closed_borel_set.
  exact: compact_closed (@metric_hausdorff R (inner_metric_space (@euclidean_inner_productP R n))) (set_valP j).1.
Qed.
