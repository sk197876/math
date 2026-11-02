(** Federer (1969), 2.10.3, p. 172: restricting generators to open sets
    gives the same final measure. Compact finite endpoint powers and
    continuity give open enlargements with arbitrarily close cost. Compare
    distinct positive cutoffs before taking their supremum. Source context
    and supporting continuity references: ExteriorDiameterUP.v and
    ExteriorEndpointContinuity.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import EuclideanInnerProduct InnerMetric HausdorffLengthUP
  HausdorffMeasureUP ExteriorMeasureGauge ExteriorMeasureUP ExteriorMeasure
  ExteriorOpenCoverUP ExteriorOpenEnlargement ExtendedRealOrderTopology
  MetricDiameter MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleEnvelopeLaws
  MetricScaleCutoffCost MetricScaleMeasureBound MetricScaleWeightedBound
  CaratheodoryLimitUP CaratheodoryMeasure CaratheodoryFamilyReplacement CaratheodoryBorelRegular MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [open_exterior_scale_generator_bound]: supporting
    open enlargement for Federer 2.10.3, p. 172.
    A smaller source diameter cutoff leaves room for an
    open generator. Order density eliminates the strict
    cost slack, including infinite costs or envelope values. *)
Lemma open_exterior_scale_generator_bound (R : realType) (n m : nat)
    (nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d t : R) (tau : \bar R) :
  is_metric_scale_envelope
    (fun j : @nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => exterior_diameter_cost m (val j)) tau nu ->
  A !=set0 -> (0<=d)%R -> (d<t)%R -> t%:E<=tau -> extended_metric_diameter A<=d%:E ->
  nu A<=exterior_diameter_cost m A.
Proof.
move=> hn hA hd hdt htau hdiam.
rewrite leNgt; apply/negP=> hbad.
have [q [hcost hqn]] := @extended_rationals_order_dense R
  (exterior_diameter_cost m A) (nu A) hbad.
have [U [hU [hne [hAU [hsize hcostU]]]]] :=
  @exterior_gauge_open_enlargement R n m A d t (ratr q) hA hd hdt hdiam hcost.
pose j : @nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) :=
  @exist _ (fun B : set (inner_metric_space (@euclidean_inner_productP R n)) =>
    B \in [set B | open B /\ B !=set0]) U (mem_set (conj hU hne)).
have hbound := @metric_scale_generator_bound R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) tau nu j hn
  (exterior_diameter_cost_nonnegative m U) (le_trans hsize htau).
have hmono := @metric_scale_envelope_mono R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) tau nu hn A U hAU.
have hh := le_trans hmono (le_trans hbound hcostU).
by have := lt_le_trans hqn hh; rewrite ltxx.
Qed.

(** Source for [exterior_open_cover_agreement]: direct
    open-cover equality in Federer 2.10.3, p. 172,
    for independently specified final measures and arbitrary
    target sets. Finite cofinal cutoffs handle the infinite
    cutoff without a global boundedness hypothesis. *)
Theorem exterior_open_cover_agreement (R : realType) (n m : nat)
    (mu nu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  is_exterior_diameter_measure m mu -> is_open_exterior_diameter_measure m nu ->
  forall A, mu A=nu A.
Proof.
move=> hm hn A.
have hlo : mu A<=nu A.
  apply: (@caratheodory_family_replacement R (inner_metric_space (@euclidean_inner_productP R n))
    (@nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
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
have hd : (0<=t/2)%R by rewrite divr_ge0 //; exact: ltW ht.
have hdt : (t/2<t)%R by rewrite ltr_pdivrMr //; lra.
pose phi := metric_scale_envelope
  (fun j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
  (fun j => exterior_diameter_cost m (val j)) ((t/2)%R%:E).
have hphi := @metric_scale_envelope_specification R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) ((t/2)%R%:E).
have hxi_measure : is_measure xi := metric_scale_envelope_is_measure hxi
  (fun j => exterior_diameter_cost_nonnegative m (val j)).
have hgen (j : @nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))) :
    extended_metric_diameter (val j)<=(t/2)%R%:E -> xi (val j)<=exterior_diameter_cost m (val j).
  move=> hj; exact (@open_exterior_scale_generator_bound R n m xi (val j) (t/2)%R t tau
    hxi (set_valP j) hd hdt hell hj).
apply: le_trans (@measure_bounded_by_metric_scale_envelope R
  (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) ((t/2)%R%:E) phi xi
  hphi hxi_measure hgen A) _.
apply: (@caratheodory_limit_upper R (inner_metric_space (@euclidean_inner_productP R n))
  (@nonempty_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)))
  (fun j => val j) (fun j => exterior_diameter_cost m (val j)) mu hm A ((t/2)%R%:E) phi _ hphi).
by rewrite lte_fin divr_gt0 // ltr0n.
Qed.

(** Source for [exterior_measure_open_cover_specification]:
    direct assertion that selected T^m satisfies the open-
    cover construction of Federer 2.10.3, p. 172.
    The alternative exists by the sealed Caratheodory
    construction; its equality is the preceding theorem. *)
Theorem exterior_measure_open_cover_specification (R : realType) (n m : nat) :
  is_open_exterior_diameter_measure m (@exterior_diameter_measure R n m).
Proof.
pose S := fun j : @nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j.
pose c := fun j : @nonempty_open_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) =>
  exterior_diameter_cost m (val j).
pose nu := caratheodory_measure S c.
have hn : is_open_exterior_diameter_measure m nu := caratheodory_measure_specification S c.
have he : @exterior_diameter_measure R n m=nu.
  apply: funext=> A; exact (@exterior_open_cover_agreement R n m _ _
    (@exterior_diameter_measure_specification R n m) hn A).
by rewrite he.
Qed.
