(** Federer (1969), 2.10.19(2), p. 181: finite positive-cutoff
    approximations make the locus of upper phi_infinity-restricted density
    below 2^(-m) Hausdorff null. Here the equivalent empty-completed
    generator family permits the existing intersection-cover proof without
    regarding empty intersections as nonempty generators. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureRestriction MeasureAlmostBasic MeasureIndexedCover
  NonnegativeSum MetricDiameter HausdorffLengthUP HausdorffMeasure HausdorffDiameterCost HausdorffAllSets
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost MetricScaleLocalAgreement
  CaratheodoryLimitMeasure CaratheodoryDensityGoodSets CaratheodoryDensityGoodNull CaratheodoryBorelRegular
  MetricDensities MetricDensityNumericalBounds MetricDensityHausdorffGauge ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_scale_measure]: public actual
    phi_delta of 2.10.19, p. 181, using the
    original nonempty Hausdorff generators of 2.10.2(1),
    p. 171. Its infimum implementation is already sealed. *)
Definition hausdorff_scale_measure (R : realType) (X : metricType R) (m : nat) (delta : \bar R) :=
  metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) delta.

(** Source for [hausdorff_subcritical_metric_density_null]: direct
    null-locus assertion in 2.10.19(2), p. 181,
    allowing any omega satisfying the original infinity-
    cutoff specification. Positive rational thresholds
    and reciprocal cutoffs expand the printed exhaustion. *)
Theorem hausdorff_subcritical_metric_density_null (R : realType) (X : metricType R)
    (m : nat) (omega : set X -> \bar R) (A : set X) :
  is_metric_scale_envelope (fun j : nonempty_metric_sets X => val j)
    (fun j => hausdorff_diameter_cost m (val j)) +oo omega ->
  (forall d : \bar R, 0<d -> hausdorff_scale_measure m d A < +oo) ->
  hausdorff_measure m [set x | A x /\ upper_metric_density m (measure_restrict omega A) x<((2 : R)^+m)^-1%R%:E]=0.
Proof.
move=> homega hfinite.
pose J := @all_sets_hausdorff_generators R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := hausdorff_diameter_cost m (S j).
have hc j : 0<=c j := @hausdorff_diameter_cost_nonnegative R X m (S j).
have ho := hausdorff_all_sets_scale_specification homega.
have hpsi := @hausdorff_all_sets_limit_specification R X m.
have hm := caratheodory_limit_is_measure hpsi hc.
have how := metric_scale_envelope_is_measure ho hc.
have hmu := measure_restrict_is_measure how A.
have hInt : is_intersection_cost_family S c.
  move=> j k.
  pose l : J := @exist _ (fun B : set X => B \in [set: set X]) (S j `&` S k) (mem_set I).
  exists l; split=> //.
  apply: hausdorff_diameter_cost_monotone=> x [_ hx]; exact hx.
have hfinall d (hd : 0<d) : metric_scale_envelope S c d A < +oo.
  have hn := @metric_scale_envelope_specification R X (@nonempty_metric_sets R X)
    (fun j => val j) (fun j => hausdorff_diameter_cost m (val j)) d.
  have ha := @metric_scale_envelope_specification R X J S c d.
  rewrite -(hausdorff_all_sets_scale_values hn ha A).
  exact: hfinite d hd.
pose P : R := ((2 : R)^+m)%R.
have hP : (0<P)%R by rewrite /P exprn_gt0 // ltr0n.
have hPn : P!=0%R by rewrite gt_eqF.
pose K := [the choiceType of ((rat*nat)%type : Type)].
pose D : set K := [set p | (0<P*ratr p.1<1)%R].
pose d k := (((k.+1)%:R : R)^-1)%:E.
pose B (p : K) := caratheodory_density_good_set S c omega A (P*ratr p.1)%R (d p.2).
have hD : countable D := countableP D.
have hnull p (hp : D p) : hausdorff_measure m (B p)=0.
  exact: (@caratheodory_density_good_set_null R X J S c omega (hausdorff_measure m) A
    (P*ratr p.1)%R (d p.2) hc hInt ho hpsi hfinall hp (reciprocal_metric_cutoff_positive R p.2)).
pose E := [set x | A x /\ upper_metric_density m (measure_restrict omega A) x<P^-1%R%:E].
have hcover : E `<=` \bigcup_(p in D) B p.
  move=> x [hx hlim].
  have [q [huq hq]] := @extended_rationals_order_dense R
    (upper_metric_density m (measure_restrict omega A) x) P^-1%R%:E hlim.
  have hn := (@metric_densities_nonnegative R X m (measure_restrict omega A) x hmu).2.
  have hq0 : (0<(ratr q : R))%R by have hh := le_lt_trans hn huq; move: hh; rewrite lte_fin.
  have hqP : ((ratr q : R)<P^-1)%R by move: hq; rewrite lte_fin.
  have hp0 : (0<P*ratr q)%R := mulr_gt0 hP hq0.
  have hp1 : (P*ratr q<1)%R.
    have hh : (P*ratr q<P*P^-1)%R by rewrite ltr_pM2l.
    by rewrite mulfV in hh.
  have hp : (0<P*ratr q<1)%R by apply/andP.
  have [eta [heta hlocal]] := @metric_density_local_set_bound R X m (measure_restrict omega A) x (ratr q) hmu huq.
  have hEta : 0<eta%:E by rewrite lte_fin.
  have [k hk] := reciprocal_metric_cutoffs_cofinal hEta.
  exists (q,k)=> //; split=> // j hj hdiam.
  exact: hlocal (S j) hj (le_trans hdiam hk).
apply: (@measure_null_subset R X (hausdorff_measure m) hm E (\bigcup_(p in D) B p) hcover).
apply/eqP; rewrite eq_le (@measure_nonnegative R X (hausdorff_measure m) hm _) andbT.
have hh := @measure_indexed_cover R X K (hausdorff_measure m) hm (\bigcup_(p in D) B p) D B hD
  (fun x hx => hx).
by rewrite (nonnegative_sum_zero hnull) in hh.
Qed.

(** Source for [federer_2_10_19_2]: direct printed assertion
    of 2.10.19(2), p. 181, at integer degree,
    with the actual original phi_infinity and actual
    positive-cutoff approximations, including infinite cutoff. *)
Theorem federer_2_10_19_2 (R : realType) (X : metricType R) (m : nat) (A : set X) :
  (forall d : \bar R, 0<d -> hausdorff_scale_measure m d A < +oo) ->
  hausdorff_measure m [set x | A x /\ upper_metric_density m
    (measure_restrict (hausdorff_scale_measure m +oo) A) x<((2 : R)^+m)^-1%R%:E]=0.
Proof.
move=> hfinite; apply: hausdorff_subcritical_metric_density_null hfinite.
exact: metric_scale_envelope_specification.
Qed.
