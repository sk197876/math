(** Federer (1969), 3.3.15, p. 299: the original positive
    upper-density strata, including infinite upper density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MetricDensities MetricUpperDensityBorel ExtendedRealOrderTopology CountableOrderIntervals
  BorelFunctionUP TopologicalBorel ExtendedRealReciprocalBounds HausdorffMeasure
  FiniteUpperDensityHausdorffBound MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_density_threshold]: positive reciprocal
    thresholds i inverse in Federer 3.3.15, p. 299. Natural index
    zero denotes printed positive index one; no threshold zero is used. *)
Definition structure_density_threshold (R:realType) (i:nat):R:=((i.+1)%:R:R)^-1.

(** Source for [structure_upper_density_stratum]: original E_i in
    Federer 3.3.15, p. 299: original points whose actual upper
    m density exceeds the positive reciprocal threshold. Neither
    rectifiability nor measurability is part of this definition. *)
Definition structure_upper_density_stratum (R:realType) (X:metricType R) m
    (psi:set X->\bar R) (i:nat):set X:=
  [set x|(structure_density_threshold R i)%:E<upper_metric_density m psi x]%E.

(** Source for [structure_density_threshold_positive]: supporting
    positivity of the printed thresholds in Federer 3.3.15, p. 299. *)
Lemma structure_density_threshold_positive (R:realType) i:
  (0<structure_density_threshold R i)%R.
Proof. by rewrite /structure_density_threshold invr_gt0 ltr0n. Qed.

(** Source for [structure_density_stratum_borel]: the original
    Borel assertion for E_i in Federer 3.3.15, p. 299. Apply actual
    upper-density Borel measurability and the actual strict order ray. *)
Lemma structure_density_stratum_borel (R:realType) (X:metricType R) m
    (psi:set X->\bar R) i:
  is_measure psi ->borel_set (structure_upper_density_stratum m psi i).
Proof.
move=>hPsi.
have hBorel:=@metric_upper_density_borel R X m psi hPsi.
exact:(hBorel [set u:extended_real_line R|(structure_density_threshold R i)%:E<u]%E
  (@order_strict_upper_ray_open _ [the orderTopologicalType _ of order_topology (\bar R)]
    (structure_density_threshold R i)%:E)).
Qed.

(** Source for [structure_density_strata_union]: supporting
    exhaustion in the last paragraph of Federer 3.3.15, p. 299.
    The original positive-upper-density locus is exactly the union
    of the original E_i; positive infinite densities are retained. *)
Lemma structure_density_strata_union (R:realType) (X:metricType R) m
    (psi:set X->\bar R):
  (\bigcup_i structure_upper_density_stratum m psi i)=
    [set x|(0<upper_metric_density m psi x)%E].
Proof.
apply/seteqP; split=>x.
- move=>[i _ hAbove].
  have hPositive:(0<(structure_density_threshold R i)%:E)%E.
    rewrite lte_fin; exact:structure_density_threshold_positive.
  exact:lt_trans hPositive hAbove.
- move=>hPositive.
  have [q [hQ0 hQDensity]]:=@extended_rationals_order_dense R 0%E _ hPositive.
  have hQPositive:(0<(ratr q:R))%R:=hQ0.
  have [i hSmall]:=positive_reciprocal_nat_small hQPositive.
  exists i; first exact:Logic.I.
  apply:lt_trans _ hQDensity.
  by rewrite /structure_density_threshold lte_fin.
Qed.

(** Source for [structure_density_stratum_hausdorff_bound]: actual
    H^m(B)<=i*psi(B) in Federer 3.3.15, p. 299, for EVERY original
    B contained in E_i. Actual open approximation and 2.10.19(3)
    discharge all premises. This includes nonmeasurable B. *)
Lemma structure_density_stratum_hausdorff_bound (R:realType) (X:metricType R) m
    (psi:set X->\bar R) i (B:set X):
  is_measure psi ->is_borel_regular_measure psi ->(psi setT< +oo)%E ->
  B `<=` structure_upper_density_stratum m psi i ->
  (@hausdorff_measure R X m B<=
    (structure_density_threshold R i)^-1%R%:E*psi B)%E.
Proof.
move=>hPsi hRegular hFinite hSub.
apply:(@finite_upper_density_hausdorff_bound R X m psi B
  (structure_density_threshold R i) hPsi hRegular hFinite
  (@structure_density_threshold_positive R i)).
by move=>x hx; exact:hSub x hx.
Qed.
