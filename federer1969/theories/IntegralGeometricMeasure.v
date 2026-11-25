(** Federer (1969), 2.10.5(1)–(2), p. 173: select the three independently
    specified Caratheodory constructions from the actual normalized
    projected-volume gauge. Use the existing generic seal and its abstract
    laws; no construction or existence is assumed. Generator nonnegativity
    and Borel regularity are proved for every exponent t>=1. Source context
    and dimensional scope: IntegralGeometricMeasureUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricGauge
  IntegralGeometricMeasureUP ProjectionMeasureUP SuslinSetUP BorelClosedProjection
  CaratheodoryMeasure CaratheodoryLimitUP CaratheodoryLimitMeasure
  CaratheodoryBorelRegular BorelCaratheodoryMeasure BorelCoverCostUP
  TopologicalBorel MeasureUP BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_measure]: direct
    I_t^m of Federer 2.10.5(1), p. 173,
    using the actual gauge and all Borel generators. *)
Definition integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :=
  borel_caratheodory_measure (@integral_geometric_gauge R n m hmn t).

(** Source for [integral_geometric_measure_specification]:
    the covering laws of I_t^m in Federer
    2.10.5(1), p. 173, supplied by the
    existing generic Caratheodory seal. *)
Lemma integral_geometric_measure_specification (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  is_integral_geometric_measure hmn t (@integral_geometric_measure R n m hmn t).
Proof. exact: borel_caratheodory_specification. Qed.

(** Source for [integral_geometric_measure_is_measure]:
    direct measure assertion for I_t^m in Federer
    2.10.5(1), p. 173. Borel sets are Suslin
    by 2.2.10, p. 66, so every generator
    has the proved nonnegative zeta_t cost. *)
Theorem integral_geometric_measure_is_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_measure (@integral_geometric_measure R n m hmn t).
Proof.
move=> ht; apply: (caratheodory_limit_is_measure
  (@integral_geometric_measure_specification R n m hmn t))=> j.
apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
exact: (@metric_borel_suslin R (inner_metric_space (@euclidean_inner_productP R n))
  (val j) (set_valP j)).
Qed.

(** Source for [integral_geometric_measure_borel_regular]:
    supporting Borel regularity of I_t^m in Federer
    2.10.5(1), p. 173, by the Borel-generator
    theorem 2.10.1, p. 170. *)
Theorem integral_geometric_measure_borel_regular (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_borel_regular_measure (@integral_geometric_measure R n m hmn t).
Proof.
move=> ht; apply: (caratheodory_limit_borel_regular
  (@integral_geometric_measure_specification R n m hmn t)).
- move=> j; apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
  exact: (@metric_borel_suslin R (inner_metric_space (@euclidean_inner_productP R n))
    (val j) (set_valP j)).
- move=> j; exact: set_valP j.
Qed.

(** Source for [convex_integral_geometric_measure]:
    direct Q_t^m of Federer 2.10.5(2), p. 173,
    using open convex generators and the actual gauge. *)
Definition convex_integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :=
  caratheodory_measure (fun j : open_convex_euclidean_sets R n => val j)
    (fun j => @integral_geometric_gauge R n m hmn t (val j)).

(** Source for [convex_integral_geometric_measure_specification]:
    the independent covering laws of Q_t^m in
    Federer 2.10.5(2), p. 173. *)
Lemma convex_integral_geometric_measure_specification (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  is_convex_integral_geometric_measure hmn t (@convex_integral_geometric_measure R n m hmn t).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [convex_integral_geometric_measure_is_measure]:
    direct measure assertion for Q_t^m in Federer
    2.10.5(2), p. 173, with nonnegative costs
    proved on its open, hence Suslin, generators. *)
Theorem convex_integral_geometric_measure_is_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_measure (@convex_integral_geometric_measure R n m hmn t).
Proof.
move=> ht; apply: (caratheodory_limit_is_measure
  (@convex_integral_geometric_measure_specification R n m hmn t))=> j.
apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
apply: metric_borel_suslin; exact: open_borel_set (set_valP j).1.
Qed.

(** Source for [convex_integral_geometric_measure_borel_regular]:
    supporting Borel regularity of Q_t^m in Federer
    2.10.5(2), p. 173, since its actual
    open convex generators are Borel. *)
Theorem convex_integral_geometric_measure_borel_regular (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  1<=t -> is_borel_regular_measure (@convex_integral_geometric_measure R n m hmn t).
Proof.
move=> ht; apply: (caratheodory_limit_borel_regular
  (@convex_integral_geometric_measure_specification R n m hmn t)).
- move=> j; apply: (@integral_geometric_gauge_nonnegative R n m hmn t ht (val j)).
  apply: metric_borel_suslin; exact: open_borel_set (set_valP j).1.
- move=> j; exact: open_borel_set (set_valP j).1.
Qed.

(** Source for [closed_convex_integral_geometric_measure]:
    independent closed convex construction from
    Federer 2.10.5(2), p. 173. Equality with
    Q_t remains a separate theorem. *)
Definition closed_convex_integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :=
  caratheodory_measure (fun j : closed_convex_euclidean_sets R n => val j)
    (fun j => @integral_geometric_gauge R n m hmn t (val j)).

(** Source for [closed_convex_integral_geometric_measure_specification]:
    covering laws of the independent closed convex
    alternative in Federer 2.10.5(2), p. 173. *)
Lemma closed_convex_integral_geometric_measure_specification (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R) :
  is_closed_convex_integral_geometric_measure hmn t
    (@closed_convex_integral_geometric_measure R n m hmn t).
Proof. exact: caratheodory_measure_specification. Qed.

(** Source for [gillespie_measure]: direct name for
    Q_1^m in Federer 2.10.5(2), p. 173. *)
Definition gillespie_measure (R : realType) (n m : nat) (hmn : (m<=n)%N) :=
  @convex_integral_geometric_measure R n m hmn 1.
