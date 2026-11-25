(** Federer (1969), 2.10.5(1)–(2), p. 173, definitions, paraphrased: apply
    Caratheodory's construction to zeta_t on all Borel sets to obtain I_t^m,
    and on all open convex sets to obtain Q_t^m. Closed convex generators
    give the same Q; specify that construction independently so equality
    remains a theorem. The target has positive m<=n and 1<=t<=infinity;
    supporting interfaces retain the already declared degree-zero Lebesgue
    convention. Source context and absence of a corresponding. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric IntegralGeometricGauge
  ProjectionMeasureUP BorelCoverCostUP CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_integral_geometric_measure]:
    direct abstract covering specification of
    I_t^m in Federer 2.10.5(1), p. 173,
    with all Borel generators and the actual zeta_t. *)
Definition is_integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n)) => val j)
    (fun j => @integral_geometric_gauge R n m hmn t (val j)) mu.

(** Source for [is_convex_integral_geometric_measure]:
    direct abstract covering specification of
    Q_t^m in Federer 2.10.5(2), p. 173,
    with open convex generators and the actual zeta_t. *)
Definition is_convex_integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit (fun j : open_convex_euclidean_sets R n => val j)
    (fun j => @integral_geometric_gauge R n m hmn t (val j)) mu.

(** Source for [is_closed_convex_integral_geometric_measure]:
    independent specification for the closed convex
    alternative in Federer 2.10.5(2), p. 173.
    Equality with Q_t is a separate obligation. *)
Definition is_closed_convex_integral_geometric_measure (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (t : \bar R)
    (mu : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :=
  is_caratheodory_limit (fun j : closed_convex_euclidean_sets R n => val j)
    (fun j => @integral_geometric_gauge R n m hmn t (val j)) mu.
