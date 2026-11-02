(** Federer (1969), 2.10.40, printed pp. 199–200: minimise the common
    dilation t for a compact nonempty family of balls with positive radii.
    Specify feasibility and minimality before constructing a witness;
    uniqueness and the contact-centre convex hull conclusion are later
    consequences, not fields. The working erratum has no entry for pp.
    199–200. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [positive_ball_parameter_family]: direct
    positivity requirement on P in 2.10.40,
    p. 199. Real radii are already finite;
    positivity is a property, not a chosen representation. *)
Definition positive_ball_parameter_family (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R)) :=
  forall p, P p -> 0<p.2.

(** Source for [weighted_ball_centres]: direct Y_t in
    2.10.40, p. 199. In words, a centre
    is within r t of every prescribed centre a.
    Subsequent minimum laws explicitly require t nonnegative. *)
Definition weighted_ball_centres (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R)) (t : R) :=
  [set y : inner_metric_space (@euclidean_inner_productP R n) |
    forall p, P p -> inner_norm (@euclidean_inner_productP R n) (y-p.1)<=p.2*t].

(** Source for [weighted_ball_contact_centres]: direct
    contact-centre family A in 2.10.40, p. 199.
    An original centre a is a contact centre when
    one of its prescribed balls meets the minimising centre
    at distance r c. No convex hull property is assumed. *)
Definition weighted_ball_contact_centres (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R))
    (b : inner_metric_space (@euclidean_inner_productP R n)) (c : R) :=
  [set a | exists r, P (a,r) /\ inner_norm (@euclidean_inner_productP R n) (b-a)=r*c].

(** Source for [weighted_ball_minimum_data]: supporting
    centre and scale data for 2.10.40, pp. 199–200.
    The mathematical properties are specified separately. *)
Record weighted_ball_minimum_data (R : realType) n := {
  (** Source for [weighted_minimum_centre]: supporting
      minimising centre b of 2.10.40, p. 199. *)
  weighted_minimum_centre : inner_metric_space (@euclidean_inner_productP R n);
  (** Source for [weighted_minimum_scale]: supporting
      least feasible dilation c of 2.10.40, p. 199. *)
  weighted_minimum_scale : R
}.

(** Source for [is_weighted_ball_minimum]: supporting
    order specification of the minimum in 2.10.40,
    pp. 199–200. Only nonnegative scale, feasibility
    and leastness are laws. Existence is proved separately;
    no uniqueness or convex-hull conclusion is postulated. *)
Record is_weighted_ball_minimum (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R))
    (D : weighted_ball_minimum_data R n) : Prop := {
  (** Source for [weighted_minimum_scale_nonnegative_law]: direct
      nonnegative dilation convention in 2.10.40, p. 199. *)
  weighted_minimum_scale_nonnegative_law : 0<=weighted_minimum_scale D;
  (** Source for [weighted_minimum_feasible_law]: direct
      b in Y_c assertion of 2.10.40, p. 199,
      stated without assuming that Y_c is a singleton. *)
  weighted_minimum_feasible_law : weighted_ball_centres P (weighted_minimum_scale D)
    (weighted_minimum_centre D);
  (** Source for [weighted_minimum_least_law]: supporting
      least feasible nonnegative dilation in 2.10.40,
      pp. 199–200. The infimum identification follows
      from feasibility and this order property. *)
  weighted_minimum_least_law : forall t y, 0<=t -> weighted_ball_centres P t y ->
    weighted_minimum_scale D<=t
}.
