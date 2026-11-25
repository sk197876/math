(** Federer (1969), 3.2.37, pp. 273--274: upper, lower and common
    m-dimensional Minkowski contents. The whole positive-radius domain
    is used. Actual unions of open balls give empty sets empty tubes,
    without assigning a finite distance to the empty set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  EuclideanBallVolume MetricOpenThickening PositiveRadiusLimits PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [minkowski_tube_quotient]: the normalized open-tube
    volume in the two displays of Federer 3.2.37, p. 273. The
    supporting expression is total; only positive radii enter contents. *)
Definition minkowski_tube_quotient (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R): \bar R :=
  @euclidean_lebesgue_measure R n (metric_open_thickening S r) /
    (euclidean_unit_ball_volume R (n-m)*r^+(n-m))%:E.

(** Source for [upper_minkowski_content]: the first display in
    Federer 3.2.37, p. 273, with the existing independently specified
    and sealed extended supremum and infimum operators. *)
Definition upper_minkowski_content (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) :=
  positive_radius_upper_limit (minkowski_tube_quotient m S).

(** Source for [lower_minkowski_content]: the second display in
    Federer 3.2.37, p. 273. Every positive real radius is retained. *)
Definition lower_minkowski_content (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) :=
  positive_radius_lower_limit (minkowski_tube_quotient m S).

(** Source for [minkowski_content]: the common value when the two
    contents agree, Federer 3.2.37, p. 273, final paragraph.
    The partial graph assigns no value when the contents differ. *)
Definition minkowski_content (R:realType) (n m:nat):
    partial_function (set (inner_metric_space (@euclidean_inner_productP R n))) (\bar R).
Proof.
refine (@Build_partial_function _ (\bar R)
  (fun S y=>upper_minkowski_content m S=y /\ lower_minkowski_content m S=y) _).
move=>S y z [hy _] [hz _]; exact:eq_trans (esym hy) hz.
Defined.

(** Source for [minkowski_content_graph]: the exact agreement domain
    and value of the common content, Federer 3.2.37, p. 273. *)
Lemma minkowski_content_graph (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) y:
  partial_function_graph (@minkowski_content R n m) S y <->
    upper_minkowski_content m S=y /\ lower_minkowski_content m S=y.
Proof. by []. Qed.

(** Source for [minkowski_contents_ordered]: supporting liminf <=
    limsup for Federer 3.2.37, pp. 273--274. No source measurability,
    boundedness or finiteness premise is imposed. *)
Lemma minkowski_contents_ordered (R:realType) (n m:nat)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  lower_minkowski_content m S<=upper_minkowski_content m S.
Proof. exact:positive_radius_limits_ordered. Qed.
