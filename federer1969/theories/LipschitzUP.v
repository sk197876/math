(** Federer (1969), 2.2.7, pp. 63–64: Lipschitz maps, their least constants
    and local Lipschitz regularity. Federer introduces positive bounds,
    whereas the least bound can be zero. We retain positive witnesses for
    Lipschitzian maps and use nonnegative bounds for the optimal constant.
    This convention also treats empty domains and constant maps. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_metric_lipschitz_bound]: Federer 2.2.7, pp. 63–64, the
    displayed distance inequality on a domain X. Paraphrase: the image
    distance is bounded by M times the original distance. Nonnegative M
    includes the optimal zero bound *)
Definition is_metric_lipschitz_bound (R : realType)
    (T U : metricType R) (X : set T) (f : T -> U) (M : R) : Prop :=
  0 <= M /\ forall x y, X x -> X y -> mdist (f x) (f y) <= M * mdist x y.

(** Source for [is_metric_lipschitz]: Federer 2.2.7,
    pp. 63–64, direct definition using a finite positive real bound.
    A relative carrier X permits the empty domain and restrictions
    without introducing an inhabitance hypothesis. *)
Definition is_metric_lipschitz (R : realType)
    (T U : metricType R) (X : set T) (f : T -> U) : Prop :=
  exists M, 0 < M /\ is_metric_lipschitz_bound X f M.

(** Source for [is_least_metric_lipschitz_constant]: Federer 2.2.7, p. 64,
    first paragraph: the least Lipschitz constant Lip(f). Abstract
    specification by attainment and minimality *)
Record is_least_metric_lipschitz_constant (R : realType)
    (T U : metricType R) (X : set T) (f : T -> U) (L : R) : Prop := {
  least_metric_lipschitz_bound : is_metric_lipschitz_bound X f L;
  least_metric_lipschitz_minimal : forall M,
    is_metric_lipschitz_bound X f M -> L <= M
}.

(** Source for [is_locally_metric_lipschitz]: Federer 2.2.7,
    p. 64, second paragraph; each point has a neighborhood on which
    the restriction is Lipschitzian. Ambient neighborhoods intersected
    with X express neighborhoods in the relative domain topology. *)
Definition is_locally_metric_lipschitz (R : realType)
    (T U : metricType R) (X : set T) (f : T -> U) : Prop :=
  forall x, X x -> exists V, nbhs x V /\ is_metric_lipschitz (X `&` V) f.
