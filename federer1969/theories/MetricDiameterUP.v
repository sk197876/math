(** Federer (1969), 2.10.1, pp. 169–170, and 2.10.2(1), p. 171: diameters
    control the admissible covers and their costs. This order specification
    supplies the diameter used by the Hausdorff-length example in 2.5.10, p.
    101. We use zero for the empty set; the Hausdorff construction itself
    uses nonempty sets. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_extended_metric_diameter]: abstract least
    nonnegative upper bound of pairwise distances, supporting
    the diameter condition in Federer 2.10.1, p. 170.
    The zero lower bound makes the empty-set convention explicit. *)
Record is_extended_metric_diameter (R : realType) (X : metricType R)
    (A : set X) (d : \bar R) : Prop := {
  (** Source for [metric_diameter_nonnegative]: supporting
      nonnegativity of the cost in Federer 2.10.2, p. 171. *)
  metric_diameter_nonnegative : 0 <= d;
  (** Source for [metric_diameter_upper]: the pairwise distance
      bound implicit in diam S <= delta, Federer 2.10.1, p. 170. *)
  metric_diameter_upper : forall x y, A x -> A y -> (mdist x y)%:E <= d;
  (** Source for [metric_diameter_least]: least-bound clause for
      the diameter used in Federer 2.10.1, p. 170. *)
  metric_diameter_least : forall b, 0 <= b ->
    (forall x y, A x -> A y -> (mdist x y)%:E <= b) -> d <= b
}.

(** Source for [metric_diameter_unique]: supporting uniqueness
    from the diameter's order specification; Federer 2.10.1,
    p. 170, uses a uniquely determined diameter. *)
Lemma metric_diameter_unique (R : realType) (X : metricType R)
    (A : set X) (a b : \bar R) :
  is_extended_metric_diameter A a -> is_extended_metric_diameter A b -> a=b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (metric_diameter_least ha (metric_diameter_nonnegative hb)
    (metric_diameter_upper hb)).
- exact: (metric_diameter_least hb (metric_diameter_nonnegative ha)
    (metric_diameter_upper ha)).
Qed.
