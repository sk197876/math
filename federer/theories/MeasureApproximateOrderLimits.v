(** Federer (1969), 2.9.12, p. 159, upper and lower approximate limits with
    values in the extended real line. Apply the May 1987 erratum, p. 3, book
    p. 159 line 7: the upper exceptional set is the complement of the
    preimage of the closed lower ray. Thus it includes undefined inputs.
    here thresholds belong to Federer's extended real target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP MeasureSetDensity ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [measure_approximate_upper_thresholds]: direct
    threshold set in Federer 2.9.12, p. 159, second paragraph,
    corrected by erratum p. 3, book p. 159 line 7. Undefined
    points are included in X minus the closed lower-ray preimage. *)
Definition measure_approximate_upper_thresholds (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x : set (\bar R) :=
  [set t | partial_function_graph (measure_set_density phi V
    (~` partial_function_preimage f [set y | y<=t])) x 0].

(** Source for [measure_approximate_lower_thresholds]: direct
    order-dual threshold set for the approximate lower limit in
    Federer 2.9.12, p. 159. The word "similarly" is expanded
    using the complement of the closed upper-ray preimage,
    consistently with the erratum p. 3, book p. 159 line 7. *)
Definition measure_approximate_lower_thresholds (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x : set (\bar R) :=
  [set t | partial_function_graph (measure_set_density phi V
    (~` partial_function_preimage f [set y | t<=y])) x 0].

(** Source for [is_measure_approximate_upper_limit]: abstract
    greatest-lower-bound specification of the approximate upper
    limit in Federer 2.9.12, p. 159. The threshold predicate
    incorporates the erratum p. 3, book p. 159 line 7. *)
Definition is_measure_approximate_upper_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x c :=
  (forall t, measure_approximate_upper_thresholds phi V f x t -> c<=t) /\
  (forall d, (forall t, measure_approximate_upper_thresholds phi V f x t -> d<=t) -> d<=c).

(** Source for [is_measure_approximate_lower_limit]: abstract
    least-upper-bound specification of the order-dual definition
    in Federer 2.9.12, p. 159. It is meaningful also for
    an empty feasible threshold set. *)
Definition is_measure_approximate_lower_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x c :=
  (forall t, measure_approximate_lower_thresholds phi V f x t -> t<=c) /\
  (forall d, (forall t, measure_approximate_lower_thresholds phi V f x t -> t<=d) -> c<=d).

(** Source for [measure_approximate_upper_limit]: direct
    infimum definition in Federer 2.9.12, p. 159, with the
    corrected exceptional set (erratum p. 3, p. 159 line 7).
    Existence uses only the sealed extended-real bound interface. *)
Definition measure_approximate_upper_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x :=
  extended_real_inf (measure_approximate_upper_thresholds phi V f x).

(** Source for [measure_approximate_lower_limit]: direct
    supremum definition, expanding "similarly" in Federer
    2.9.12, p. 159, with the dual corrected exceptional set. *)
Definition measure_approximate_lower_limit (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x :=
  extended_real_sup (measure_approximate_lower_thresholds phi V f x).

(** Source for [measure_approximate_upper_limit_law]: existence
    and defining infimum laws for Federer 2.9.12, p. 159,
    including an empty feasible threshold set, by 2.1.1, p. 51. *)
Lemma measure_approximate_upper_limit_law (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x :
  is_measure_approximate_upper_limit phi V f x (measure_approximate_upper_limit phi V f x).
Proof.
split; [exact: extended_real_inf_lower|exact: extended_real_inf_greatest].
Qed.

(** Source for [measure_approximate_lower_limit_law]: existence
    and defining supremum laws for Federer 2.9.12, p. 159,
    including an empty feasible threshold set, by 2.1.1, p. 51. *)
Lemma measure_approximate_lower_limit_law (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x :
  is_measure_approximate_lower_limit phi V f x (measure_approximate_lower_limit phi V f x).
Proof.
split; [exact: extended_real_sup_upper|exact: extended_real_sup_least].
Qed.

(** Source for [measure_approximate_upper_limit_unique]:
    supporting uniqueness of the greatest lower bound in
    Federer 2.9.12, p. 159; this is order antisymmetry. *)
Lemma measure_approximate_upper_limit_unique (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x c :
  is_measure_approximate_upper_limit phi V f x c -> c=measure_approximate_upper_limit phi V f x.
Proof.
move=> [hlo hgreat]; have [hlo' hgreat'] := measure_approximate_upper_limit_law phi V f x.
apply/eqP; by rewrite eq_le (hgreat' c hlo) (hgreat _ hlo').
Qed.

(** Source for [measure_approximate_lower_limit_unique]:
    supporting uniqueness of the least upper bound in
    Federer 2.9.12, p. 159; this is order antisymmetry. *)
Lemma measure_approximate_lower_limit_unique (R : realType) (X : metricType R)
    (phi : set X -> \bar R) (V : X -> set X -> Prop)
    (f : partial_function X (\bar R)) x c :
  is_measure_approximate_lower_limit phi V f x c -> c=measure_approximate_lower_limit phi V f x.
Proof.
move=> [hup hleast]; have [hup' hleast'] := measure_approximate_lower_limit_law phi V f x.
apply/eqP; by rewrite eq_le (hleast _ hup') (hleast' c hup).
Qed.
