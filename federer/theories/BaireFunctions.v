(** Federer (1969), 2.2.15, p. 70: public Baire functions and their defining
    closure and minimality consequences. All statements use only the sealed
    abstract specification. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PointwiseLimit BaireFunctionUP BaireFunctionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_baire_function]: direct public predicate
    for the Baire functions defined in Federer 2.2.15,
    p. 70, exposed through the sealed smallest-class laws. *)
Definition is_baire_function (R : realType) (X : topologicalType) (Y : metricType R)
    (f : X -> Y) : Prop := @BaireFunction.value R X Y f.

(** Source for [baire_functions_specification]: public defining
    laws of the family in Federer 2.2.15, p. 70. *)
Lemma baire_functions_specification (R : realType) (X : topologicalType) (Y : metricType R) :
  is_baire_function_family (@is_baire_function R X Y).
Proof. exact: BaireFunction.laws. Qed.

(** Source for [continuous_baire_function]: direct generator
    inclusion in the definition in Federer 2.2.15, p. 70. *)
Lemma continuous_baire_function (R : realType) (X : topologicalType) (Y : metricType R)
    (f : X -> Y) : continuous f -> is_baire_function f.
Proof. exact: (@baire_family_continuous R X Y (@is_baire_function R X Y)
  (@baire_functions_specification R X Y) f). Qed.

(** Source for [baire_function_pointwise_limit]: direct sequential
    closure in Federer 2.2.15, p. 70. Each source
    point may have its own rate of convergence. *)
Lemma baire_function_pointwise_limit (R : realType) (X : topologicalType) (Y : metricType R)
    (f : nat -> X -> Y) (g : X -> Y) :
  (forall n, is_baire_function (f n)) -> is_pointwise_limit f g -> is_baire_function g.
Proof. exact: (@baire_family_closed R X Y (@is_baire_function R X Y)
  (@baire_functions_specification R X Y) f g). Qed.

(** Source for [baire_function_induction]: supporting minimality
    principle for Federer 2.2.15, p. 70. A property
    of maps holds for all Baire functions if it includes every
    continuous map and is preserved by pointwise sequential limits. *)
Theorem baire_function_induction (R : realType) (X : topologicalType) (Y : metricType R)
    (G : set (X -> Y)) : is_baire_class G ->
  (forall f, continuous f -> G f) -> forall f, is_baire_function f -> G f.
Proof. exact: (@baire_family_least R X Y (@is_baire_function R X Y)
  (@baire_functions_specification R X Y) G). Qed.
