(** Federer (1969), 3.2.20, p. 257: the two applications
    of 3.2.5(2) first transport finite real weights. This independent
    predicate records precisely that equality of integral value graphs;
    the extended-weight consequence is proved separately. *)
From mathcomp Require Import all_boot classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [is_finite_weight_integral_transport]: supporting
    specification of the finite-real-weight transformation used in
    Federer 3.2.20, p. 257, via 3.2.5(2), pp. 244–245.
    The nonnegative finite densities are supplied separately. This is
    a predicate whose hypotheses must be proved, not a project axiom. *)
Definition is_finite_weight_integral_transport (R : realType) (X Y : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (f : X -> Y) (p : X -> R) (q : Y -> R) : Prop :=
  forall (h : Y -> R) a,
    is_measure_integral mu (partial_function_total (fun x=>(h (f x))%:E* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>(h y)%:E* (q y)%:E : extended_real_line R)) a.

(** Source for [is_finite_weight_pair_transport]: supporting symmetric
    version of the same finite-weight transformation in Federer
    3.2.20, p. 257. Two parametrizations of a common weight
    space allow the monotone-limit proof to be applied in either direction. *)
Definition is_finite_weight_pair_transport (R : realType) (X Y Z : choiceType)
    (mu : set X -> \bar R) (nu : set Y -> \bar R)
    (u : X -> Z) (v : Y -> Z) (p : X -> R) (q : Y -> R) : Prop :=
  forall (h : Z -> R) a,
    is_measure_integral mu (partial_function_total (fun x=>(h (u x))%:E* (p x)%:E : extended_real_line R)) a <->
    is_measure_integral nu (partial_function_total (fun y=>(h (v y))%:E* (q y)%:E : extended_real_line R)) a.
