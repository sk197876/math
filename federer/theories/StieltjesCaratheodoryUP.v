(** Federer (1969), 2.10.7, pp. 174–175: Caratheodory's construction on
    nonempty bounded open real intervals with cost g(b)-g(a) for
    nondecreasing g. Parameterise the family by ordered endpoint pairs and
    state its abstract covering specification before selecting a measure. We
    retain the printed Federer cost and make no such substitution at
    discontinuity endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CaratheodoryLimitUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [stieltjes_open_intervals]: direct
    family of nonempty bounded open intervals
    in Federer 2.10.7, p. 174. Endpoint
    order is part of the generator type. *)
Definition stieltjes_open_intervals (R : realType) : choiceType :=
  [the choiceType of {q : R*R | q \in [set q : R*R | q.1<q.2]}].

(** Source for [stieltjes_interval_set]: direct
    generator (a,b) of Federer 2.10.7,
    p. 174, represented in the given real
    metric and order topology. *)
Definition stieltjes_interval_set (R : realType) (j : stieltjes_open_intervals R) :
    set (real_line_metric R) := `](val j).1,(val j).2[.

(** Source for [stieltjes_interval_cost]: direct printed cost g(b)-g(a) in
    Federer 2.10.7, p. 174. *)
Definition stieltjes_interval_cost (R : realType) (g : R -> R)
    (j : stieltjes_open_intervals R) : \bar R :=
  (g (val j).2-g (val j).1)%:E.

(** Source for [is_stieltjes_caratheodory_measure]:
    direct abstract specification of the measure
    resulting from the interval family and
    printed cost in Federer 2.10.7, p. 174. *)
Definition is_stieltjes_caratheodory_measure (R : realType) (g : R -> R)
    (mu : set (real_line_metric R) -> \bar R) :=
  is_caratheodory_limit (@stieltjes_interval_set R) (stieltjes_interval_cost g) mu.
