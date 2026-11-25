(** Federer (1969), 2.10.44, printed p. 202, final paragraph and displayed
    infimum formula: g(x)=inf{f(a)+L dist(x,a):a in S}. Specify the envelope
    by its upper and greatest- lower-bound laws before constructing it.
    Agreement, global Lipschitz bounds and optimality are later
    consequences. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [mcshane_costs_at]: direct set under
    the infimum in the final formula of 2.10.44,
    p. 202. A supplied finite real bound L
    is used; the final theorem takes the optimal bound. *)
Definition mcshane_costs_at (R : realType) (X : metricType R)
    (S : set X) (f : X -> R) (L : R) (x : X) : set R :=
  [set r | exists a, S a /\ r=f a+L*mdist x a].

(** Source for [is_mcshane_envelope]: abstract infimum
    specification of the extension formula in 2.10.44,
    p. 202. Only the two real order laws are
    fields; no agreement or Lipschitz conclusion is assumed. *)
Record is_mcshane_envelope (R : realType) (X : metricType R)
    (S : set X) (f : X -> R) (L : R) (g : X -> R) : Prop := {
  (** Source for [mcshane_envelope_upper_law]: direct
      infimum upper bound by each prescribed cost
      in 2.10.44, p. 202. *)
  mcshane_envelope_upper_law : forall x a, S a -> g x<=f a+L*mdist x a;
  (** Source for [mcshane_envelope_greatest_law]: supporting
      greatest-lower-bound characterisation of the infimum
      in 2.10.44, p. 202. *)
  mcshane_envelope_greatest_law : forall x z,
    (forall a, S a -> z<=f a+L*mdist x a) -> z<=g x
}.
