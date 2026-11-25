(** Federer (1969), 2.6.4, pp. 118–119: L1 closure of a linear space of
    summable total functions, supporting the tensor-image density assertion.
    Unlike a function lattice, the tensor image need not be closed under
    pointwise minima. We therefore specify approximation for an arbitrary
    linear subspace. its extra lattice closure is not assumed here. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals constructive_ereal.
From Federer Require Import ModuleQuotient SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_subspace_lone_approximable]: supporting
    explicit epsilon formulation of closure in the (alpha times beta)(1)
    seminorm in Federer 2.6.4, pp. 118–119. The
    actual finite integral of the absolute error is retained. *)
Definition is_subspace_lone_approximable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : subspace (GRing.Lmodule.clone R (X -> R^o) _)) (f : X -> R) :=
  summable_real_functions mu f /\ forall e : R, 0<e ->
    exists (h : X -> R) (q : R), L h /\
      is_measure_integral mu (real_total_integrand (fun x => `|h x-f x|)) q%:E /\ q<e.
