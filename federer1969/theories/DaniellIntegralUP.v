(** Federer (1969), 2.5.5, printed pp. 96–97: additive, positively
    homogeneous functionals bounded above on each positive order interval
    and continuous on increasing sequences. Unlike 2.5.2, the functional
    itself need not preserve order. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP MonotoneDaniellIntegralUP ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [lattice_positive_order_interval]: the functions k in L with
    0 <= k <= f in Federer 2.5.5, p. 96, third hypothesis and variation
    formulas *)
Definition lattice_positive_order_interval (R : realType) (X : Type)
    (L : set (X -> R)) (f : X -> R) :=
  [set k | L k /\ function_nonnegative k /\ function_le k f].

(** Source for [is_daniell_integral]: exact four hypotheses of Federer
    2.5.5, p. 96, named in 2.5.6, p. 97 The last condition is ordinary
    convergence of functional values, not increasing convergence. *)
Record is_daniell_integral (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) : Prop := {
  (** Source for [daniell_integral_add]: first hypothesis of Federer 2.5.5, p.
    96 *)
  daniell_integral_add : forall f g, L f -> L g ->
    A (fun x => (f x+g x)%R)=(A f+A g)%R;
  (** Source for [daniell_integral_scale]: second hypothesis of Federer 2.5.5,
    p. 96 *)
  daniell_integral_scale : forall c f, (0 <= c)%R -> L f ->
    A (fun x => (c * f x)%R)=(c * A f)%R;
  (** Source for [daniell_integral_order_bounded]: third hypothesis of Federer
    2.5.5, p. 96 A finite upper bound expresses sup < infinity, including
    the vacuous case of an empty order interval. *)
  daniell_integral_order_bounded : forall f, L f -> exists b : R,
    forall k, lattice_positive_order_interval L f k -> (A k <= b)%R;
  (** Source for [daniell_integral_increasing_continuity]: fourth hypothesis
    of Federer 2.5.5, p. 96 *)
  daniell_integral_increasing_continuity : forall f g,
    (forall n, L (f n)) -> L g -> real_functions_increase_to f g ->
    extended_order_limit (fun n => (A (f n))%:E) (A g)%:E
}.
