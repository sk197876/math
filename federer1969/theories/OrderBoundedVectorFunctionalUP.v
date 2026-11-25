(** Federer (1969), 2.5.14, p. 108, vector-representation paragraph: the
    compactness argument of 2.5.13 removes the decreasing-sequence
    continuity condition in 2.5.12(5), p. 103. Linearity and the finite
    bounds on the displayed variation suprema remain explicit here: the
    argument uses lambda(f)<infinity and cannot establish representation of
    an arbitrary nonlinear or unbounded map. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import FunctionLatticeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_order_bounded_vector_functional]: the linearity
    and finite variation bounds of Federer 2.5.12(5), p. 103,
    retained for the compact-support extension of 2.5.14, p. 108.
    Sequential continuity is deliberately a later conclusion. *)
Record is_order_bounded_vector_functional (R : realType) (X : Type)
    (E : lmodType R) (N : E -> R) (L : set (X -> R)) (Q : set (X -> E))
    (T : (X -> E) -> R) : Prop := {
  (** Source for [order_bounded_vector_add]: linearity in Federer
      2.5.12(5), p. 103, used in 2.5.14, p. 108. *)
  order_bounded_vector_add : forall w v, Q w -> Q v -> T (fun x=>w x+v x)=T w+T v;
  (** Source for [order_bounded_vector_scale]: homogeneity in
      Federer 2.5.12(5), p. 103, used in 2.5.14, p. 108. *)
  order_bounded_vector_scale : forall c w, Q w -> T (fun x=>c*:w x)=c*T w;
  (** Source for [order_bounded_vector_bound]: finite upper bounds
      for lambda(f) in Federer 2.5.12(5), p. 103, as required
      by the compactness estimate invoked in 2.5.14, p. 108. *)
  order_bounded_vector_bound : forall f, positive_function_lattice L f ->
    exists c : R, forall w, Q w -> function_le (fun x=>N (w x)) f -> T w<=c
}.
