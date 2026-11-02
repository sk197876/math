(** Federer (1969), 2.3.5, pp. 76–77: finite disjoint closed pieces with
    small image oscillation and small residual. The oscillation formulation
    retains both values in one small target partition member; it avoids
    choosing values for empty pieces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP SetSequenceDisjointification.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [is_lusin_piece_system]: abstract supporting data
    E_{i,j} and J(i) of Federer 2.3.5, pp. 76–77. A zero
    prefix and empty pieces are permitted. The diameter condition
    implies the finite-step approximation estimate in the printed proof. *)
Record is_lusin_piece_system (R : realType) (X : topologicalType)
    (Y : metricType R) (mu : set X -> \bar R) (A : set X)
    (f : partial_function X Y) (eta delta : R) (N : nat)
    (E : nat -> set X) : Prop := {
  (** Source for [lusin_piece_closed]: closed pieces in Federer
      2.3.5, p. 76, second proof display. *)
  lusin_piece_closed : forall n, (n < N)%N -> closed (E n);
  (** Source for [lusin_piece_within]: containment of the pieces in A and the
    function domain, Federer 2.3.5, p. 76 *)
  lusin_piece_within : forall n, (n < N)%N -> E n `<=` A `&` partial_function_domain f;
  (** Source for [lusin_piece_disjoint]: disjoint pieces in
      Federer 2.3.5, p. 76. *)
  lusin_piece_disjoint : forall n m, (n < N)%N -> (m < N)%N -> n != m ->
    forall x, E n x -> E m x -> False;
  (** Source for [lusin_piece_oscillation]: supporting two-value
      bound from the small target partition in Federer 2.3.5,
      pp. 76–77. This is not a separately stated book lemma. *)
  lusin_piece_oscillation : forall n, (n < N)%N -> forall x z y w,
    E n x -> E n z -> partial_function_graph f x y ->
    partial_function_graph f z w -> (mdist y w <= eta)%R;
  (** Source for [lusin_piece_error]: finite-union residual bound
      in Federer 2.3.5, p. 76, final display. *)
  lusin_piece_error : mu (A `\` set_sequence_prefix E N) < delta%:E
}.
