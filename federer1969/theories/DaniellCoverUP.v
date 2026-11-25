(** Federer (1969), proof of 2.5.2, p. 92: increasing positive lattice
    sequences that suit a set, and the infimum of their limiting functional
    values. The specifications below precede existence and measure laws.
    Natural-number sequences start at zero rather than one; this reindexing
    changes no monotonicity or limiting requirement. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import FunctionLatticeUP ExtendedRealBoundsUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_daniell_suiting_sequence]: the sequence that 'suits A' in
    Federer 2.5.2, p. 92 For an increasing sequence, limit at least one is
    expressed by eventually exceeding every real number below one, without
    choosing its limit in the definition. *)
Definition is_daniell_suiting_sequence (R : realType) (X : Type)
    (L : set (X -> R)) (S : set X) (f : nat -> X -> R) :=
  (forall n, positive_function_lattice L (f n)) /\
  (forall n m, (n <= m)%N -> function_le (f n) (f m)) /\
  (forall x, S x -> forall r : R, (r < 1)%R -> exists n, (r < f n x)%R).

(** Source for [is_daniell_sequence_cost]: the limit of functional values in
    Federer's measure formula, 2.5.2, p. 92 *)
Definition is_daniell_sequence_cost (R : realType) (X : Type)
    (A : (X -> R) -> R) (f : nat -> X -> R) (c : \bar R) :=
  is_extended_real_supremum [set z | exists n, z=(A (f n))%:E] c.

(** Source for [is_daniell_cover_envelope]: abstract infimum specification
    for phi(A) in Federer 2.5.2, p. 92 Being a measure is a subsequent
    theorem, not a premise of this specification. *)
Record is_daniell_cover_envelope (R : realType) (X : Type)
    (L : set (X -> R)) (A : (X -> R) -> R) (mu : set X -> \bar R) : Prop := {
  (** Source for [daniell_cover_lower]: every suiting-sequence cost bounds
    phi(A) in Federer 2.5.2, p. 92 *)
  daniell_cover_lower : forall S f c, is_daniell_suiting_sequence L S f ->
    is_daniell_sequence_cost A f c -> mu S <= c;
  (** Source for [daniell_cover_greatest]: greatest-lower-bound clause of the
    same defining infimum in Federer 2.5.2, p. 92 *)
  daniell_cover_greatest : forall S b,
    (forall f c, is_daniell_suiting_sequence L S f -> is_daniell_sequence_cost A f c -> b <= c) -> b <= mu S
}.
