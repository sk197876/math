(** Federer (1969), 1.10.5, pp. 47-48: suprema defining form and polynomial
    norms in arbitrary normed spaces. These can be infinite in infinite
    dimension. This supporting least-upper-bound specification uses extended
    real arithmetic as order background only; no external theorem about
    norms or multilinear maps is used. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_extended_supremum]: Federer 1.10.5,
    pp. 47-48, supporting specification of the displayed suprema.
    The value is an upper bound for the real values and is below every
    extended upper bound. This characterizes finite and infinite cases. *)
Record is_extended_supremum (R : realType) (S : set R) (c : \bar R) : Prop := {
  extended_supremum_upper : forall x, S x -> (x%:E <= c)%E;
  extended_supremum_least : forall d, (forall x, S x -> (x%:E <= d)%E) -> (c <= d)%E
}.

(** Source for [extended_supremum_unique]: Federer 1.10.5,
    pp. 47-48, supporting uniqueness of each norm supremum.
    Mutual least-upper-bound comparisons imply equality. *)
Theorem extended_supremum_unique (R : realType) (S : set R) c d :
  is_extended_supremum S c -> is_extended_supremum S d -> c=d.
Proof.
move=> hc hd; apply/eqP; rewrite eq_le; apply/andP; split.
- exact (@extended_supremum_least R S c hc d (@extended_supremum_upper R S d hd)).
- exact (@extended_supremum_least R S d hd c (@extended_supremum_upper R S c hc)).
Qed.

(** Source for [extended_supremum_nonnegative]: Federer 1.10.5,
    pp. 47-48, supporting nonnegativity of a norm supremum.
    It is enough that the value set contains one nonnegative element. *)
Lemma extended_supremum_nonnegative (R : realType) (S : set R) c :
  is_extended_supremum S c -> (exists x, S x /\ 0 <= x) -> (0 <= c)%E.
Proof.
move=> hc [x [hx h0]]; apply: le_trans _ (@extended_supremum_upper R S c hc x hx).
by rewrite lee_fin.
Qed.
