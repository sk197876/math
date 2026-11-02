(** Federer (1969), 1.10.5, pp. 47-48: existence of the
    suprema defining form and polynomial norms. Source context and
    editions: ExtendedSupremumUP.v. This private witness uses only
    real least-upper-bound completeness and the distinction between a
    bounded and an unbounded nonempty set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal.
From Federer Require Import ExtendedSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [extended_supremum_exists]: Federer 1.10.5,
    pp. 47-48, supporting existence of each displayed supremum.
    A nonempty bounded set has its real supremum; an unbounded set
    has positive infinity as its extended supremum. *)
Theorem extended_supremum_exists (R : realType) (S : set R) :
  S !=set0 -> exists c, is_extended_supremum S c.
Proof.
move=> hn; have [hb|hb] := pselect (has_ubound S).
- exists (sup S)%:E; constructor.
  + move=> x hx; rewrite lee_fin; exact (@ub_le_sup R S hb x hx).
  + move=> [d| |] hu.
    * rewrite lee_fin; apply: ge_sup; first exact hn.
      move=> x hx; have := hu x hx; by rewrite lee_fin.
    * exact: leey.
    * have [x hx] := hn; by have := hu x hx.
- exists (+oo : \bar R)%E; constructor.
  + move=> x hx; exact: leey.
  + move=> [d| |] hu.
    * exfalso; apply: hb; exists d; move=> x hx.
      have := hu x hx; by rewrite lee_fin.
    * exact: lexx.
    * have [x hx] := hn; by have := hu x hx.
Qed.
