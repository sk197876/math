(** Federer (1969), 1.7.13, p. 37: existence of the distance from a point to
    a nonempty set. The construction uses only completeness of the real
    scalar order, not a Hilbert-space theorem. It is hidden behind the
    distance specification. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import InnerProductUP InnerNorm InnerSetDistanceUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_set_distance_exists]: Federer 1.7.13,
    p. 37, supporting existence of the defining infimum:
    the nonempty set of distances has lower bound zero. *)
Theorem inner_set_distance_exists (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (a : V) (C : set V) :
  C !=set0 -> exists d, is_inner_set_distance hB a C d.
Proof.
move=> [x0 hx0].
pose D := (fun x => inner_norm hB (a-x)) @` C.
have hn : D !=set0 by exists (inner_norm hB (a-x0)); exists x0.
have hl : lbound D 0.
  move=> t [x hx <-]; exact: inner_norm_nonnegative.
have hb : has_lbound D by exists 0.
have hi : has_inf D by split.
exists (inf D); constructor.
- exact: lb_le_inf hn hl.
- move=> x hx; apply: (ge_inf hb); by exists x.
- move=> eps heps.
  have [t [x hx hxt] ht] := inf_adherent heps hi.
  exists x; split=> //; by rewrite hxt.
Qed.
