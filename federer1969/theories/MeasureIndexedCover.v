(** Federer (1969), 2.1.2, p. 53: indexed countable coverings, derived from
    the printed family formulation. editions: MeasureUP.v. No external
    measure theory is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumImageBound MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measure_indexed_cover]: Federer 2.1.2,
    p. 53; supporting countable indexed form of the covering law,
    allowing repetition of a set in the family. *)
Lemma measure_indexed_cover (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu)
    (A : set I) (D : set J) (F : J -> set I) :
  countable D -> A `<=` \bigcup_(j in D) F j ->
  mu A <= nonnegative_sum D (fun j => mu (F j)).
Proof.
move=> hD hc.
have hF : countable (F @` D) := sub_countable (card_image_le F D) hD.
have hcover : A `<=` \bigcup_(B in F @` D) B.
  move=> x hx; have [j hj hxj] := hc x hx; exists (F j); last exact hxj.
  by exists j.
apply: le_trans (@measure_countable_cover R I mu hm A (F @` D) hF hcover) _.
apply: nonnegative_sum_image_bound=> j _; exact: (@measure_nonnegative R I mu hm (F j)).
Qed.
