(** Federer (1969), 3.3.19, p. 303: independent
    specification of the finite weighted cell-hit measure.
    The defining value is the original hit count times
    the original nonnegative weight; measure laws are proved
    separately and are not fields of this specification. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_cell_hit_indices]: the actual
    original finite cells meeting a test set, as in
    the definition of psi_n in 3.3.19, p. 303.
    The intersection must be nonempty. *)
Definition finite_cell_hit_indices (I X:choiceType) (F:{fset I})
    (S:I->set X) (T:set X):{fset I}:=
  [fset i in F | `[< S i `&` T!=set0 >]].

(** Source for [is_finite_cell_hit_measure]: literal
    weighted hit-count value in 3.3.19, p. 303,
    specified before any existence proof. This predicate
    does not assume additivity or measurability of cells. *)
Definition is_finite_cell_hit_measure (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu:set X->\bar R):Prop:=
  forall T,mu T=(#|` finite_cell_hit_indices F S T|%:R*w)%:E.

(** Source for [finite_cell_hit_measure_unique]: uniqueness
    of the measure specified by the original finite
    hit-count values, supporting 3.3.19, p. 303. *)
Lemma finite_cell_hit_measure_unique (R:realType) (I X:choiceType)
    (F:{fset I}) (S:I->set X) (w:R) (mu nu:set X->\bar R):
  is_finite_cell_hit_measure F S w mu ->is_finite_cell_hit_measure F S w nu ->mu=nu.
Proof. move=>hm hn;apply/funext=>T;by rewrite hm hn. Qed.
