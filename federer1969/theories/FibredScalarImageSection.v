(** Supporting Federer (1969), 3.2.45, p. 279:
    the exact set identity needed before applying Fubini to row images. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import ProductSections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [fibred_scalar_image_vertical_section]: an expanded
    set-theoretic helper for the continuity argument of Federer
    3.2.45, p. 279. The vertical section of the actual image
    x mapping to (b(x),u(x)) is precisely the image of the original
    b-fibre. No regularity, nonemptiness or selected lift is assumed. *)
Lemma fibred_scalar_image_vertical_section (X Y Z : Type)
    (A : set X) (b : X -> Y) (u : X -> Z) y :
  product_vertical_section ((fun x => (b x,u x)) @` A) y =
    u @` [set x | A x /\ b x=y].
Proof.
apply/seteqP; split=> t.
- move=> [x hx hPair].
  exists x; last by have h := congr1 snd hPair; exact h.
  split=> //; by have h := congr1 fst hPair; exact h.
- move=> [x [hx hB] hU]; exists x=> //.
  by rewrite hB hU.
Qed.
