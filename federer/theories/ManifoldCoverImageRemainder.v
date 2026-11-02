(** Federer (1969), 3.2.29, p. 268:
    the uncovered image lies in the union of the
    small disagreement image and the critical image.
    The printed equality is used only through this
    valid containment; no image-disjointness is assumed. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [agreement_image_cover_remainder]: the
    first display after the local submanifold family
    in Federer 3.2.29, p. 268. The proof
    needs containment, which remains valid when the
    two error images overlap the covering image.
    This does not assert the printed equality. *)
Lemma agreement_image_cover_remainder (X Y:Type) (F f:X->Y)
    (S C P:set X):
  (forall x,C x ->f x=F x) ->
  (F @` S) `\` (f @` P) `<=` (F @` (S `\` C)) `|` (f @` (C `\` P)).
Proof.
move=>hAgree y [[x hx hFy] hn].
case:(pselect (C x))=>hC.
- right; exists x; last by rewrite (hAgree x hC).
  split; first exact hC.
  move=>hP; apply:hn; exists x; first exact hP.
  by rewrite (hAgree x hC).
- left; exists x; last exact hFy; by split.
Qed.
