(** Federer (1969), 1.7.3, p. 29: supporting sign change in a
    two-dimensional invariant block, used to make its alternating-form
    coefficient nonnegative. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Negation.
Variable R : fieldType.
Variables U V W : lmodType R.
Variable B : U -> V -> W.
Hypothesis hB : bilinear B.

(** Source for [bilNl]: Federer 1.7.3, p. 29, supporting
    bilinear identity for negating the first coordinate. *)
Lemma bilNl x y : B (-x) y = -B x y.
Proof. by rewrite -[(-x)]sub0r (bilBl hB) (bil0l hB) sub0r. Qed.

(** Source for [bilNr]: Federer 1.7.3, p. 29, supporting
    bilinear identity for negating the second coordinate. *)
Lemma bilNr x y : B x (-y) = -B x y.
Proof. by rewrite -[(-y)]sub0r (bilBr hB) (bil0r hB) sub0r. Qed.
End Negation.
