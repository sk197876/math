(** Supporting rectangular restriction in Federer (1969), 2.6.3(2), p. 118,
    with the subset-integral convention of 2.4.10, p. 85. The graph
    identities hold for arbitrary partial functions and a specified zero,
    preserving exact domains. *)
From mathcomp Require Import all_boot classical_sets.
From Federer Require Import PartialFunctionUP PartialProductSections PartialZeroExtension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectangle_restriction_horizontal_on]: supporting
    section of f restricted to A times B in Federer
    2.6.3(2), p. 118: when y belongs to B,
    its horizontal section is the original section restricted
    to A. Undefined original values remain undefined. *)
Lemma rectangle_restriction_horizontal_on (X Y Z : Type) (zero : Z)
    (A : set X) (B : set Y) (f : partial_function (X*Y) Z) (y : Y) :
  B y -> forall x z,
    partial_function_graph (partial_product_horizontal_section
      (partial_function_zero_extension zero (A `*` B) f) y) x z <->
    partial_function_graph (partial_function_zero_extension zero A
      (partial_product_horizontal_section f y)) x z.
Proof.
move=> hy x z.
change (partial_function_graph (partial_function_zero_extension zero (A `*` B) f) (x,y) z <->
  partial_function_graph (partial_function_zero_extension zero A (partial_product_horizontal_section f y)) x z).
rewrite !partial_function_zero_extension_graph /=; split.
- move=> [[[hx _] hf]|[hn hz]].
  + left; by split.
  + right; split=> // hx; apply: hn; by split.
- move=> [[hx hf]|[hn hz]].
  + left; split=> //; by split.
  + right; split=> //; by move=> [hx _]; apply: hn.
Qed.

(** Source for [rectangle_restriction_horizontal_off]: supporting
    zero section off B in the rectangular integral of
    Federer 2.6.3(2), p. 118. The zero extension
    is total there, independently of the original domain. *)
Lemma rectangle_restriction_horizontal_off (X Y Z : Type) (zero : Z)
    (A : set X) (B : set Y) (f : partial_function (X*Y) Z) (y : Y) :
  ~ B y -> forall x z,
    partial_function_graph (partial_product_horizontal_section
      (partial_function_zero_extension zero (A `*` B) f) y) x z <-> z=zero.
Proof.
move=> hy x z; apply: partial_function_zero_extension_off.
by move=> [_ hB]; exact: hy hB.
Qed.
