(** Federer (1969), 1.7.11, p. 36: supporting inclusions and
    projections for the Cartesian product in the difference-map proof.
    These elementary linear maps express the two factors without
    inspecting any inner-product construction. Source context:
    ProductInnerUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Maps.
Variable R : fieldType.
Variables V W : lmodType R.
Local Notation P := (GRing.Lmodule.clone R (V * W)%type _).

(** Source for [product_left]: Federer 1.7.11, p. 36,
    supporting inclusion x maps to (x,0), used in the displayed basis. *)
Definition product_left (x : V) : P := (x,0).
(** Source for [product_left_linear]: Federer 1.7.11,
    p. 36, linearity of the first factor inclusion. *)
Lemma product_left_linear : linear product_left.
Proof.
move=> a x y.
change ((a *: x + y, (0 : W)) = (a *: x + y, a *: (0 : W) + 0)).
by rewrite scaler0 addr0.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R V P *:%R product_left product_left_linear.

(** Source for [product_right]: Federer 1.7.11, p. 36,
    supporting inclusion y maps to (0,y), used in the displayed basis. *)
Definition product_right (y : W) : P := (0,y).
(** Source for [product_right_linear]: Federer 1.7.11,
    p. 36, linearity of the second factor inclusion. *)
Lemma product_right_linear : linear product_right.
Proof.
move=> a x y.
change (((0 : V), a *: x + y) = (a *: (0 : V) + 0, a *: x + y)).
by rewrite scaler0 addr0.
Qed.
HB.instance Definition _ := GRing.isLinear.Build R W P *:%R product_right product_right_linear.

(** Source for [product_first]: Federer 1.7.11, p. 36,
    supporting first-coordinate projection on the Cartesian product. *)
Definition product_first (x : P) : V := x.1.
(** Source for [product_first_linear]: Federer 1.7.11,
    p. 36, linearity of the first-coordinate projection. *)
Lemma product_first_linear : linear product_first.
Proof. by move=> a x y. Qed.
HB.instance Definition _ := GRing.isLinear.Build R P V *:%R product_first product_first_linear.

(** Source for [product_second]: Federer 1.7.11, p. 36,
    supporting second-coordinate projection on the Cartesian product. *)
Definition product_second (x : P) : W := x.2.
(** Source for [product_second_linear]: Federer 1.7.11,
    p. 36, linearity of the second-coordinate projection. *)
Lemma product_second_linear : linear product_second.
Proof. by move=> a x y. Qed.
HB.instance Definition _ := GRing.isLinear.Build R P W *:%R product_second product_second_linear.
End Maps.
