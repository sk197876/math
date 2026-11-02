(** Federer (1969), 1.7.4, pp. 30-31: the adjoint equation and coordinate
    projections. Supporting substitution of linear maps into a bilinear
    form; this infrastructure is not a separate claim in the book. editions:
    InnerProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bilinear_linear_precompose]: Federer 1.7.4,
    pp. 30-31, supporting bilinearity of both sides of the adjoint
    equation, used to check it on bases. *)
Lemma bilinear_linear_precompose (R : fieldType)
    (X Y U V W : lmodType R) (B : U -> V -> W) (hB : bilinear B)
    (f : {linear X -> U}) (g : {linear Y -> V}) :
  bilinear (fun x y => B (f x) (g y)).
Proof.
split=> y a x z.
- by rewrite linearP (bilDl hB) (bilZl hB).
- by rewrite linearP (bilDr hB) (bilZr hB).
Qed.
