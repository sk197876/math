(** Federer (1969), 1.7.1, pp. 27-28: symmetric bilinear forms, polarities,
    and inner products. Definitions are stated independently of coordinates
    or a chosen basis. The local May 1987 erratum has no correction to this
    item. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_symmetric_bilinear]: Federer 1.7.1, p. 27,
    opening paragraph: B is bilinear and B(x,y)=B(y,x). This
    abstract specification makes sense over any field. *)
Definition is_symmetric_bilinear (K : fieldType) (V : lmodType K)
    (B : V -> V -> K) :=
  @bilinear K V V K^o B /\ forall x y, B x y = B y x.

(** Source for [is_inner_product]: Federer 1.7.1, p. 28,
    first paragraph. An inner product is a symmetric bilinear function
    with B(x,x)>0 exactly when x is nonzero. The specification imposes
    no finite-dimensional hypothesis and chooses no construction. *)
Record is_inner_product (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) : Prop := {
  inner_bilinear : @bilinear R V V R^o B;
  inner_symmetric : forall x y, B x y = B y x;
  inner_positive : forall x, (0 < B x x) = (x != 0)
}.
