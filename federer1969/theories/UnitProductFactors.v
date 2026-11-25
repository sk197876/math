(** Federer (1969), 1.10.5, p. 48: supporting scalar product bounds in the
    extremal-tuple proof of the Hilbert norm equality. These elementary
    ordered-field facts are proved locally; they are not separately stated
    assertions of Federer. *)
From mathcomp Require Import all_boot all_order all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [unit_interval_product_upper]: Federer 1.10.5,
    p. 48, supporting fact: a finite product of numbers in
    [0,1] is at most one, including the empty product. *)
Lemma unit_interval_product_upper (R : realFieldType) (T : eqType)
    (a : T -> R) (s : seq T) :
  (forall x, x\in s -> 0<=a x<=1) -> (\prod_(x<-s) a x)<=1.
Proof.
elim: s=> [|x s ih] hb; first by rewrite big_nil.
have /andP[hx0 hx1] := hb x (mem_head _ _).
have ht : forall y, y\in s -> 0<=a y<=1.
  move=> y hy; apply: hb; by rewrite in_cons hy orbT.
have hh := ler_wpM2l hx0 (ih ht).
rewrite big_cons; apply: le_trans _ hx1; by rewrite mulr1 in hh.
Qed.

(** Source for [unit_interval_product_member]: Federer 1.10.5,
    p. 48, supporting fact: a product of numbers in [0,1]
    is at most each factor appearing in it. *)
Lemma unit_interval_product_member (R : realFieldType) (T : eqType)
    (a : T -> R) (s : seq T) :
  (forall x, x\in s -> 0<=a x<=1) -> forall x, x\in s ->
  (\prod_(y<-s) a y)<=a x.
Proof.
move=> hb x hx; rewrite (big_rem x) //=.
have /andP[hx0 hx1] := hb x hx.
have hr : (\prod_(y<-rem x s) a y)<=1.
  apply: unit_interval_product_upper=> y hy; apply: hb; exact: mem_rem hy.
have hh := ler_wpM2l hx0 hr; by rewrite mulr1 in hh.
Qed.

(** Source for [positive_product_maximizer_factors]: Federer
    1.10.5, p. 48, supporting saturation of the unit-ball
    constraints. If a positive maximum M is bounded by M times a
    product of unit-interval factors, every factor equals one. *)
Lemma positive_product_maximizer_factors (R : realFieldType) (T : eqType)
    (a : T -> R) (s : seq T) (M : R) : 0<M ->
  (forall x, x\in s -> 0<=a x<=1) ->
  M<=M*\prod_(y<-s) a y -> forall x, x\in s -> a x= 1.
Proof.
move=> hM hb hm x hx.
have hh := le_trans hm (ler_wpM2l (ltW hM) (unit_interval_product_member hb hx)).
have hx1 := (andP (hb x hx)).2.
rewrite -[X in X<=_]mulr1 (ler_pM2l hM) in hh.
apply/eqP; by rewrite eq_le hx1 hh.
Qed.
