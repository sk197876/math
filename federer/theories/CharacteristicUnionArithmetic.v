(** Federer (1969), 2.6.4, pp. 118–119: supporting characteristic-function
    identities in the finite-union step of the density proof. These follow
    from the two pointwise laws in 2.2.14, p. 70. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import CharacteristicFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [characteristic_rectangle_product]: the pure
    rectangle characteristic used in the P0 density step of
    Federer 2.6.4, p. 118. *)
Lemma characteristic_rectangle_product (R : realType) (X Y : Type)
    (A : set X) (B : set Y) (f : X -> R) (g : Y -> R) :
  is_characteristic_function A f -> is_characteristic_function B g ->
  is_characteristic_function (A `*` B) (fun p : X*Y => f p.1*g p.2).
Proof.
move=> hf hg; constructor.
- move=> [x y] [hx hy] /=; by rewrite (characteristic_on_set hf hx) (characteristic_on_set hg hy) mulr1.
- move=> [x y] hn /=; case: (pselect (A x))=> hx.
  + have hy : ~ B y by move=> hy; apply: hn; by split.
    by rewrite (characteristic_off_set hg hy) mulr0.
  + by rewrite (characteristic_off_set hf hx) mul0r.
Qed.

(** Source for [characteristic_union_difference]: supporting
    inclusion-exclusion identity for the P1 finite-union step
    in Federer 2.6.4, pp. 118–119. *)
Lemma characteristic_union_difference (R : realType) (X : Type)
    (A B : set X) (a b c : X -> R) :
  is_characteristic_function A a -> is_characteristic_function B b ->
  is_characteristic_function (A `&` B) c ->
  is_characteristic_function (A `|` B) (fun x => a x+b x-c x).
Proof.
move=> ha hb hc; constructor.
- move=> x hx; case: (pselect (A x))=> hA; case: (pselect (B x))=> hB.
  + have hC : (A `&` B) x by split.
    by rewrite (characteristic_on_set ha hA) (characteristic_on_set hb hB) (characteristic_on_set hc hC) addrK.
  + have hC : ~ (A `&` B) x by move=> [_ h]; exact: hB h.
    by rewrite (characteristic_on_set ha hA) (characteristic_off_set hb hB) (characteristic_off_set hc hC) addr0 subr0.
  + have hC : ~ (A `&` B) x by move=> [h _]; exact: hA h.
    by rewrite (characteristic_off_set ha hA) (characteristic_on_set hb hB) (characteristic_off_set hc hC) add0r subr0.
  + case: hx=> h; [by case: (hA h)|by case: (hB h)].
- move=> x hx.
  have hA : ~ A x by move=> h; apply: hx; left.
  have hB : ~ B x by move=> h; apply: hx; right.
  have hC : ~ (A `&` B) x by move=> [h _]; exact: hA h.
  by rewrite (characteristic_off_set ha hA) (characteristic_off_set hb hB) (characteristic_off_set hc hC) add0r subr0.
Qed.

(** Source for [characteristic_absolute_difference]: supporting
    L1 error identification by symmetric difference in the density
    proof of Federer 2.6.4, pp. 118–119. The set
    is written explicitly as (A minus B) union (B minus A). *)
Lemma characteristic_absolute_difference (R : realType) (X : Type)
    (A B : set X) (a b : X -> R) :
  is_characteristic_function A a -> is_characteristic_function B b ->
  is_characteristic_function ((A `\` B) `|` (B `\` A)) (fun x => `|a x-b x|).
Proof.
move=> ha hb; constructor.
- move=> x [[hA hB]|[hB hA]].
  + by rewrite (characteristic_on_set ha hA) (characteristic_off_set hb hB) subr0 normr1.
  + by rewrite (characteristic_off_set ha hA) (characteristic_on_set hb hB) sub0r normrN normr1.
- move=> x hn; case: (pselect (A x))=> hA.
  + have hB : B x by apply: contrapT=> hB; apply: hn; left; by split.
    by rewrite (characteristic_on_set ha hA) (characteristic_on_set hb hB) subrr normr0.
  + have hB : ~ B x by move=> hB; apply: hn; right; by split.
    by rewrite (characteristic_off_set ha hA) (characteristic_off_set hb hB) subrr normr0.
Qed.
