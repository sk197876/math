(** Federer (1969), 3.1.1, p. 209: the gradient is specified by
    L(v)=v.grad f(a). Its existence uses finite dimension or completeness,
    whereas its uniqueness follows from the inner-product laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerProductLaws Bilinear
  HilbertSpaceUP LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_differential_gradient]: Federer 3.1.1, p. 209,
    second special case, characterising equation: applying the differential
    L to v gives the inner product of v with the gradient u. *)
Definition is_differential_gradient (R : realType) (V : lmodType R)
    (B : V -> V -> R) (L : Hom V R^o) (u : V) :=
  forall v, L v = B v u.

(** Source for [differential_gradient_space]: the two alternatives in
    Federer 3.1.1, p. 209: the inner-product space is finite dimensional
    or, more generally, complete. Finite dimension is witnessed by a basis;
    neither alternative is an unproved global axiom. *)
Definition differential_gradient_space (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :=
  (exists n (e : 'I_n -> V), is_basis e) \/ is_hilbert_space hB.

(** Source for [differential_gradient_unique]: the characterisation of
    grad f(a) in Federer 3.1.1, p. 209, uniquely determines its vector.
    This supporting uniqueness argument needs no dimension assumption. *)
Lemma differential_gradient_unique (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (L : Hom V R^o) u w :
  is_differential_gradient B L u -> is_differential_gradient B L w -> u=w.
Proof.
move=> hu hw.
have hz : u-w=0.
  apply: (inner_right_separates hB)=> v.
  by rewrite (bilBr (inner_bilinear hB)) -hu -hw subrr.
apply/eqP; by rewrite -subr_eq0 hz eqxx.
Qed.
