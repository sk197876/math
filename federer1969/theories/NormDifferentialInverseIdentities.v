(** Federer (1969), 3.1.1(1), p. 209, used in
    3.1.11, p. 220: differentials of mutually
    inverse differentiable maps are inverse operators. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  NormDifferentialLinear NormDifferentialLocal NormDifferentialChain
  NormDifferentialDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differentials_left_inverse]:
    the inverse differential identity in Federer
    3.1.1(1), p. 209. Applying the chain
    rule to a left inverse gives the
    identity operator by uniqueness. Completeness
    and finite dimension are not assumed. *)
Theorem norm_differentials_left_inverse (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->X)
    (a : X) (L : Hom X Y) (M : Hom Y X) :
  (forall x, A x -> B (f x)) ->
  (forall x, A x -> g (f x)=x) ->
  has_norm_differential NX NY A f a L ->
  has_norm_differential NY NX B g (f a) M ->
  hom_comp M L=hom_of_linear (linear_id X).
Proof.
move=> hAB hgf hf hg.
have hchain := norm_differential_chain hNX hNY hNX hf hg.
have hsub x (hx : A x) : A x /\ B (f x) := conj hx (hAB x hx).
have hd := norm_differential_restrict hsub (norm_differential_interior hf) hchain.
have hid := norm_differential_domain_agreement hNX hgf hd.
have hbound : norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
  exists 1; split; first exact: ler01.
  by move=> v; rewrite hom_of_linearE /= mul1r.
have hlin := norm_differential_linear hNX hNX (norm_differential_interior hf) hbound.
exact (norm_differential_unique hNX hNX hid hlin).
Qed.
