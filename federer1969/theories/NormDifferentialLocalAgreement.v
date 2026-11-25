(** Federer (1969), 3.1.11, p. 219:
    locality of differentiation when the actual domains
    and function values agree on a neighbourhood.
    This supports the recursive higher-differential definition. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_local_agreement]:
    supporting locality law for the recursion in Federer
    3.1.11, p. 219. Neither function is required
    to extend the other globally; domains and values
    agree only in the stated neighbourhood. *)
Lemma norm_differential_local_agreement (R : realType) (X Y : lmodType R)
    (NX : X->R) (NY : Y->R) (hNX : is_real_norm NX)
    (A B : X->Prop) (f g : X->Y) (a : X) (L : Hom X Y) (r : R) :
  0<r ->
  (forall h, NX h<r -> (A (a+h)<->B (a+h))) ->
  (forall h, NX h<r -> A (a+h) -> f (a+h)=g (a+h)) ->
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY B g a L.
Proof.
move=> hr hAB hfg hf.
have ha := norm_domain_interior_member hNX (norm_differential_interior hf).
have hzero : NX 0<r by rewrite (real_seminorm_zero hNX.1).
have hfa : f a=g a.
  have hh := hfg 0 hzero; rewrite addr0 in hh; exact: hh ha.
have [s [hs hAs]] := norm_differential_interior hf.
constructor.
- exists (Num.min r s); split; first by rewrite lt_min hr hs.
  move=> h; rewrite lt_min=> /andP [hhr hhs].
  exact: (hAB h hhr).1 (hAs h hhs).
- exact: norm_differential_bounded hf.
- move=> e he; have [d [hd hrem]] := norm_differential_remainder hf he.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  move=> h hBh; rewrite lt_min=> /andP [hhr hhd].
  have hAh := (hAB h hhr).2 hBh.
  rewrite -(hfg h hhr hAh) -hfa.
  exact: hrem h hAh hhd.
Qed.
