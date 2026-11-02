(** Federer (1969), 3.1.22, pp. 235–236: the
    differentiability of local representatives depends only on
    their values in a neighbourhood of the base point. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.

(** Source for [norm_differential_enlarge]: supporting the local
    agreements in Federer 3.1.22, p. 236. A derivative
    on an interior subdomain remains a derivative on any
    larger domain of the same total representative. *)
Lemma norm_differential_enlarge (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (A B:X->Prop) (f:X->Y) a (L:Hom X Y) :
  (forall x,A x -> B x) -> has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY B f a L.
Proof.
move=>hAB hf; have [r [hr hA]]:=norm_differential_interior hf.
constructor.
- exists r; split=>// h hh; exact (hAB _ (hA h hh)).
- exact (norm_differential_bounded hf).
- move=>e he; have [d [hd hrem]]:=norm_differential_remainder hf he.
  exists (Num.min r d); split; first by rewrite lt_min hr hd.
  move=>h _; rewrite lt_min=>/andP [hhr hhd].
  exact (hrem h (hA h hhr) hhd).
Qed.
