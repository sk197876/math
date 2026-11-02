(** Federer (1969), 3.1.1, p. 210: subtracting the identity in
    the inverse-function proof. The supporting subtraction rule holds
    for arbitrary differentiable maps with a common domain. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialArithmetic NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_subtract]: the calculation
    D(f-identity)=Df-identity in Federer 3.1.1, p. 210, in its general
    subtraction form. It follows from the proved sum and scalar rules. *)
Lemma norm_differential_subtract (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (A : X -> Prop) (f g : X -> Y)
    (a : X) (L M : Hom X Y) :
  has_norm_differential NX NY A f a L ->
  has_norm_differential NX NY A g a M ->
  has_norm_differential NX NY A (fun x => f x-g x) a (L-M).
Proof.
move=> hf hg.
have hn := @norm_differential_scale R X Y NX NY hNX hNY A g a M (-1) hg.
have hs := norm_differential_add hNY hf hn.
have heq : L+(-1)*:M = L-M by rewrite scaleN1r.
rewrite heq in hs.
apply: (@norm_differential_domain_agreement R X Y NX NY hNX A
  (fun x => f x+(-1)*:g x) (fun x => f x-g x) a (L-M) _ hs)=> x _.
by rewrite scaleN1r.
Qed.
