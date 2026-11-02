(** Federer (1969), 3.1.18, pp. 229–230: calculus for the coordinate
    maps, using only the public multilinear representation and the
    class laws already proved in 3.1.11, pp. 220–221. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed NormClassHigherUP
  NormClassHigherRestriction NormClassHigherArithmetic NormClassHigherComposition
  NormClassHigherInverseFunction NormClassHigherLocalValues NormClassInfinityLinear NormHigherDifferentialConstant
  NormRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Operations.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Local Notation P := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ep := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation PN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hP := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).

(** Source for [norm_class_open_restriction]: restriction to an open
    subset, supporting the chart restrictions in 3.1.18, p. 229. *)
Lemma norm_class_open_restriction (A B : X->Prop) (f : X->Y) k :
  (forall x, B x -> A x) ->
  (forall x, B x -> norm_domain_interior NX B x) ->
  norm_class hNX hNY A f k -> norm_class hNX hNY B f k.
Proof. exact (@norm_class_higher_open_restriction R X Y NX NY hNX hNY P ep PN hP A B f k). Qed.

(** Source for [norm_class_add]: sums of class-k maps, supporting the
    target change h in Federer 3.1.18, p. 230; class law from 3.1.11. *)
Lemma norm_class_add (A : X->Prop) (f g : X->Y) k :
  norm_class hNX hNY A f k -> norm_class hNX hNY A g k ->
  norm_class hNX hNY A (fun x=>f x+g x) k.
Proof. exact (@norm_class_higher_add R X Y NX NY hNX hNY P ep PN hP A k f g). Qed.

(** Source for [norm_class_scale]: scalar multiples of class-k maps,
    supporting the signed target changes in 3.1.18, p. 230. *)
Lemma norm_class_scale (A : X->Prop) (f : X->Y) c k :
  norm_class hNX hNY A f k -> norm_class hNX hNY A (fun x=>c*:f x) k.
Proof. exact (@norm_class_higher_scale R X Y NX NY hNX hNY P ep PN hP A k f c). Qed.

(** Source for [norm_class_linear]: a bounded linear map is of every
    class on any open domain; supporting p,q,r,p* in 3.1.18, pp. 229–230,
    by the polynomial assertion in 3.1.11, p. 221. *)
Lemma norm_class_linear (A : X->Prop) (L : Hom X Y) k :
  (forall x, A x -> norm_domain_interior NX A x) ->
  norm_bounded_linear NX NY L -> norm_class hNX hNY A L k.
Proof.
move=>hA hL.
exact (@norm_class_infinity_linear R X Y NX NY hNX hNY P ep PN hP A hA L hL k).
Qed.

(** Source for [norm_class_constant]: constant maps are of every
    class on any open domain, supporting the rank-zero case of 3.1.18,
    p. 229, by 3.1.11, p. 221. *)
Lemma norm_class_constant (A : X->Prop) (c : Y) k :
  (forall x, A x -> norm_domain_interior NX A x) ->
  norm_class hNX hNY A (fun _=>c) k.
Proof.
move=>hA; exact (@norm_class_infinity_constant R X Y NX NY hNX hNY P ep PN hP A hA c k).
Qed.
End Operations.

(** Source for [norm_class_composition]: the composition law of
    3.1.11, p. 220, supporting the coordinate changes in 3.1.18,
    pp. 229–230. The actual domain is A intersect f inverse(B). *)
Lemma norm_class_composition (R : realType) (X Y Z : lmodType R)
    (NX : X->R) (NY : Y->R) (NZ : Z->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNZ : is_real_norm NZ)
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->Z) k :
  norm_class hNX hNY A f k -> norm_class hNY hNZ B g k ->
  norm_class hNX hNZ (fun x=>A x /\ B (f x)) (fun x=>g (f x)) k.
Proof.
exact (@norm_class_higher_composition R X NX hNX k Y Z NY NZ hNY hNZ
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.space R j Y Z NY NZ hNY hNZ)
  (fun j=>@ContinuousMultilinear.space R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j Y Z NY NZ hNY hNZ)
  (fun j=>@ContinuousMultilinear.norm R j Y Z NY NZ hNY hNZ)
  (fun j=>@ContinuousMultilinear.evaluation R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.norm R j X Z NX NZ hNX hNZ)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j Y Z NY NZ hNY hNZ)
  (fun j=>@ContinuousMultilinear.laws R j X Z NX NZ hNX hNZ) A B f g).
Qed.

(** Source for [norm_class_domain_agreement]: total representatives
    equal on the actual domain have the same class, supporting all
    restricted coordinate identities in 3.1.18, pp. 229–230. *)
Lemma norm_class_domain_agreement (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f g:X->Y) k :
  (forall x, A x -> f x=g x) ->
  norm_class hNX hNY A f k -> norm_class hNX hNY A g k.
Proof.
exact (@norm_class_higher_domain_agreement R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY) A f g k).
Qed.

(** Source for [norm_class_inverse_from_first]: the inverse-function
    class upgrade of 3.1.11, p. 220, used for the local diffeomorphism
    in Federer 3.1.18, p. 229. The same inverse has each higher class
    held by the forward map, without an additional completeness premise. *)
Lemma norm_class_inverse_from_first (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->X) k :
  (forall x, A x -> B (f x)) -> (forall y, B y -> A (g y)) ->
  (forall x, A x -> g (f x)=x) -> (forall y, B y -> f (g y)=y) ->
  norm_class hNX hNY A f k -> norm_class hNY hNX B g 1%N ->
  norm_class hNY hNX B g k.
Proof.
move=>hfmap hgmap hgf hfg.
exact (@norm_class_higher_inverse_function R X Y NX NY hNX hNY
  (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.space R j Y X NY NX hNY hNX)
  (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.evaluation R j Y X NY NX hNY hNX)
  (fun j=>@ContinuousMultilinear.norm R j Y X NY NX hNY hNX)
  (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY)
  (fun j=>@ContinuousMultilinear.laws R j Y X NY NX hNY hNX) A B f g hfmap hgmap hgf hfg k).
Qed.

(** Source for [norm_class_compose_on]: composition on a prescribed
    open source domain whose image lies in the second domain; supporting
    all chart composites in Federer 3.1.18, pp. 229–230. *)
Lemma norm_class_compose_on (R:realType) (X Y Z:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) (g:Y->Z) k :
  (forall x, A x -> B (f x)) ->
  norm_class hNX hNY A f k -> norm_class hNY hNZ B g k ->
  norm_class hNX hNZ A (fun x=>g (f x)) k.
Proof.
move=>hAB hf hg.
have hc := norm_class_composition hf hg.
apply: (@norm_class_open_restriction R X Z NX NZ hNX hNZ
  (fun x=>A x /\ B (f x)) A (fun x=>g (f x)) k _ _ hc).
- by move=>x hx; split=>//; exact: hAB.
- move=>x hx; exact ((@norm_class_continuous R X Y NX NY hNX hNY A f k hf x hx).1).
Qed.

(** Source for [norm_class_subtract]: differences of maps preserve
    class k, supporting h and its inverse in 3.1.18, p. 230. *)
Lemma norm_class_subtract (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (f g:X->Y) k :
  norm_class hNX hNY A f k -> norm_class hNX hNY A g k ->
  norm_class hNX hNY A (fun x=>f x-g x) k.
Proof.
move=>hf hg.
have hn := norm_class_scale (-1) hg.
have hs := norm_class_add hf hn.
apply: (norm_class_domain_agreement _ hs)=>x hx.
by rewrite scaleN1r.
Qed.
