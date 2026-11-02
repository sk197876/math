(** Federer (1969), 3.1.11, pp. 220–222:
    arithmetic of real-source differentials, expressed
    by their vector coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormHigherCurveDerivativeUP NormDifferentialScalarProduct
  NormDifferentialChain NormDifferentialLocal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_coefficient_linear_add]:
    addition of real-source differential coefficients
    in Federer 3.1.11, p. 220. *)
Lemma scalar_coefficient_linear_add (R : realType) (Y : lmodType R)
    (u v : Y) :
  scalar_coefficient_linear_map (u+v)=
    scalar_coefficient_linear_map u+scalar_coefficient_linear_map v.
Proof. apply: hom_ext=>t; exact: scalerDr. Qed.

(** Source for [scalar_coefficient_linear_scale]:
    scalar multiplication of real-source differential
    coefficients in Federer 3.1.11, p. 220. *)
Lemma scalar_coefficient_linear_scale (R : realType) (Y : lmodType R)
    (c : R) (v : Y) :
  scalar_coefficient_linear_map (c*:v)=c*:scalar_coefficient_linear_map v.
Proof.
apply: hom_ext=>t; change (t*:(c*:v)=c*:(t*:v)).
by rewrite !scalerA mulrC.
Qed.

(** Source for [scalar_coefficient_linear_zero]:
    the zero real-source differential coefficient,
    supporting Federer 3.1.11, p. 220. *)
Lemma scalar_coefficient_linear_zero (R : realType) (Y : lmodType R) :
  scalar_coefficient_linear_map (0 : Y)= 0.
Proof. apply: hom_ext=>t; exact: scaler0. Qed.

(** Source for [scalar_vector_product_coefficient]:
    the real-source product derivative coefficient
    is f' g+f g', the first Leibniz
    rule used in Federer 3.1.11, pp. 220–222. *)
Lemma scalar_vector_product_coefficient (R : realType) (Y : lmodType R)
    (c l : R) (w m : Y) :
  scalar_vector_product_linear_term c w
    (@scalar_coefficient_linear_map R R^o l) (scalar_coefficient_linear_map m)=
  scalar_coefficient_linear_map (l*:w+c*:m).
Proof.
apply: hom_ext=>t.
change ((t* l)*:w+c*:(t*:m)=t*:(l*:w+c*:m)).
by rewrite scalerDr !scalerA [c*t]mulrC.
Qed.

(** Source for [norm_curve_scalar_product]:
    the first Leibniz rule for a scalar function
    times a normed-vector curve, supporting the
    Taylor calculation in Federer 3.1.11,
    pp. 220–221. *)
Theorem norm_curve_scalar_product (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A : R->Prop) (f : R->R) (g : R->Y) a l m :
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A f a (@scalar_coefficient_linear_map R R^o l) ->
  has_norm_differential (fun t : R^o=>`|t|) NY A g a
    (scalar_coefficient_linear_map m) ->
  has_norm_differential (fun t : R^o=>`|t|) NY A (fun x=>f x*:g x) a
    (scalar_coefficient_linear_map (l*:g a+f a*:m)).
Proof.
move=> hf hg.
have h := norm_differential_scalar_product (@scalar_absolute_value_norm R) hNY hf hg.
by rewrite scalar_vector_product_coefficient in h.
Qed.


(** Source for [scalar_coefficient_linear_compose]:
    the real-source chain-rule coefficient is the
    product of the two first derivative coefficients,
    supporting Federer 3.1.11, pp. 220–223. *)
Lemma scalar_coefficient_linear_compose (R : realType) (Y : lmodType R)
    (l : R) (m : Y) :
  hom_comp (scalar_coefficient_linear_map m) (@scalar_coefficient_linear_map R R^o l)=
    scalar_coefficient_linear_map (l*:m).
Proof.
apply: hom_ext=>t; change ((t* l)*:m=t*:(l*:m)).
exact: esym (scalerA _ _ _).
Qed.

(** Source for [norm_curve_chain_on_domain]:
    the first chain rule of 3.1.1(2), p. 210,
    in the real-source coefficient notation used
    in Federer 3.1.11, pp. 220–223.
    The function-domain inclusion is explicit. *)
Lemma norm_curve_chain_on_domain (R : realType) (Y : lmodType R)
    (NY : Y->R) (hNY : is_real_norm NY)
    (A B : R->Prop) (f : R->R) (g : R->Y) a l m :
  (forall x, A x -> B (f x)) ->
  has_norm_differential (fun t : R^o=>`|t|)
    (fun t : R^o=>`|t|) A f a (@scalar_coefficient_linear_map R R^o l) ->
  has_norm_differential (fun t : R^o=>`|t|) NY B g (f a)
    (scalar_coefficient_linear_map m) ->
  has_norm_differential (fun t : R^o=>`|t|) NY A (fun x=>g (f x)) a
    (scalar_coefficient_linear_map (l*:m)).
Proof.
move=> hAB hf hg.
have hc := norm_differential_chain (@scalar_absolute_value_norm R)
  (@scalar_absolute_value_norm R) hNY hf hg.
rewrite scalar_coefficient_linear_compose in hc.
apply: norm_differential_restrict _ (norm_differential_interior hf) hc.
by move=> x hx; split=> //; exact: hAB x hx.
Qed.
