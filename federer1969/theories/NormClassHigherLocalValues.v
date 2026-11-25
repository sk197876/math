(** Federer (1969), 3.1.11, pp. 219–220:
    higher differentiability classes depend only on
    the function's values on its open domain.
    Empty domains satisfy the class conditions vacuously. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormClassOneUP ContinuousMultilinearUP
  NormHigherDifferentialLocal NormClassHigherUP NormClassHigherDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [norm_class_higher_domain_agreement]:
    changing a total representative off its
    domain preserves class k, supporting the
    exact-domain conventions of Federer 3.1.11,
    pp. 219–220. *)
Theorem norm_class_higher_domain_agreement (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (hZ : forall k, is_continuous_multilinear_space NX NY (@ez k) (@ZN k))
    (A : X->Prop) (f g : X->Y) k :
  (forall x, A x -> f x=g x) ->
  norm_class_higher NX NY ez ZN A f k ->
  norm_class_higher NX NY ez ZN A g k.
Proof.
move=> hfg [hf [D [hD hcD]]].
have hopen a (ha : A a) := (hf a ha).1.
split; first exact: norm_class_zero_domain_agreement hfg hf.
exists D; split; last exact hcD.
move=> a ha.
have hh := @norm_higher_differential_local_agreement R X Y NX NY hNX hNY
  Z ez ZN hZ k A A A f g hopen
  (fun x _=>iff_refl (A x)) (fun x _ hx=>hfg x hx) a ha (D a).
exact: hh.1 (hD a ha).
Qed.

(** Source for [norm_class_higher_empty_domain]:
    the class-k conditions on an empty
    open domain, supporting the boundary cases
    of the inverse assertion in Federer 3.1.11,
    p. 220. No point or derivative
    is invented outside that domain. *)
Lemma norm_class_higher_empty_domain (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (Z : nat->lmodType R)
    (ez : forall k, {ffun 'I_k->X}->Hom (Z k) Y)
    (ZN : forall k, Z k->R)
    (A : X->Prop) (f : X->Y) k :
  (forall x, ~A x) -> norm_class_higher NX NY ez ZN A f k.
Proof.
move=> hA; split.
- move=> a ha; exfalso; exact: hA a ha.
- exists (fun _ : X=>(0 : Z k)); split; move=> a ha; exfalso; exact: hA a ha.
Qed.
