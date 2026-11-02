(** Federer (1969), 3.1.11, p. 223: the general
    reciprocal formula as a specialization of the composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormHigherCurveDerivativeUP
  SymmetricForms ContinuousMultilinearUP ContinuousMultilinearSealed
  NormHigherSymmetricFormUP NormClassHigherUP NormClassHigherComposition
  NormHigherCompositionFormula ScalarReciprocalHigherDifferentials
  ScalarReciprocalForms ReciprocalFormCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_reciprocal_formula]: the displayed
    formula for D^p(1/f)(a), Federer 3.1.11, p. 223.
    It uses the original derivatives of f, and the reciprocal's
    domain is exactly the nonzero part of the original domain.
    The conclusion includes class k on that open domain. *)
Theorem norm_higher_reciprocal_formula (R : realType)
    (X : lmodType R) (NX : X->R) (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (A : X->Prop) (f : X->R^o) k a (phi : forall i, S_m X R^o i) :
  (1<=k)%N -> A a -> f a!=0 ->
  norm_class_higher NX (fun t : R^o=>`|t|) ev ZN A f k ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A f i a (phi i)) ->
  norm_class_higher NX (fun t : R^o=>`|t|) ev ZN
    (fun x=>A x /\ f x!=0) (fun x=>(f x)^-1) k /\
  forall p, (1<=p<=k)%N -> forall eta : S_m X R^o p,
    is_norm_higher_differential_form NX ev ZN
      (fun x=>A x /\ f x!=0) (fun x=>(f x)^-1) p a eta ->
    eta=reciprocal_differential_form_coefficient k phi (f a) p.
Proof.
move=>hk ha hfa hf hphi.
pose N := fun t : R^o=>`|t|.
have hN : is_real_norm N := @scalar_absolute_value_norm R.
pose W j := @ContinuousMultilinear.space R j R^o R^o N N hN hN.
pose ew j := @ContinuousMultilinear.evaluation R j R^o R^o N N hN hN.
pose WN j := @ContinuousMultilinear.norm R j R^o R^o N N hN hN.
have hW j : is_continuous_multilinear_space N N (ew j) (WN j).
  exact: ContinuousMultilinear.laws.
have hg := scalar_reciprocal_class_infinity hW k.
have hpsi j (_ : (j<=k)%N) : is_norm_higher_differential_form N ew WN
    (fun t=>t!=0) (fun t=>t^-1) j (f a) (scalar_reciprocal_form (f a) j).
  exact (@scalar_reciprocal_form_actual R W ew WN hW (f a) j hfa).
split.
- exact (@norm_class_higher_composition R X NX hNX k R^o R^o N N hN hN
    Z W Z ev ZN ew WN ev ZN hZ hW hZ A (fun t=>t!=0) f (fun t=>t^-1) hf hg).
- move=>p hp eta heta.
  have hh := @norm_higher_composition_formula R X R^o R^o NX N N hNX hN hN
    Z W Z ev ZN ew WN ev ZN hZ hW hZ A (fun t=>t!=0) f (fun t=>t^-1)
    k a phi (scalar_reciprocal_form (f a)) hk ha hfa hf hg hphi hpsi p hp eta heta.
  by rewrite reciprocal_composition_form_coefficient in hh.
Qed.
