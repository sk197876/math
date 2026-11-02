(** Federer (1969), 3.1.13, p. 225:
    nonnegative smooth bumps covering by their
    unit plateaus give a smooth partition of
    unity after division by their locally finite sum. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP NormClassHigherUP
  FiniteFamilySumUP NormLocallyFiniteFamilyUP NormClassHigherLocallyFiniteSum
  FinitePositiveFamilyNormalization NormClassHigherScalarQuotient NormPartitionUnityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_locally_finite_quotient_family]:
    normalizing a bump family cannot enlarge
    the locally active index sets, supporting
    Federer 3.1.13, p. 225. *)
Lemma norm_locally_finite_quotient_family (R : realType)
    (X : lmodType R) (J : choiceType) (NX : X->R)
    (U : X->Prop) (I : J->Prop) (f : J->X->R) (g : X->R) :
  is_norm_locally_finite_function_family NX U I f ->
  is_norm_locally_finite_function_family NX U I (fun j x=>f j x/g x).
Proof.
move=>hlocal a ha; have [O [hOa [hOU [hOo [F [hFI hF]]]]]] := hlocal a ha.
exists O; split; first exact hOa; split; first exact hOU; split; first exact hOo.
exists F; split; first exact hFI.
by move=>x hx j hj hn; rewrite (hF x hx j hj hn) mul0r.
Qed.

(** Source for [norm_partition_from_positive_bumps]:
    v_s=u_s/u is a smooth partition
    of unity on U, Federer 3.1.13,
    p. 225. Smoothness, positivity
    of the denominator, and sum one
    are conclusions derived from the bump laws. *)
Theorem norm_partition_from_positive_bumps (R : realType)
    (X : lmodType R) (J : choiceType) (NX : X->R)
    (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX
      (fun t : R^o=>`|t|) (@ev i) (@ZN i))
    (U : X->Prop) (I : J->Prop) (f : J->X->R) (g : X->R) :
  is_norm_locally_finite_function_family NX U I f ->
  is_finite_family_sum_on U I f g ->
  (forall j, I j -> forall x, U x -> 0<=f j x) ->
  (forall x, U x -> exists j, I j /\ f j x= 1) ->
  (forall j, I j -> norm_class_infinity NX (fun t : R^o=>`|t|) ev ZN U (f j)) ->
  is_norm_smooth_partition_of_unity NX ev ZN U I (fun j x=>f j x/g x).
Proof.
move=>hlocal hsum hnonneg hplateau hf.
have hfin := norm_locally_finite_active_family hlocal.
have hg := norm_class_infinity_locally_finite_sum hNX
  (@scalar_absolute_value_norm R) hZ hlocal hsum hf.
have hgne x (hx : U x) : g x!=0.
  have hl := finite_nonnegative_family_sum_plateau_bound
    hfin hsum hnonneg hx (hplateau x hx).
  exact: (lt0r_neq0 (lt_le_trans ltr01 hl)).
constructor.
- move=>j hj x hx; exact: (finite_normalized_family_range hfin hsum hnonneg hplateau hj hx).
- move=>j hj k.
  exact: (norm_class_higher_scalar_quotient hNX hZ hgne (hf j hj k) (hg k)).
- exact: (norm_locally_finite_quotient_family g hlocal).
- exact: (finite_normalized_family_sum_one hfin hsum hnonneg hplateau).
Qed.
