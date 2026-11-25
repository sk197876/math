(** Federer (1969), 3.1.11, p. 223: all derivatives
    of the scalar reciprocal, used in the reciprocal composition formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialArithmetic
  NormHigherCurveDerivativeUP ScalarCoefficientLinearAlgebra ScalarPowerDifferential
  ScalarReciprocalDifferential ContinuousMultilinearUP NormHigherDifferentialUP
  NormClassHigherUP ScalarDerivativeSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [scalar_reciprocal_derivative_coefficient]:
    (-1)^j j! / a^(j+1), the derivative of the outer function
    g(y)=1/y in Federer 3.1.11, p. 223. *)
Definition scalar_reciprocal_derivative_coefficient (R : realType) j (a : R) :=
  (-1)^+j*(j`!)%:R*(a^-1)^+j.+1.

(** Source for [scalar_reciprocal_derivative_zero]: the zeroth
    derivative is the original reciprocal, supporting the recursion
    in Federer 3.1.11, pp. 220 and 223. *)
Lemma scalar_reciprocal_derivative_zero (R : realType) (a : R) :
  scalar_reciprocal_derivative_coefficient 0 a=a^-1.
Proof. by rewrite /scalar_reciprocal_derivative_coefficient expr0 fact0 expr1 !mul1r. Qed.

(** Source for [scalar_reciprocal_derivative_step]: each displayed
    reciprocal derivative differentiates to the next one, supporting
    Federer 3.1.11, p. 223. The domain is the nonzero scalars. *)
Lemma scalar_reciprocal_derivative_step (R : realType) j (a : R) :
  a!=0 -> has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    (fun t=>t!=0) (@scalar_reciprocal_derivative_coefficient R j) a
    (@scalar_coefficient_linear_map R R^o (scalar_reciprocal_derivative_coefficient j.+1 a)).
Proof.
move=>ha.
have hN := @scalar_absolute_value_norm R.
have hp := @norm_curve_power_differential R (fun t=>t!=0) (fun t=>t^-1)
  a (-((a^-1)^+2)) j.+1 (scalar_reciprocal_differential ha).
have hs := norm_differential_scale hN hN ((-1)^+j*(j`!)%:R) hp.
rewrite -scalar_coefficient_linear_scale in hs.
have hc : ((-1)^+j*(j`!)%:R)*(j.+1%:R*(a^-1)^+j*(-((a^-1)^+2)))=
    scalar_reciprocal_derivative_coefficient j.+1 a.
  rewrite /scalar_reciprocal_derivative_coefficient factS natrM
    [(-1)^+j.+1]exprS [(a^-1)^+j.+2]exprS [(a^-1)^+j.+1]exprS expr2.
  ring.
change (has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
  (fun t=>t!=0) (@scalar_reciprocal_derivative_coefficient R j) a
  (@scalar_coefficient_linear_map R R^o
    (((-1)^+j*(j`!)%:R)*(j.+1%:R*(a^-1)^+j*(-((a^-1)^+2)))))) in hs.
by rewrite hc in hs.
Qed.

Section ReciprocalHigher.
Variable R : realType.
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R^o}->Hom (Z i) R^o.
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@ev i) (@ZN i).

(** Source for [scalar_reciprocal_class_infinity]: g(y)=1/y
    is smooth on the nonzero scalars, as needed for the
    specialization in Federer 3.1.11, p. 223. *)
Theorem scalar_reciprocal_class_infinity :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    ev ZN (fun t=>t!=0) (fun t=>t^-1).
Proof.
have hF j a (ha : a!=0) : exists L : Hom R^o R^o,
    has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      (fun t=>t!=0) (scalar_reciprocal_derivative_coefficient j) a L /\
    forall t, L t=t*scalar_reciprocal_derivative_coefficient j.+1 a.
  exists (@scalar_coefficient_linear_map R R^o (scalar_reciprocal_derivative_coefficient j.+1 a)).
  split; first exact: scalar_reciprocal_derivative_step.
  by move=>t.
have hc := @scalar_derivative_sequence_class_infinity R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R) Z ev ZN hZ
  (fun t=>t!=0) (@scalar_reciprocal_derivative_coefficient R) hF.
have he : (@scalar_reciprocal_derivative_coefficient R 0)=(fun t=>t^-1).
  apply: funext=>t; exact: scalar_reciprocal_derivative_zero.
by rewrite he in hc.
Qed.

(** Source for [scalar_reciprocal_higher_differentials]: the
    actual jth differential of the reciprocal is the product of
    its scalar arguments times (-1)^j j! a^(-j-1), supporting
    the formula in Federer 3.1.11, p. 223. *)
Theorem scalar_reciprocal_higher_differentials j a : a!=0 ->
  exists z : Z j,
    has_norm_higher_differential (fun t : R^o=>`|t|) ev ZN
      (fun t=>t!=0) (fun t=>t^-1) j a z /\
    forall u, @ev j u z=(\prod_(i<j) u i)*scalar_reciprocal_derivative_coefficient j a.
Proof.
move=>ha.
have hF n b (hb : b!=0) : exists L : Hom R^o R^o,
    has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      (fun t=>t!=0) (scalar_reciprocal_derivative_coefficient n) b L /\
    forall t, L t=t*scalar_reciprocal_derivative_coefficient n.+1 b.
  exists (@scalar_coefficient_linear_map R R^o (scalar_reciprocal_derivative_coefficient n.+1 b)).
  split; first exact: scalar_reciprocal_derivative_step.
  by move=>t.
have [D [hD [hDE _]]] := @scalar_derivative_sequence_differentials R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R) Z ev ZN hZ
  (fun t=>t!=0) (@scalar_reciprocal_derivative_coefficient R) hF.
have he : (@scalar_reciprocal_derivative_coefficient R 0)=(fun t=>t^-1).
  apply: funext=>t; exact: scalar_reciprocal_derivative_zero.
exists (D j a); split.
- rewrite -he; exact: hD j a ha.
- exact: hDE.
Qed.
End ReciprocalHigher.
