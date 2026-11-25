(** Federer (1969), 3.1.11, p. 223:
    the printed zero-extended exponential is of
    class infinity and has all derivatives
    zero on the nonpositive half-line.
    Only the sealed function laws are used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarSmoothSequenceUP Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormClassHigherUP NormHigherCurveDerivativeUP
  ScalarDerivativeSequence FlatExponentialUP FlatExponentialSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FlatSmoothness.
Variable R : realType.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->R^o}->Hom (Z k) R^o.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@evaluation k) (@ZN k).

(** Source for [flat_exponential_class_infinity]:
    the class-infinity assertion for the first
    displayed function on Federer 3.1.11,
    p. 223. All orders use the
    exact recursive differential graphs. *)
Theorem flat_exponential_class_infinity :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    evaluation ZN (fun _=>True) (@FlatExponential.value R).
Proof.
have [F [[hF0 hF] hz]] := @FlatExponential.smooth_derivatives R.
have he : F 0%N=@FlatExponential.value R := funext hF0.
rewrite -he; apply: (@scalar_derivative_sequence_class_infinity R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R) Z evaluation ZN hZ
  (fun _=>True) F).
move=> k a _; exists (@scalar_coefficient_linear_map R R^o (F k.+1 a)).
split; first exact: hF.
by move=>t.
Qed.

(** Source for [flat_exponential_higher_differential_zero]:
    every derivative of the extended function
    vanishes at zero and on the negative
    half-line, supporting the smooth cutoff
    in Federer 3.1.11, p. 223. *)
Theorem flat_exponential_higher_differential_zero k a :
  a<= 0 ->
  has_norm_higher_differential (fun t : R^o=>`|t|) evaluation ZN
    (fun _=>True) (@FlatExponential.value R) k a (0 : Z k).
Proof.
move=> ha.
have [F [[hF0 hF] hz]] := @FlatExponential.smooth_derivatives R.
have hseq n b (_ : True) : exists L : Hom R^o R^o,
    has_norm_differential (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      (fun _=>True) (F n) b L /\ forall t, L t=t*F n.+1 b.
  exists (@scalar_coefficient_linear_map R R^o (F n.+1 b)); split; first exact: hF.
  by move=>t.
have [D [hD [hDe hc]]] := @scalar_derivative_sequence_differentials R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R)
  Z evaluation ZN hZ (fun _=>True) F hseq.
have hzero : D k a= 0.
  apply: (continuous_multilinear_extensional (@hZ k))=>u.
  by rewrite hDe (hz k a ha) scaler0 linear0.
have hh := hD k a I.
have he : F 0%N=@FlatExponential.value R := funext hF0.
by rewrite he hzero in hh.
Qed.
End FlatSmoothness.
