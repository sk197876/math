(** Federer (1969), 3.1.11, p. 223:
    the sealed printed cutoff has actual
    higher differentials of every order.
    The private derivative expressions and
    polynomial witnesses are not imported. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormHigherCurveDerivativeUP
  ContinuousMultilinearUP NormHigherDifferentialUP NormClassHigherUP
  ScalarDerivativeSequence ScalarSmoothSequenceUP ScalarUnitCutoffUP ScalarUnitCutoffSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CutoffSmoothness.
Variable R : realType.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->R^o}->Hom (Z k) R^o.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) (fun t : R^o=>`|t|) (@evaluation k) (@ZN k).

(** Source for [scalar_smooth_sequence_class_infinity]:
    successive ordinary derivative coefficients yield
    all exact higher differentials and their
    continuity, Federer 3.1.11, p. 220,
    as used for the cutoff on p. 223. *)
Lemma scalar_smooth_sequence_class_infinity (f : R->R) (F : nat->R->R) :
  is_scalar_smooth_derivative_sequence f F ->
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    evaluation ZN (fun _=>True) f.
Proof.
move=> [h0 hF]; have he : F 0%N=f := funext h0.
rewrite -he; apply: (@scalar_derivative_sequence_class_infinity R R^o
  (fun t : R^o=>`|t|) (@scalar_absolute_value_norm R)
  Z evaluation ZN hZ (fun _=>True) F).
move=>k a _; exists (@scalar_coefficient_linear_map R R^o (F k.+1 a)).
split; first exact: hF.
by move=>t.
Qed.

(** Source for [scalar_unit_cutoff_class_infinity]:
    the second displayed function of Federer
    3.1.11, p. 223, is of
    class infinity. The theorem is stated
    for any lawful abstract multilinear spaces. *)
Theorem scalar_unit_cutoff_class_infinity :
  norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
    evaluation ZN (fun _=>True) (@ScalarUnitCutoff.value R).
Proof.
have [F hF] := @ScalarUnitCutoff.smooth_derivatives R.
exact: scalar_smooth_sequence_class_infinity hF.
Qed.

(** Source for [scalar_smooth_unit_cutoff_exists]:
    existence of a smooth nonincreasing scalar
    cutoff, one before zero and zero after
    one, Federer 3.1.11, p. 223.
    This form is used in 3.1.13,
    pp. 224–225, through its abstract laws. *)
Theorem scalar_smooth_unit_cutoff_exists :
  exists g : R->R, is_scalar_unit_cutoff g /\
    norm_class_infinity (fun t : R^o=>`|t|) (fun t : R^o=>`|t|)
      evaluation ZN (fun _=>True) g.
Proof.
exists (@ScalarUnitCutoff.value R); split.
- exact: ScalarUnitCutoff.laws.
- exact: scalar_unit_cutoff_class_infinity.
Qed.
End CutoffSmoothness.
