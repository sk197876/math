(** Federer (1969), 3.1.11, p. 220:
    a sequence of ordinary real-source derivatives
    supplies the exact higher differentials. This gives
    the class-infinity criterion used for the smooth scalar
    cutoff example on p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormClassOneUP NormClassOneLaws ContinuousMultilinearUP ContinuousMultilinearNorm
  ContinuousMultilinearScalar NormHigherDifferentialUP NormHigherDifferentialFields
  NormClassHigherUP MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section ScalarDerivativeSequence.
Variable R : realType.
Variable Y : lmodType R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->R^o}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space
  (fun t : R^o=>`|t|) NY (@evaluation k) (@ZN k).
Variable A : R->Prop.
Variable F : nat->R->Y.
Hypothesis hF : forall k a, A a -> exists L : Hom R^o Y,
  has_norm_differential (fun t : R^o=>`|t|) NY A (F k) a L /\
  forall t, L t=t*:F k.+1 a.

(** Source for [scalar_derivative_sequence_differentials]:
    the evaluation of D^k f on real arguments is their
    product times f^(k), Federer 3.1.11, p. 220.
    This direction constructs all higher differentials from
    the recursively verified ordinary derivative sequence. *)
Theorem scalar_derivative_sequence_differentials :
  exists D : forall k, R->Z k,
    (forall k a, A a -> has_norm_higher_differential
      (fun t : R^o=>`|t|) evaluation ZN A (F 0%N) k a (D k a)) /\
    (forall k a u, @evaluation k u (D k a)=(\prod_(i<k) u i)*:F k a) /\
    forall k, norm_class_zero (fun t : R^o=>`|t|) (@ZN k) A (D k).
Proof.
have hex k := @continuous_multilinear_scalar_identification R k Y (Z k) NY hNY
  (@evaluation k) (@ZN k) (@hZ k).
pose J k := projT1 (cid (hex k)).
have hJ k := projT2 (cid (hex k)).
have hJe k u y : @evaluation k u (J k y)=(\prod_(i<k) u i)*:y.
  by rewrite (continuous_multilinear_scalar_evaluation (@hZ k)) (hJ k).1.
have hJn k y : @ZN k (J k y)=NY y := (hJ k).2.2 y.
have hJb k : norm_bounded_linear NY (@ZN k) (J k).
  exists 1; split; first exact: ler01.
  by move=> y; rewrite hJn mul1r.
pose D k a := J k (F k a).
have hD : forall k a, A a -> has_norm_higher_differential
    (fun t : R^o=>`|t|) evaluation ZN A (F 0%N) k a (D k a).
  elim=> [|k ih] a ha.
  - split; first exact ha; by rewrite /D hJe big_ord0 scale1r.
  - have [L [hL hLe]] := @hF k a ha.
    have hDL := norm_differential_postcompose (@scalar_absolute_value_norm R) hL (hJb k).
    apply: (norm_higher_differential_field_step (@scalar_absolute_value_norm R)
      hNY hZ ih hDL).
    move=> u t; rewrite hom_compE /D !hJe hLe multilinear_successor_product scalerA.
    by [].
exists D; split; first exact hD.
split; first by move=> k a u; rewrite /D hJe.
move=> k.
have hexL a : exists L : Hom R^o (Z k), A a ->
    has_norm_differential (fun t : R^o=>`|t|) (@ZN k) A (D k) a L.
  case: (pselect (A a))=> [ha|ha].
  - have [L [hL _]] := @hF k a ha.
    exists (hom_comp (J k) L)=> _.
    exact (norm_differential_postcompose (@scalar_absolute_value_norm R) hL (hJb k)).
  - exists 0; by move=> /ha.
have [L hL] := choice hexL.
exact (@norm_everywhere_differentiable_class_zero R R^o (Z k)
  (fun t : R^o=>`|t|) (@ZN k)
  (continuous_multilinear_norm_is_norm hNY (@hZ k)) A (D k) L hL).
Qed.

(** Source for [scalar_derivative_sequence_class_infinity]:
    a real-source function with all recursively defined
    derivatives is of class infinity, supporting the
    smooth example in Federer 3.1.11, p. 223.
    Continuity of each derivative follows from the next
    derivative; it is not an additional assumption. *)
Theorem scalar_derivative_sequence_class_infinity :
  norm_class_infinity (fun t : R^o=>`|t|) NY evaluation ZN A (F 0%N).
Proof.
have [D [hD [hDe hDc]]] := scalar_derivative_sequence_differentials.
have hexL a : exists L : Hom R^o Y, A a ->
    has_norm_differential (fun t : R^o=>`|t|) NY A (F 0%N) a L.
  case: (pselect (A a))=> [ha|ha].
  - have [L [hL _]] := @hF 0%N a ha; by exists L.
  - exists 0; by move=> /ha.
have [L hL] := choice hexL.
have hzero := @norm_everywhere_differentiable_class_zero R R^o Y
  (fun t : R^o=>`|t|) NY hNY A (F 0%N) L hL.
move=> k; split; first exact hzero.
exists (D k); by split; [exact: hD|exact: hDc].
Qed.
End ScalarDerivativeSequence.
