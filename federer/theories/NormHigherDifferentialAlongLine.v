(** Federer (1969), 3.1.11, p. 221:
    the derivatives of t to f(a+t v)
    are the repeated-v evaluations of D^i f
    along that path. For Taylor's formula,
    v=x-a, as corrected by the erratum,
    p. 4, book p. 221 line 1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialFiniteCalculus
  NormClassOneUP NormHigherCurveDerivativeUP NormDifferentialAffineLine
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearEvaluationBound
  NormHigherDifferentialUP NormHigherDifferentialFields
  MultilinearSuccessorArguments NormClassZeroPostcompose.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section LineFields.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).

(** Source for [higher_line_coefficient]:
    the repeated-v evaluation of D^i f(a+t v),
    displayed in the Taylor-path proof in Federer
    3.1.11, p. 221. The derivative fields
    are supplied through their exact graph laws. *)
Definition higher_line_coefficient (D : forall i, X->Z i)
    (a v : X) i t :=
  @evaluation i [ffun j : 'I_i=>v] (D i (a+t*:v)).

(** Source for [higher_line_coefficient_derivative]:
    the chain rule gives the successor coefficient
    along the affine path, Federer 3.1.11,
    p. 221. The proof uses the exact
    recursive differential at every needed order and
    bounded linear evaluation, with no symmetry assumption. *)
Theorem higher_line_coefficient_derivative (A : X->Prop) (f : X->Y)
    (D : forall i, X->Z i) (a v : X) i :
  (forall x, A x ->
    has_norm_higher_differential NX evaluation ZN A f i x (D i x)) ->
  (forall x, A x ->
    has_norm_higher_differential NX evaluation ZN A f i.+1 x (D i.+1 x)) ->
  forall t, A (a+t*:v) ->
    has_norm_differential (fun s : R^o=>`|s|) NY
      (fun s=>A (a+s*:v)) (higher_line_coefficient D a v i) t
      (scalar_coefficient_linear_map (higher_line_coefficient D a v i.+1 t)).
Proof.
move=> hDi hDj t ht.
have [L [hL he]] := @norm_higher_differential_field_step_elim
  R X Y NX hNX Z evaluation ZN A f i (D i)
  (a+t*:v) (D i.+1 (a+t*:v)) hDi (hDj _ ht).
have hNi := continuous_multilinear_norm_is_norm hNY (@hZ i).
have hline := norm_differential_along_affine_line hNX hNi hL.
have hb := continuous_multilinear_evaluation_bounded hNX (@hZ i) [ffun j : 'I_i=>v].
have hd := norm_differential_postcompose (@scalar_absolute_value_norm R) hline hb.
have hc : hom_comp (@evaluation i [ffun j : 'I_i=>v])
    (hom_comp L (scalar_coefficient_linear_map v))=
    scalar_coefficient_linear_map (higher_line_coefficient D a v i.+1 t).
  apply: hom_ext=>s; rewrite !hom_compE.
  change (@evaluation i [ffun j : 'I_i=>v] (L (s*:v))=
    s*:higher_line_coefficient D a v i.+1 t).
  by rewrite !linearZ /= he multilinear_successor_constant_arguments.
by rewrite hc in hd.
Qed.

(** Source for [higher_line_coefficient_continuous]:
    a continuous differential field gives a continuous
    scalar-source coefficient along the Taylor path,
    Federer 3.1.11, p. 221. *)
Lemma higher_line_coefficient_continuous (A : X->Prop)
    (D : forall i, X->Z i) (a v : X) i :
  norm_class_zero NX (@ZN i) A (D i) ->
  norm_class_zero (fun s : R^o=>`|s|) NY (fun s=>A (a+s*:v))
    (higher_line_coefficient D a v i).
Proof.
move=> hc.
have hp := @norm_class_zero_along_affine_line R X (Z i) NX (@ZN i)
  hNX A (D i) a v hc.
have hb := continuous_multilinear_evaluation_bounded hNX (@hZ i) [ffun j : 'I_i=>v].
exact (@norm_class_zero_postcompose R R^o (Z i) Y
  (fun t=>`|t|) (@ZN i) NY
  (continuous_multilinear_norm_is_norm hNY (@hZ i))
  (fun s=>A (a+s*:v)) (fun s=>D i (a+s*:v))
  (@evaluation i [ffun j : 'I_i=>v]) hp hb).
Qed.

(** Source for [higher_line_coefficient_zero]:
    the order-zero coefficient along the path is
    f(a+t v), as required in the Taylor
    reduction of Federer 3.1.11, p. 221. *)
Lemma higher_line_coefficient_zero (A : X->Prop) (f : X->Y)
    (D : forall i, X->Z i) (a v : X) t :
  has_norm_higher_differential NX evaluation ZN A f 0%N
    (a+t*:v) (D 0%N (a+t*:v)) ->
  higher_line_coefficient D a v 0%N t=f (a+t*:v).
Proof.
move=> [_ hf].
have he : [ffun j : 'I_0=>v]=[ffun j : 'I_0=>(0:X)].
  apply/ffunP=>j; by have := ltn_ord j; rewrite ltn0.
by rewrite /higher_line_coefficient he.
Qed.
End LineFields.
