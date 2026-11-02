(** Federer (1969), 3.1.11, pp. 220–221:
    the Taylor integral formula for normed spaces,
    through the exact abstract higher differentials.
    The segment a+t(x-a) incorporates the erratum,
    p. 4, book p. 221 line 1. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP ContinuousMultilinearUP
  NormHigherDifferentialUP NormClassHigherUP NormClassHigherFields
  NormHigherCurveDerivativeUP NormHigherDifferentialAlongLine
  NormedStieltjesUP NormedStieltjesLaws NormCurveTaylorStieltjes.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section Taylor.
Variable R : realType.
Variables X Y : lmodType R.
Variables (NX : X->R) (NY : Y->R).
Hypothesis hNX : is_real_norm NX.
Hypothesis hNY : is_real_norm NY.
Variable Z : nat->lmodType R.
Variable evaluation : forall k, {ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN : forall k, Z k->R.
Hypothesis hZ : forall k, is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).

(** Source for [norm_taylor_integral_fields]:
    Federer 3.1.11, pp. 220–221, the
    general Taylor integral formula. Evaluation at a
    repeated vector expresses the printed tensor-power
    pairing through the abstract multilinear interface.
    The fields must be the actual higher differentials;
    their highest order is continuous on the given domain. *)
Theorem norm_taylor_integral_fields (A : X->Prop) (f : X->Y)
    (D : forall i, X->Z i) (a v : X) k :
  (forall i, (i<=k.+1)%N -> forall x, A x ->
    has_norm_higher_differential NX evaluation ZN A f i x (D i x)) ->
  norm_class_zero NX (@ZN k.+1) A (D k.+1) ->
  (forall t : R, 0<=t<= 1 -> A (a+t*:v)) ->
  has_normed_stieltjes_integral NY
    (fun t=>(((k.+1)`!)%:R)^-1*:
      (@evaluation k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 a)-
       @evaluation k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 (a+t*:v))))
    (fun t=>(1-t)^+k.+1) 0 1
    (f (a+v)-\sum_(i < k.+2) ((i`!)%:R)^-1*:
      (@evaluation i [ffun j : 'I_i=>v] (D i a))).
Proof.
move=> hD hc hseg.
pose B t := A (a+t*:v).
pose F := @higher_line_coefficient R X Y Z evaluation D a v.
have hF i (hi : (i<=k)%N) t (ht : B t) :
    has_norm_differential (fun s : R^o=>`|s|) NY B (F i) t
      (scalar_coefficient_linear_map (F i.+1 t)).
  apply: (@higher_line_coefficient_derivative R X Y NX NY hNX hNY
    Z evaluation ZN hZ A f D a v i _ _ t ht).
  - exact: hD i (leq_trans hi (leqnSn _)).
  - exact: hD i.+1 hi.
have hFc := @higher_line_coefficient_continuous R X Y NX NY hNX hNY
  Z evaluation ZN hZ A D a v k.+1 hc.
have hi := norm_curve_taylor_stieltjes hNY hseg hF hFc.
have hFzero i : F i 0=@evaluation i [ffun j : 'I_i=>v] (D i a).
  by rewrite /F /higher_line_coefficient scale0r addr0.
have hFone : F 0%N 1=f (a+v).
  have h1 : 0<=(1:R)<= 1 by rewrite ler01 lexx.
  have hh := @higher_line_coefficient_zero R X Y NX Z evaluation ZN A f D a v 1
    (hD 0%N (leq0n _) _ (hseg 1 h1)).
  by rewrite scale1r in hh.
have hsum : \sum_(i < k.+2) (((i`!)%:R)^-1*:F i 0)=
    \sum_(i < k.+2) ((i`!)%:R)^-1*:
      (@evaluation i [ffun j : 'I_i=>v] (D i a)).
  apply: eq_bigr=>i _; by rewrite hFzero.
rewrite hFone hsum in hi.
apply: normed_stieltjes_integral_ext _ _ hi=>t //.
by rewrite hFzero /F /higher_line_coefficient.
Qed.

(** Source for [norm_class_higher_taylor_integral]:
    the class-k hypothesis of the general Taylor
    formula in Federer 3.1.11, pp. 220–221,
    supplies all derivative fields used above.
    Their values are constrained by the exact graphs,
    and no completeness of either normed space is added. *)
Theorem norm_class_higher_taylor_integral (A : X->Prop) (f : X->Y) k :
  norm_class_higher NX NY evaluation ZN A f k.+1 ->
  exists D : forall i, X->Z i,
    (forall i, (i<=k.+1)%N -> forall x, A x ->
      has_norm_higher_differential NX evaluation ZN A f i x (D i x)) /\
    forall a v, (forall t : R, 0<=t<= 1 -> A (a+t*:v)) ->
      has_normed_stieltjes_integral NY
        (fun t=>(((k.+1)`!)%:R)^-1*:
          (@evaluation k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 a)-
           @evaluation k.+1 [ffun j : 'I_k.+1=>v] (D k.+1 (a+t*:v))))
        (fun t=>(1-t)^+k.+1) 0 1
        (f (a+v)-\sum_(i < k.+2) ((i`!)%:R)^-1*:
          (@evaluation i [ffun j : 'I_i=>v] (D i a))).
Proof.
move=> hk.
have [D [hD hc]] := @norm_class_higher_fields R X Y NX NY hNX hNY
  Z evaluation ZN hZ A f k.+1 hk.
exists D; split; first exact hD.
move=> a v hseg.
exact: norm_taylor_integral_fields hD (hc k.+1 (leqnn _)) hseg.
Qed.
End Taylor.
