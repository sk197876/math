(** Federer (1969), 4.1.14, p. 372: the final
    class-one evaluation identity uses every continuous form.
    Apply the preceding uniform pullback estimate to the
    actual class-one convolution family and its proved first
    differential convergence. No derivative convergence is
    inferred from a family specified only by value convergence. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingForms AlternatingDual CurrentCoefficientNorms
  SmoothCompactSet CurrentMapDifferential CurrentMapDifferentialNormContinuity
  CurrentContinuousPullbackUniform CurrentCompactSmoothApproximationUP
  CurrentClassOneSmoothApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section CurrentClassOnePullbackApproximation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu m:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R nu)).
Local Notation PN := (@current_form_comass R h2 n m).
Local Notation QN := (@current_form_comass R h2 nu m).
Variables (U:X->Prop) (V:Y->Prop) (f:X->Y).
Hypothesis hClass:norm_class_one NX NY U f.
Hypothesis hImage:forall x,U x->V (f x).
Variable phi:Y->A_m Y R^o m.
Hypothesis hPhi:norm_class_zero NY QN V phi.
Local Notation D := (@current_map_differential R n nu U f).

(** Source for [current_class_one_continuous_pullback]: the
    original f#phi is continuous when f is class one
    and phi is continuous, supporting both finite-mass
    actions in Federer 4.1.14, p. 372. The
    actual sealed differential is used without an extra
    derivative field or smoothness premise. *)
Theorem current_class_one_continuous_pullback:
  norm_class_zero NX PN U
    (fun x=>A_m_dual (hom_as_linear (D x)) (phi (f x))).
Proof.
have[DF hDF]:=hClass.
have hf:=norm_class_one_zero hDF.
have hFirst:norm_class hNX hNY U f 1%N.
  exact:((@norm_class_firstP R X Y NX NY hNX hNY U f).2 hClass).
have hD:=@current_class_one_differential_continuous R n nu U f hFirst.
exact:(@current_continuous_pullback_class R h2 n nu m U V f D
  hImage hf hD phi hPhi).
Qed.

Variable K:smooth_compact_set hNX U.
Variable Z:X->Prop.
Variable g:nat->X->Y.
Hypothesis hFamily:@is_current_class_one_smooth_approximation R n nu U V K f Z g.

(** Source for [current_class_one_pullback_approximation_uniform]:
    the actual smooth approximations of the original
    class-one map have continuous pullbacks converging uniformly
    on K to the original pullback of every continuous
    form, supporting the last sentence of Federer 4.1.14,
    p. 372. Dg_i uses Z and Df uses U;
    no agreement of their openness witnesses is required. *)
Theorem current_class_one_pullback_approximation_uniform:
  forall epsilon:R,0<epsilon->exists N:nat,forall i:nat,(N<=i)%N->forall x,
    smooth_compact_carrier K x->
    PN (A_m_dual (hom_as_linear (@current_map_differential R n nu Z (g i) x))
          (phi (g i x))-
        A_m_dual (hom_as_linear (D x)) (phi (f x)))<epsilon.
Proof.
have[DF hDF]:=hClass.
have hf:=norm_class_one_zero hDF.
have hFirst:norm_class hNX hNY U f 1%N.
  exact:((@norm_class_firstP R X Y NX NY hNX hNY U f).2 hClass).
have hD:=@current_class_one_differential_continuous R n nu U f hFirst.
have[L hOrdinary]:=current_class_one_smooth_ordinary hFamily.
apply:(@current_continuous_pullback_uniform_on_compact R h2 n nu m U V f D
  hImage hf hD phi hPhi K g
  (fun i=>@current_map_differential R n nu Z (g i))).
- move=>i x hx.
  have hxZ:Z x:=@current_compact_smooth_domain_contains R n nu U V K f L Z g
    hOrdinary x hx.
  exact:(@current_compact_smooth_image R n nu U V K f L Z g hOrdinary i x hxZ).
- exact:current_compact_smooth_uniform hOrdinary.
- exact:current_class_one_smooth_differential_uniform hFamily.
Qed.
End CurrentClassOnePullbackApproximation.
