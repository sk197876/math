(** Federer (1969), 4.1.8, p. 360: finitely
    many derivative estimates admit one input seminorm and
    constant. This supporting finite combination uses only
    monotonicity and nonnegativity of the original derivative
    seminorms from 4.1.1, pp. 343–344. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearSealed SmoothCompactSet
  SmoothFunctionDerivativesUP SmoothDerivativeSeminormUP SmoothDerivativeSeminormLaws
  SmoothFunctionTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section FiniteSmoothSeminormControl.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Variable E:lmodType R.
Variable ev:E->X->Y.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable K:smooth_compact_set hNX U.
Variables F W:Type.
Variable inclusion:F->E.
Variable admissible:F->Prop.
Variable points:W->Prop.
Variable I:finType.
Variable q:I->F->W->R.
Local Notation nu := (smooth_function_derivative_seminorm hD K).

(** Source for [finite_smooth_seminorm_control]: the finite
    collection of original coordinate derivative bounds in the
    slice argument of Federer 4.1.8, p. 360,
    has one dominating input order and constant. The
    estimate keeps the same compact K and includes
    the empty coordinate family and arbitrary admissible inputs. *)
Theorem finite_smooth_seminorm_control:
  (forall a:I,exists r:nat,exists C:R,0<=C /\forall f:F,admissible f->
    forall w:W,points w->q a f w<=C*nu r (inclusion f))->
  exists r:nat,exists C:R,0<=C /\forall a:I,forall f:F,admissible f->
    forall w:W,points w->q a f w<=C*nu r (inclusion f).
Proof.
move=>hBounds.
have[orders hOrders]:=choice hBounds.
have[coefficients hCoefficients]:=choice hOrders.
pose r:=(\max_(a:I) orders a)%N.
pose C:=\sum_(a:I) coefficients a.
have hC:0<=C by apply:sumr_ge0=>a _;exact:(hCoefficients a).1.
exists r,C;split;first exact:hC.
move=>a f hAdmissible w hPoint.
have hFirst:=((hCoefficients a).2 f hAdmissible w hPoint).
have hNu:=smooth_derivative_seminorm_monotone
  (smooth_function_derivative_seminorm_laws hD K (orders a))
  (smooth_function_derivative_seminorm_laws hD K r) (leq_bigmax a)
  (fun x hx=>hx) (inclusion f).
have hCommon:coefficients a<=C.
  rewrite /C (bigD1 a) //= lerDl.
  apply:sumr_ge0=>b _;exact:(hCoefficients b).1.
have hNonnegative:=smooth_derivative_seminorm_nonnegative
  (smooth_function_derivative_seminorm_laws hD K r) (inclusion f).
exact:(le_trans hFirst (le_trans (ler_wpM2l (hCoefficients a).1 hNu)
  (ler_wpM2r hNonnegative hCommon))).
Qed.
End FiniteSmoothSeminormControl.
