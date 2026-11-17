(** Federer (1969), 3.4.7, p. 324: the
    actual diagonal of D^k Phi(a) is a
    homogeneous polynomial of degree k. Multiplying the
    divided-power polynomial by k factorial restores
    the original unnormalized derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP SymmetricForms SymmetricFormSum PolynomialFunctions
  SymmetricPolynomialEvaluation HomogeneousPolynomialFunctions PolynomialDiagonalNorm
  ContinuousMultilinearUP ContinuousMultilinearSealed AnalyticGermUP AnalyticGermJetsSealed
  AnalyticGermCoefficientForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_germ_directional_polynomial_exists]:
    the original homogeneous polynomial v mapped to
    D^k Phi(a) applied to k copies of v,
    3.4.7, p. 324. The function is
    the actual derivative evaluation, with its original
    factorial normalization; no polynomial model is assumed. *)
Theorem analytic_germ_directional_polynomial_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) a k (alpha:analytic_germ_space hNX a):
  exists P:PolynomialFunction X R^o,
    @is_homogeneous_polynomial R X R^o k P /\forall v,
      P v = @ContinuousMultilinear.evaluation R k X R^o NX (fun t=>`|t|)
        hNX (@scalar_absolute_value_norm R) [ffun _:'I_k=>v]
        (@AnalyticGermJets.value R X NX hNX a k alpha).
Proof.
have [F [hF _]]:=@analytic_germ_coefficient_forms_exists R X NX hNX a alpha.
pose G:S_m X R^o k:=(k`!)%:R*:F k.
pose P:=polynomial_from_forms (sform_include G).
have hP v:P v = sform_polynomial_value G v.
  by rewrite /P polynomial_from_formsE symmetric_polynomial_value_include.
exists P;split;first by exists G.
move=>v;rewrite hP sform_polynomial_diagonal_value /G sform_scaleE scalerA.
have hFactorial:((k`!)%:R:R)!=0 by rewrite pnatr_eq0 -lt0n fact_gt0.
rewrite (mulVf hFactorial) scale1r.
have hTuple:[ffun j:'I_k=>tnth [tuple v|_<k] j] = [ffun _:'I_k=>v].
  by apply/ffunP=>j;rewrite !ffunE tnth_mktuple.
by rewrite hF hTuple.
Qed.
