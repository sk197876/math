(** Federer (1969), 4.1.7, pp. 355–357: the
    degree-zero real coefficient norm is absolute value.
    Reuse the original zeroth exterior identification
    and induced inner product from 1.7.5, pp. 31–33. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Bilinear InnerProductUP InnerNorm InnerExterior
  InnerExteriorLowDegrees ExteriorNorm ExteriorPowers ExteriorGrading
  AlternatingForms AlternatingZero AlternatingPairing SimpleZeroDegree
  ExteriorCovectorInner LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section ZeroDegreeCovectorNorm.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable V:lmodType R.
Variable B:V->V->R.
Hypothesis hB:is_inner_product B.

(** Source for [zeroth_inner_exterior_scalar]: the
    original polarity in degree zero is the scalar
    identification, supporting Federer 4.1.7, p. 357. *)
Lemma zeroth_inner_exterior_scalar (c:R):
  inner_exterior_form h2 hB (exterior_zeroth_inclusion V c)=@zero_form R V R^o c.
Proof.
apply:form_ext=>t; rewrite (tuple0 t) zero_formE.
rewrite -(@pairing_tuple R V R^o 0 [tuple]
  (inner_exterior_form h2 hB (exterior_zeroth_inclusion V c))) empty_e_lambda.
change (exterior_inner_form h2 hB (exterior_zeroth_inclusion V 1)
  (exterior_zeroth_inclusion V c)=c).
by rewrite exterior_inner_zeroth mul1r.
Qed.

(** Source for [zeroth_exterior_scalar_norm]: the
    actual scalar multivector has absolute scalar
    norm, supporting Federer 4.1.7, p. 357. *)
Lemma zeroth_exterior_scalar_norm (c:R):
  exterior_norm h2 hB (exterior_zeroth_inclusion V c)=`|c|.
Proof.
apply:inner_norm_value; first exact:normr_ge0.
by rewrite exterior_inner_zeroth -normrX ger0_norm ?sqr_ge0 // expr2.
Qed.

(** Source for [zeroth_covector_absolute_norm]: the
    actual degree-zero form norm is the absolute
    value of its coefficient, supporting Federer
    4.1.7, p. 357, with the prior 1.8.1 correction. *)
Theorem zeroth_covector_absolute_norm n (e:'I_n->V) (he:is_basis e)
    (phi:A_m V R^o 0):
  exterior_covector_norm h2 hB he phi=`|zero_form_value phi|.
Proof.
rewrite -{1}(zero_form_valueK phi) -zeroth_inner_exterior_scalar inner_exterior_form_norm.
exact:zeroth_exterior_scalar_norm.
Qed.
End ZeroDegreeCovectorNorm.
