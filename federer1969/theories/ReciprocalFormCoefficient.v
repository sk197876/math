(** Federer (1969), 3.1.11, p. 223: the coefficient
    sum in the displayed higher reciprocal formula. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals ring.
From Federer Require Import Hom HomogeneousHom BoundedHom SymmetricForms
  SymmetricFormSum HomogeneousPolynomialFunctions SymmetricMultiIndices
  SymmetricDividedMonomials CompositionMultiIndices CompositionMultinomial
  CompositionFormCoefficient ScalarFormMonomials ScalarReciprocalHigherDifferentials
  ScalarReciprocalForms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [reciprocal_differential_form_coefficient]:
    sum over S(p) of (sum alpha)!/alpha! times 1/b times
    the symmetric product of (-D^i f/b)^alpha_i, exactly the
    displayed formula in Federer 3.1.11, p. 223. *)
Definition reciprocal_differential_form_coefficient (R : realType)
    (X : lmodType R) k (phi : forall i, S_m X R^o i) (b : R) p : S_m X R^o p :=
  \sum_(a : composition_indices k p)
    let alpha := composition_indices_unbound a in
    (((symmetric_multi_degree alpha)`!)%:R/(symmetric_multi_factorial alpha)%:R/b)*:
      sform_component p (scalar_form_monomial (fun j=>(-b^-1)*:phi j) alpha).

(** Source for [reciprocal_composition_form_coefficient]: the
    general composition coefficient specializes to the printed
    reciprocal coefficient, Federer 3.1.11, p. 223. This
    is an identity in the actual symmetric-form space. *)
Theorem reciprocal_composition_form_coefficient (R : realType)
    (X : lmodType R) k (phi : forall i, S_m X R^o i) (b : R) p :
  composition_differential_form_coefficient k phi (scalar_reciprocal_form b) p=
    reciprocal_differential_form_coefficient k phi b p.
Proof.
rewrite /composition_differential_form_coefficient /reciprocal_differential_form_coefficient.
apply: eq_bigr=>a _.
apply: (@sform_polynomial_injective R X R^o p (@pchar_num R)); apply: funext=>v.
rewrite (@composition_differential_form_term_value R X R^o R^o k phi
  (scalar_reciprocal_form b) (@pchar_num R) p a v)
  /composition_multinomial_term scalar_reciprocal_form_monomial.
pose alpha := composition_indices_unbound a.
pose d := symmetric_multi_degree alpha.
pose c (i : 'I_k) := sform_polynomial_value (phi (val i).+1) v.
have hscale j t (F : S_m X R^o j) :
    sform_polynomial_value (t*:F) v=t*:sform_polynomial_value F v.
  have he : sform_polynomial_value (t*:F)=t*:sform_polynomial_value F.
    exact: linearZ.
  exact (congr1 (fun H : X->R^o=>H v) he).
rewrite hscale (@scalar_form_monomial_component_value R X k
  (fun j=>(-b^-1)*:phi j) (@pchar_num R) alpha p v (composition_indices_weight a)).
have hc : (fun i : 'I_k=>sform_polynomial_value ((-b^-1)*:phi (val i).+1) v)=
    (fun i : 'I_k=>(-b^-1)*c i).
  apply: funext=>i; exact: hscale.
rewrite hc scalar_monomial_common_scale.
change (((symmetric_multi_factorial alpha)%:R)^-1*
  (scalar_reciprocal_derivative_coefficient d b*symmetric_scalar_monomial c alpha)=
  ((d`!)%:R/(symmetric_multi_factorial alpha)%:R/b)*
    ((-b^-1)^+d*symmetric_scalar_monomial c alpha) :> R).
have hneg : (-b^-1)^+d=(-1)^+d*(b^-1)^+d.
  have hh : -b^-1=(-1)*b^-1 by rewrite mulN1r.
  by rewrite {1}hh exprMn.
rewrite /scalar_reciprocal_derivative_coefficient [(b^-1)^+d.+1]exprS hneg.
ring.
Qed.
