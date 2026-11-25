(** Federer (1969), 3.1.24, p. 239: the
    exact scalar value of the weighted composition sum S(p). *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom SymmetricAlgebra SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism
  SymmetricMultiIndices SymmetricMonomials SymmetricDividedMonomials
  HomogeneousPolynomialFunctions CompositionMultiIndices CompositionMultinomial CompositionFormCoefficient
  CompositionPositiveDegree ScalarAnalyticFraction ScalarAnalyticFractionPolynomial
  ScalarAnalyticCompositionCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [analytic_composition_scalar_sum]: the equality
    sum_(alpha in S(p)) gamma^(sum alpha) (sum alpha)!/alpha!
    = gamma(gamma+1)^(p-1) in Federer 3.1.24,
    p. 239. The proof follows the printed rational
    special case, using its actual derivatives and the proved
    3.1.11 composition formula. It includes gamma=0. *)
Theorem analytic_composition_scalar_sum (R:realType) (g:R) p :
  0<=g -> (1<=p)%N ->
  \sum_(a:composition_indices p p)
    (g^+(symmetric_multi_degree (composition_indices_unbound a))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R)/
      (symmetric_multi_factorial (composition_indices_unbound a))%:R=
    g*(g+1)^+(p-1).
Proof.
move=>hg hp.
pose v:'I_p->R^o:=fun i=>sform_polynomial_value (scalar_analytic_fraction_form 1 (val i).+1) 1.
pose L j:Hom (symmetric_space R^o) R^o:=sform_homogeneous (scalar_analytic_fraction_form g j).
have hc:=scalar_analytic_composition_coefficient hg hp.
rewrite (@composition_differential_form_coefficient_value R R^o R^o R^o p
  (fun i=>scalar_analytic_fraction_form (1:R) i) (fun i=>scalar_analytic_fraction_form g i)
  (@pchar_num R) p 1 (leqnn p)) in hc.
have hw:=@composition_weight_coefficient_formula R R^o R^o p v L p (leqnn p).
rewrite hw in hc.
have hv:v= (fun _:'I_p=>(1:R^o)).
  apply: funext=>i; rewrite /v (@scalar_analytic_fraction_polynomial_unit R 1 (val i).+1 (leq0n (val i))).
  exact: expr1n.
have hsum:(\sum_(a:composition_indices p p)
    (g^+(symmetric_multi_degree (composition_indices_unbound a))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R)/
      (symmetric_multi_factorial (composition_indices_unbound a))%:R)=
    \sum_(a:composition_indices p p)
      @composition_multinomial_term R R^o R^o p v L (composition_indices_unbound a).
  apply: eq_bigr=>a _.
  have hd:=composition_indices_positive_outer_degree a hp.
  rewrite /composition_multinomial_term /L hv (@scalar_analytic_fraction_form_monomial R g p
    (fun _:'I_p=>(1:R^o)) (composition_indices_unbound a) hd).
  have hm:symmetric_scalar_monomial (fun _:'I_p=>(1:R)) (composition_indices_unbound a)= 1.
    rewrite /symmetric_scalar_monomial.
    under eq_bigr do rewrite expr1n.
    by rewrite prodr_const expr1n.
  rewrite hm mulr1.
  change ((g^+(symmetric_multi_degree (composition_indices_unbound a))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R)*
      (symmetric_multi_factorial (composition_indices_unbound a))%:R^-1=
    (symmetric_multi_factorial (composition_indices_unbound a))%:R^-1*
      (g^+(symmetric_multi_degree (composition_indices_unbound a))*
      (symmetric_multi_degree (composition_indices_unbound a))`!%:R)).
  exact: mulrC.
by rewrite -hsum in hc.
Qed.
