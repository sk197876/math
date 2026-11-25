(** Supporting Federer (1969), 3.4.8(5), p. 328:
    scalar linearity of the actual finite Taylor operator follows
    from its independent polynomial value law. Constructions are
    used only for existence; the theorem applies to every specified map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum RealNormUP LinearBasis
  SymmetricForms SymmetricCoordinateDualBasis HomogeneousPolynomialFunctions PolynomialFunctions
  AnalyticGermRing AnalyticScalarsSealed RingScalarRestriction FiniteJetDegreeIndices
  AnalyticPolynomialGermUP AnalyticPolynomialGermLinear AnalyticTaylorSectionUP
  AnalyticTaylorSectionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_taylor_coefficient_form_linear]: supporting
    original finite Taylor arithmetic for Federer 3.4.8(5), p. 328.
    Each degree of the original coordinate-form synthesis is linear
    in its finite normalized derivative coefficients. *)
Lemma finite_taylor_coefficient_form_linear (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) l (k:'I_l):
  linear (fun c:{ffun finite_jet_degree_indices n l->K^o}=>
    finite_taylor_coefficient_form he c k).
Proof.
move=>a c d;rewrite /finite_taylor_coefficient_form scaler_sumr -big_split.
apply:eq_bigr=>b _;by rewrite !ffunE /= scalerDl scalerA.
Qed.

(** Source for [finite_taylor_polynomial_witness_linear]: supporting
    original finite Taylor arithmetic for Federer 3.4.8(5), p. 328.
    The exact original finite polynomial sum is linear as an actual
    polynomial function; this is proved from its value formula. *)
Lemma finite_taylor_polynomial_witness_linear (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) l:
  linear (@finite_taylor_polynomial_witness K X n e he l).
Proof.
move=>a c d;apply:polynomial_function_ext=>x.
change (finite_taylor_polynomial_witness he (a*:c+d) x =
  a*finite_taylor_polynomial_witness he c x+finite_taylor_polynomial_witness he d x).
rewrite !finite_taylor_polynomial_witness_values mulr_sumr -big_split.
apply:eq_bigr=>k _.
rewrite (finite_taylor_coefficient_form_linear he k a c d).
have hValue:=sform_polynomial_linear (K:=K) (V:=X) (W:=K^o) (m:=val k) a
  (finite_taylor_coefficient_form he c k) (finite_taylor_coefficient_form he d k).
exact:(congr1 (fun f:X->K^o=>f x) hValue).
Qed.

(** Source for [analytic_finite_taylor_section_linear]: supporting
    the original scalar-vector comparison for Federer 3.4.8(5), p. 328.
    Any Taylor operator satisfying the independent original polynomial
    value law is linear over the original scalar germs. *)
Theorem analytic_finite_taylor_section_linear (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0)
    (T:{ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X NX hNX 0):
  is_analytic_polynomial_germ_map J ->is_analytic_finite_taylor_section he J T ->
  linear (T:{ffun finite_jet_degree_indices n l->R^o}->
    [the lmodType R of ring_restricted_space (@AnalyticScalars.map R X NX hNX 0)
      (@analytic_germ_ring R X NX hNX 0)^o]).
Proof.
move=>hJ hT a c d.
rewrite !(analytic_finite_taylor_section_formula hT)
  (finite_taylor_polynomial_witness_linear he a c d).
exact:(analytic_polynomial_germ_linear hJ a
  (finite_taylor_polynomial_witness he c) (finite_taylor_polynomial_witness he d)).
Qed.
