(** Supporting Federer (1969), 3.4.8(5), p. 328:
    the original finite polynomial sum gives a witness for the
    independent Taylor-operator value law. The construction proves
    existence; only its opaque specified map is used downstream. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum RealNormUP LinearBasis
  SymmetricForms SymmetricFormSum SymmetricPolynomialEvaluation HomogeneousPolynomialFunctions PolynomialFunctions PolynomialRepresentations
  AnalyticGermRing FiniteJetDegreeIndices AnalyticTaylorSectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_taylor_polynomial_witness]: construction
    witnessing the original finite Taylor sum of 1.10.4, p. 46,
    for the auxiliary argument of Federer 3.4.8(5), p. 328.
    The selected abstract Taylor operator will expose its value law. *)
Definition finite_taylor_polynomial_witness (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) l (c:{ffun finite_jet_degree_indices n l->K^o}):
    PolynomialFunction X K^o:=
  polynomial_from_forms (\sum_(k<l) sform_include (finite_taylor_coefficient_form he c k)).

(** Source for [finite_taylor_polynomial_witness_values]: exact
    original finite polynomial values for the existence proof,
    supporting Federer 3.4.8(5), p. 328. *)
Lemma finite_taylor_polynomial_witness_values (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) l (c:{ffun finite_jet_degree_indices n l->K^o}) x:
  finite_taylor_polynomial_witness he c x =
    \sum_(k<l) sform_polynomial_value (finite_taylor_coefficient_form he c k) x.
Proof.
rewrite /finite_taylor_polynomial_witness polynomial_from_formsE symmetric_polynomial_value_sum.
apply:eq_bigr=>k _;exact:symmetric_polynomial_value_include.
Qed.

(** Source for [analytic_finite_taylor_section_exists]: supporting
    existence for the independent original Taylor-polynomial value
    law, Federer 3.4.8(5), p. 328. The empty sum remains included. *)
Theorem analytic_finite_taylor_section_exists (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0):
  exists T:{ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X NX hNX 0,
    is_analytic_finite_taylor_section he J T.
Proof.
exists (fun c=>J (finite_taylor_polynomial_witness he c))=>c.
exists (finite_taylor_polynomial_witness he c);split;first exact:finite_taylor_polynomial_witness_values.
reflexivity.
Qed.

(** Source for [analytic_finite_taylor_section_formula]: supporting
    uniqueness of the prescribed original polynomial germ,
    Federer 3.4.8(5), p. 328. Actual function extensionality identifies
    every witness with the proved finite polynomial sum. *)
Lemma analytic_finite_taylor_section_formula (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0)
    (T:{ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X NX hNX 0):
  is_analytic_finite_taylor_section he J T ->forall c,
    T c = J (finite_taylor_polynomial_witness he c).
Proof.
move=>hT c;have [P [hValues hGerm]]:=hT c.
have hEqual:P = finite_taylor_polynomial_witness he c.
  apply:polynomial_function_ext=>x;by rewrite hValues finite_taylor_polynomial_witness_values.
by rewrite hEqual in hGerm.
Qed.
