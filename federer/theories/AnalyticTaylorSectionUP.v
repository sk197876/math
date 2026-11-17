(** Supporting Federer (1969), 3.4.8(5), p. 328:
    prescribe the finite Taylor polynomial as an actual function
    before selecting its germ. The coefficients are the original
    monomial basis of 1.10.2 and finite sum of 1.10.4, pp. 45–46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom HomogeneousHom BoundedHom HomogeneousSum RealNormUP LinearBasis
  SymmetricForms SymmetricMultiIndices SymmetricCoordinateDualBasis
  HomogeneousPolynomialFunctions PolynomialFunctions AnalyticGermRing FiniteJetDegreeIndices.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_taylor_coefficient_form]: supporting original
    finite Taylor coefficients for Federer 3.4.8(5), p. 328. This
    algebraic sum uses exactly the original coordinate forms of
    1.10.2, p. 45, with no derivative or ideal law presumed. *)
Definition finite_taylor_coefficient_form (K:fieldType) (X:lmodType K) n
    (e:'I_n->X) (he:is_basis e) l (c:{ffun finite_jet_degree_indices n l->K^o})
    (k:'I_l):S_m X K^o k:=
  \sum_(b:symmetric_indices n k)
    (c (existT (fun h:'I_l=>symmetric_indices n (val h)) k b):K) *:
      symmetric_coordinate_basis_form he k b.

(** Source for [is_analytic_finite_taylor_section]: independent
    original polynomial-value specification for the finite Taylor
    operator supporting Federer 3.4.8(5), p. 328. It prescribes the
    actual finite polynomial function and its germ, and assumes no
    right-inverse, linearity or ideal-power statement. *)
Definition is_analytic_finite_taylor_section (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0)
    (T:{ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X NX hNX 0):Prop:=
  forall c,exists P:PolynomialFunction X R^o,
    (forall x,P x = \sum_(k<l) sform_polynomial_value
      (finite_taylor_coefficient_form he c k) x) /\T c = J P.
