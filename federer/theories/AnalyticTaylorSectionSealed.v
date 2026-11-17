(** Supporting Federer (1969), 3.4.8(5), p. 328:
    original finite Taylor interpolation behind its exact polynomial
    value law. The finite-sum existence construction stays opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP LinearBasis PolynomialFunctions AnalyticGermRing
  FiniteJetDegreeIndices AnalyticTaylorSectionUP AnalyticTaylorSectionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticFiniteTaylorSectionsSignature.
(** Source for [map]: the original finite Taylor polynomial germ,
    supporting Federer 3.4.8(5), p. 328. *)
Parameter map:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) l
  (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0),
  {ffun finite_jet_degree_indices n l->R^o}->@analytic_germ_ring R X NX hNX 0.
(** Source for [laws]: the independent original polynomial-function
    value law, supporting Federer 3.4.8(5), p. 328. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) l
  (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0),
  is_analytic_finite_taylor_section he J (@map R X NX hNX n e he l J).
End AnalyticFiniteTaylorSectionsSignature.
Module AnalyticFiniteTaylorSections:AnalyticFiniteTaylorSectionsSignature.
(** Source for [map]: private choice from proved exact finite
    Taylor existence, supporting Federer 3.4.8(5), p. 328. *)
Definition map (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0):=
  projT1 (cid (@analytic_finite_taylor_section_exists R X NX hNX n e he l J)).
(** Source for [laws]: the selected operator satisfies the
    independent polynomial value law, supporting 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (e:'I_n->X) (he:is_basis e) l
    (J:PolynomialFunction X R^o->@analytic_germ_ring R X NX hNX 0):
  is_analytic_finite_taylor_section he J (@map R X NX hNX n e he l J).
Proof. exact:(projT2 (cid (@analytic_finite_taylor_section_exists R X NX hNX n e he l J))). Qed.
End AnalyticFiniteTaylorSections.
