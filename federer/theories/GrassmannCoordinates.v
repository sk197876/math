(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra finmap.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FiniteIndependence FiniteBasisCriterion FiniteDualDimension OneFormLinear
  Biorthogonal PairingLinear ScalarCoefficients OneFormProducts CovectorProducts CovectorIndependence.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3: the vectors e_j chosen biorthogonal to the n
    independent one-covectors form a basis when dim V=n. *)
(** Source for [biorthogonal_basis]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem biorthogonal_basis (K : fieldType) (V : vectType K) n
    (omega : 'I_n -> A_m V K^o 1) (e : 'I_n -> V) : dim V = n ->
  (forall i j, omega i [tuple e j] = if i == j then 1 else 0) -> is_basis e.
Proof.
move=> hd he; apply: finite_independent_basis hd _.
apply: (@finite_independent_separating K (Finite.clone 'I_n _) V e
  (fun i => hom_as_linear (one_hom (omega i)))).
exact: he.
Qed.

(** Federer 1.4.3, the two displayed reconstruction formulae and the
    named Grassmann coordinates phi_lambda and xi_lambda. *)
Section GrassmannCoordinates.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Local Notation I := (Finite.clone (Lambda n m) _).
Local Notation E := (exterior_power V m).
Local Notation A := (A_m V K^o m).
Local Notation el := (fun lambda : Lambda n m => e_lambda e (val lambda)).
Local Notation wl := (@omega_lambda K h2 V n omega m).
Local Notation heb := (finite_e_lambda_basis he h2 m).
(** Federer 1.4.3: first compute the dimension using 1.4.1 and 1.3.2;
    independence then gives the asserted basis of products. *)
(** Source for [finite_covector_power]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Definition or construction used to formalise this
    passage. *)
Definition finite_covector_power : vectType K := finite_form_power h2 he m.
(** Source for [covector_power_dimension]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Supporting lemma for
    this passage; not separately stated in the book. *)
Theorem covector_power_dimension : dim finite_covector_power = 'C(n,m).
Proof. exact: form_power_dimension. Qed.
(** Source for [exterior_covector_dimensions]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem exterior_covector_dimensions :
  dim finite_covector_power = dim (finite_exterior_power h2 he m) /\
  dim finite_covector_power = 'C(n,m).
Proof. by rewrite covector_power_dimension exterior_power_dimension. Qed.
(** Source for [omega_lambda_basis]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem omega_lambda_basis : is_basis wl.
Proof.
apply: (@finite_independent_basis_card K finite_covector_power I wl).
- by rewrite covector_power_dimension card_Lambda.
- apply: (@finite_independent_separating K I A wl (fun lambda => pairing_right (el lambda))).
  by move=> i j; rewrite pairing_rightE (pairing_e_omega h2 hdual) eq_sym.
Qed.

(** Source for [phi_lambda]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Definition or construction used to formalise this
    passage. *)
Definition phi_lambda (phi : A) (lambda : Lambda n m) : K := pairing (el lambda) phi.
(** Source for [xi_lambda]: Federer (1969), 1.4.3, p. 19, two reconstruction
    formulae and naming of Grassmann coordinates. In words: A form or
    multivector is the sum of its pairings with the dual Grassmann basis
    times the corresponding basis elements; these pairings are its Grassmann
    coordinates. Definition or construction used to formalise this passage. *)
Definition xi_lambda (xi : E) (lambda : Lambda n m) : K := pairing xi (wl lambda).
(** Source for [phi_lambda_linear]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma phi_lambda_linear lambda : linear (fun phi : A => (phi_lambda phi lambda : K^o)).
Proof. exact: pairing_right_linear. Qed.
(** Source for [xi_lambda_linear]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma xi_lambda_linear lambda : linear (fun xi : E => (xi_lambda xi lambda : K^o)).
Proof. exact: hom_linear. Qed.

(** Source for [pairing_basis_ext]: Federer (1969), 1.4.3, p. 19,
    finite-dimensional basis and dimension paragraph. In words: The products
    of dual basic covectors form the dual basis of the m-th exterior power;
    both degree-m spaces have dimension binomial(n,m). Supporting lemma for
    this passage; not separately stated in the book. *)
Lemma pairing_basis_ext (phi psi : A) :
  (forall lambda, pairing (el lambda) phi = pairing (el lambda) psi) -> phi = psi.
Proof.
move=> h; apply: pairing_ext => xi.
exact (@basis_linear_ext K (Choice.clone (Lambda n m) _) E el heb K^o
  (pairing_left phi) (pairing_left psi) h xi).
Qed.
(** Source for [omega_sum_pairing]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma omega_sum_pairing (c : Lambda n m -> K) mu :
  pairing (el mu) (\sum_(lambda : I) c lambda *: wl lambda) = c mu.
Proof.
pose f (lambda : I) := hom_of_linear (pairing_right (el lambda)).
have hf i j : f i (wl j) = if i == j then 1 else 0.
  by rewrite /f hom_of_linearE pairing_rightE (pairing_e_omega h2 hdual) eq_sym.
exact (@biorthogonal_sum K A I f wl hf c mu).
Qed.
(** Source for [covector_Grassmann_expansion]: Federer (1969), 1.4.3, p. 19,
    two reconstruction formulae and naming of Grassmann coordinates. In
    words: A form or multivector is the sum of its pairings with the dual
    Grassmann basis times the corresponding basis elements; these pairings
    are its Grassmann coordinates. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem covector_Grassmann_expansion (phi : A) :
  phi = \sum_(lambda : I) phi_lambda phi lambda *: wl lambda.
Proof. apply: pairing_basis_ext => mu; by rewrite omega_sum_pairing. Qed.

(** Source for [xi_lambda_coordinate]: Federer (1969), 1.4.3, p. 19, two
    reconstruction formulae and naming of Grassmann coordinates. In words: A
    form or multivector is the sum of its pairings with the dual Grassmann
    basis times the corresponding basis elements; these pairings are its
    Grassmann coordinates. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Lemma xi_lambda_coordinate (xi : E) lambda :
  xi_lambda xi lambda = basis_coordinates heb xi lambda.
Proof.
apply: (basis_linear_ext heb (pairing_left (wl lambda))
  (linear_comp (GRing.Linear.clone _ _ _ _ (free_eval lambda) _) (basis_coordinates heb))) xi => mu.
change (pairing (el mu) (wl lambda) = basis_coordinates heb (el mu) lambda).
by rewrite (pairing_e_omega h2 hdual) basis_coordinatesE deltaE.
Qed.
(** Source for [vector_Grassmann_expansion]: Federer (1969), 1.4.3, p. 19,
    two reconstruction formulae and naming of Grassmann coordinates. In
    words: A form or multivector is the sum of its pairings with the dual
    Grassmann basis times the corresponding basis elements; these pairings
    are its Grassmann coordinates. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem vector_Grassmann_expansion (xi : E) :
  xi = \sum_(lambda : I) xi_lambda xi lambda *: el lambda.
Proof.
rewrite -{1}(basis_coordinatesK heb xi) basis_synthesis_finiteE.
apply: eq_bigr => lambda _; by rewrite xi_lambda_coordinate.
Qed.

End GrassmannCoordinates.

(** Federer 1.4.3: the basis assertion needs only the independence of
    the given one-covectors and dim V=n; the dual vectors are constructed. *)
(** Source for [covectors_basis_in_finite_dimension]: Federer (1969), 1.4.3,
    p. 19, finite-dimensional basis and dimension paragraph. In words: The
    products of dual basic covectors form the dual basis of the m-th
    exterior power; both degree-m spaces have dimension binomial(n,m).
    Formalises the indicated part of the passage under the hypotheses in the
    statement below. *)
Theorem covectors_basis_in_finite_dimension (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : vectType K) n (omega : 'I_n -> A_m V K^o 1) :
  dim V = n -> finite_independent omega -> forall m,
    is_basis (@omega_lambda K h2 V n omega m).
Proof.
move=> hd hw m; have [e he] := covectors_biorthogonal hw.
have heb := biorthogonal_basis hd he.
exact (@omega_lambda_basis K h2 V n m e omega heb he).
Qed.
