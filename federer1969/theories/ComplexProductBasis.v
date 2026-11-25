(** Federer (1969), 1.6.6, p. 27: complex bases of real alternating forms.
    The complex-coordinate comparison reduces the product-basis assertion to
    1.4.3, p. 19. Source context are recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import AlternatingCoordinates CovectorProducts GrassmannCoordinates OneFormProducts Bilinear
  ComplexScalarSealed ComplexCharacteristic ComplexValuedForms ComplexCoordinateRestriction
  ComplexFormWords FiniteCoordinates FiniteDimension FiniteBasisComparison FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ProductBasis.
Variable R : realFieldType.
Hypothesis hR : (1+1 : R) != 0.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation hC := (complex_two_nonzero R).
Variable U : lmodType R.
Variable n : nat.
Variable e : 'I_n -> U.
Hypothesis he : is_basis e.
Local Notation E := (coordinate_space C n).
Local Notation EV := (finite_basis_vect (coordinate_basisP C n)).
Variable a : 'I_n -> complex_valued_form embed U C^o 1.
Hypothesis ha : is_basis a.

(** Source for [complex_values_lambda]: Federer 1.6.6, p. 27,
    mixed products indexed by increasing selections. Ordered products
    of a given complex basis of the complex-valued real one-forms. *)
Definition complex_values_lambda m (l : Lambda n m) :=
  complex_values_word hR (fun j => a (tnth (val l) j)).

(** Source for [complex_product_basis]: Federer 1.6.6, p. 27,
    mixed basis. Products indexed by all increasing m-selections from
    any complex one-form basis form a complex basis in degree m.
    This includes the empty product and degrees above the dimension. *)
Theorem complex_product_basis m : is_basis (@complex_values_lambda m).
Proof.
pose ext := @coordinate_form_extension R C embed hR hC U n e he 1.
have hext : injective ext := can_inj (@coordinate_form_extensionK R C embed hR hC U n e he 1).
have hi : finite_independent (fun j => ext (a j)).
  exact: (finite_independent_map hext (finite_basis_independent ha)).
have hd : dim EV = n by rewrite finite_basis_dimension card_ord.
have hb := @covectors_basis_in_finite_dimension C hC EV n (fun j => ext (a j)) hd hi m.
have ht := @basis_transport C (Choice.clone (Lambda n m) _)
  (A_m E C^o m) (complex_valued_form embed U C^o m)
  (@omega_lambda C hC EV n (fun j => ext (a j)) m)
  (GRing.Linear.clone _ _ _ _ (@coordinate_form_restriction R C embed U n e he m) _)
  (GRing.Linear.clone _ _ _ _ (@coordinate_form_extension R C embed hR hC U n e he m) _)
  (@coordinate_form_restrictionK R C embed hR hC U n e he m)
  (@coordinate_form_extensionK R C embed hR hC U n e he m) hb.
apply: basis_congr ht => l.
change (coordinate_form_restriction embed he
  (one_forms_wedge hC (scalar_bilinear C) (1:C) (fun j => ext (a (tnth (val l) j)))) =
  complex_values_word hR (fun j => a (tnth (val l) j))).
rewrite coordinate_restriction_word.
congr (complex_values_word hR _); apply: boolp.funext => j.
exact: coordinate_form_extensionK.
Qed.
End ProductBasis.
