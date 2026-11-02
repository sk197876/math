(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import AlternatingAlgebra.
From Federer Require Import FiniteIndependence Biorthogonal PairingLinear CovectorProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.4.3, first assertion and its proof: evaluation on the
    e_mu separates all the ordered products omega_lambda. *)
(** Source for [omega_lambda_independent]: Federer (1969), 1.4.3, p. 19,
    opening assertion and biorthogonal-vector argument. In words: Increasing
    products of a finite independent family of covectors are independent;
    evaluation on the corresponding products of biorthogonal vectors gives
    the Kronecker pairing. Formalises the indicated part of the passage
    under the hypotheses in the statement below. *)
Theorem omega_lambda_independent (K : fieldType) (h2 : (1+1 : K) != 0)
    (V : lmodType K) n (omega : 'I_n -> A_m V K^o 1) :
  finite_independent omega -> forall m, finite_independent (@omega_lambda K h2 V n omega m).
Proof.
move=> hw m; have [e he] := covectors_biorthogonal hw.
apply: (@finite_independent_separating K (Finite.clone (Lambda n m) _) (A_m V K^o m)
  (@omega_lambda K h2 V n omega m) (fun lambda => pairing_right (e_lambda e (val lambda)))).
move=> lambda mu; by rewrite pairing_rightE (pairing_e_omega h2 he) eq_sym.
Qed.
