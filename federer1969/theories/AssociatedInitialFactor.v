(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.
From Federer Require Import AssociatedSubspace AssociatedInitialCoordinates InitialIndices InitialBasisProducts.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1: factor the common initial product from the surviving
    terms in the Grassmann expansion. xi_prime has exactly degree m-k. *)
Section Factor.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n m k : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
Variable hkn : (k <= n)%N.
Variable xi : exterior_power V m.
Hypothesis hT : forall i : 'I_k, FedererSimple.T xi (e (widen_ord hkn i)).
Local Notation initial := (Lambda_initial hkn).
Local Notation c := (xi_lambda h2 omega xi).
Local Notation I := {lambda : Lambda n m | Lambda_set initial \subset Lambda_set lambda}.
(** Source for [xi_prime]: Federer (1969), 1.6.1, p. 23, last paragraph,
    basis extension and the Grassmann-coordinate argument. In words: Extend
    a basis of the associated space to an ambient finite basis; multiplying
    the Grassmann expansion by e_i forces every coefficient omitting i to
    vanish. Definition or construction used to formalise this passage. *)
Definition xi_prime : exterior_power V (m-k) :=
  \sum_(lambda : I) c (val lambda) *: e_lambda e (val (InteriorComplements.nu (valP lambda))).
(** Source for [initial_factorisation]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem initial_factorisation :
  component_val xi = wedge (component_val (e_lambda e (val initial))) (component_val xi_prime).
Proof.
have hg := @initial_Grassmann_expansion K h2 V n m k e omega he hdual hkn xi hT.
have h := congr1 (@component_val K (exterior_space V) (exterior_grading V) m) hg.
rewrite linear_sum in h.
transitivity (\sum_(lambda : I) c (val lambda) *: component_val (e_lambda e (val (val lambda)))).
- apply: eq_trans h _.
  transitivity (\sum_(lambda : Lambda n m | Lambda_set initial \subset Lambda_set lambda)
    c lambda *: component_val (e_lambda e (val lambda))).
  + apply: eq_bigr => lambda _; exact: linearZ.
  + exact: sum_subtype.
- rewrite /xi_prime linear_sum.
  pose w (x : exterior_space V) := wedge (component_val (e_lambda e (val initial))) x.
  have hw : linear w := proj2 (wedge_bilinear V) _.
  change ((\sum_(lambda : I) c (val lambda) *: component_val (e_lambda e (val (val lambda)))) =
    w (\sum_(lambda : I) component_val (c (val lambda) *:
      e_lambda e (val (InteriorComplements.nu (valP lambda)))))).
  rewrite (big_morph w (linD hw) (lin0 hw)); apply: eq_bigr => lambda _.
  rewrite (linZ (linearP (@component_val K (exterior_space V) (exterior_grading V) (m-k))))
    (linZ hw).
  congr (_ *: _); exact: initial_basis_product.
Qed.
(** Source for [nonzero_initial_factorisation]: Federer (1969), 1.6.1, p.
    23, last paragraph, basis extension and the Grassmann-coordinate
    argument. In words: Extend a basis of the associated space to an ambient
    finite basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem nonzero_initial_factorisation : xi != 0 ->
  (k <= m)%N /\ exists xi' : exterior_power V (m-k),
    component_val xi = wedge (component_val (e_lambda e (val initial))) (component_val xi').
Proof.
move=> hx; split; first exact: (@initial_dimension_bound K h2 V n m k e omega he hdual hkn xi hT hx).
exists xi_prime; exact: initial_factorisation.
Qed.
End Factor.
