(** Vanishing hyperplane term in Federer (1969), 2.10.32, pp. 196–197. An
    n-fold product of vectors orthogonal to a unit normal in an
    n-dimensional space is zero. A nonzero product would give n independent
    vectors and hence a basis; orthogonality to this basis would make the
    normal orthogonal to itself. This uses the project's 1.6.1 dimension
    criterion and 1.7.1 orthogonality laws, without coordinates or an
    external determinant theorem. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp reals.
From Federer Require Import InnerProductUP InnerProductLaws OrthonormalFamilies InnerOrthogonality
  FiniteSpans FreeVector LinearBasis FiniteBasisCriterion FiniteDimension ExteriorGrading FiniteExteriorPowers
  ExteriorHadamardBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [unit_normal_hyperplane_top_product_zero]: supporting
    disappearance of the all-hyperplane term in
    the first exterior expansion of 2.10.32,
    p. 196. Any specified n-element basis
    suffices; dimension zero is included through
    the impossible unit-normal hypothesis. *)
Theorem unit_normal_hyperplane_top_product_zero (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (n : nat) (e v : 'I_n -> V) (u : V) :
  is_basis e -> B u u= 1 -> (forall i, inner_coordinate hB u (v i)=0) ->
  e_lambda v (ord_tuple n)=0.
Proof.
move=> he hu hv.
case: (eqVneq (e_lambda v (ord_tuple n)) 0)=> [//|hne]; exfalso.
have hi := exterior_product_nonzero_independent hne.
have hd : dim (finite_basis_vect he)=n by rewrite finite_basis_dimension card_ord.
have hbase := @finite_independent_basis R (finite_basis_vect he) n v hd hi.
have hspan : in_finite_span v u.
  exists (fun i=>basis_coordinates hbase u i).
  by rewrite -basis_synthesis_finiteE basis_coordinatesK.
have horth i : B u (v i)=0.
  by rewrite (inner_symmetric hB) -(inner_coordinateE hB); exact: hv.
have hh := inner_orthogonal_span hB horth hspan.
by rewrite hu in hh; move/eqP: hh; rewrite oner_eq0.
Qed.
