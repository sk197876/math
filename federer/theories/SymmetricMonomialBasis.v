(** Federer (1969), 1.9.2, p. 42: for a finite basis e_1,...,e_n, monomials
    e^alpha form a basis in every symmetric degree. The coordinate
    calculation is transported through the abstract symmetric functor. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import TensorUP AlgebraUP LinearBasis GradedAlgebra GradedComponents
  GradedBasis FiniteCoordinates BasisInterpolation SymmetricAlgebra
  SymmetricGrading SymmetricMaps SymmetricPowerFunctor SymmetricMultiIndices
  SymmetricIndexBounds SymmetricMonomials SymmetricCoordinateMonomials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section MonomialBasis.
Variable K : fieldType.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation C := (coordinate_space K n).

(** Source for [symmetric_basis_coordinates]: Federer 1.9.2,
    p. 42, supporting coordinate isomorphism sending the given
    basis to the standard coordinate basis. *)
Definition symmetric_basis_coordinates := basis_interpolation he (@coordinate_basis K n).

(** Source for [symmetric_basis_synthesis]: Federer 1.9.2,
    p. 42, supporting inverse coordinate isomorphism sending
    the standard coordinate basis to the given basis. *)
Definition symmetric_basis_synthesis := basis_interpolation (coordinate_basisP K n) e.

(** Source for [symmetric_basis_coordinatesK]: Federer 1.9.2,
    p. 42, supporting cancellation of coordinate extraction
    followed by reconstruction. *)
Lemma symmetric_basis_coordinatesK : cancel symmetric_basis_coordinates symmetric_basis_synthesis.
Proof.
apply: (basis_linear_ext he (linear_comp symmetric_basis_synthesis symmetric_basis_coordinates)
  (linear_id V))=> i.
change (symmetric_basis_synthesis (symmetric_basis_coordinates (e i)) = e i).
by rewrite /symmetric_basis_coordinates /symmetric_basis_synthesis !basis_interpolationE.
Qed.

(** Source for [symmetric_basis_synthesisK]: Federer 1.9.2,
    p. 42, supporting cancellation in the opposite order. *)
Lemma symmetric_basis_synthesisK : cancel symmetric_basis_synthesis symmetric_basis_coordinates.
Proof.
apply: (basis_linear_ext (coordinate_basisP K n)
  (linear_comp symmetric_basis_coordinates symmetric_basis_synthesis) (linear_id C))=> i.
change (symmetric_basis_coordinates (symmetric_basis_synthesis (coordinate_basis K i)) = coordinate_basis K i).
by rewrite /symmetric_basis_coordinates /symmetric_basis_synthesis !basis_interpolationE.
Qed.

(** Source for [symmetric_monomials_basis]: Federer 1.9.2,
    p. 42, the monomials in a basis form a homogeneous basis
    of the whole symmetric algebra. This is the supporting graded
    version of the book's assertion for each degree. *)
Theorem symmetric_monomials_basis :
  is_graded_basis (symmetric_grading V) (symmetric_monomial e) (@symmetric_multi_degree n).
Proof.
have [hc hgc] := symmetric_coordinate_monomials_basis K n; split.
- have ht := basis_transport
    (symmetric_algebra_mapK symmetric_basis_synthesisK)
    (symmetric_algebra_mapK symmetric_basis_coordinatesK) hc.
  apply: basis_congr _ ht=> a.
  rewrite symmetric_monomial_natural.
  rewrite /symmetric_monomial /symmetric_monomial_word.
  congr 1 (symmetric_word _); congr 1 (flatten _); apply: eq_map=> i.
  change (nseq (a i) (symmetric_basis_synthesis (coordinate_basis K i)) = nseq (a i) (e i)).
  by rewrite /symmetric_basis_synthesis basis_interpolationE.
- exact: symmetric_monomial_homogeneous.
Qed.

(** Source for [symmetric_monomial_component]: Federer 1.9.2,
    p. 42, a monomial of total degree m, regarded as an element
    of the m-th symmetric power. *)
Definition symmetric_monomial_component m (a : symmetric_degree_indices n m) :
    symmetric_power V m :=
  @component_basis K (Choice.clone (symmetric_multi_index n) _)
    (symmetric_space V) (symmetric_grading V) (symmetric_monomial e)
    (@symmetric_multi_degree n) (symmetric_monomial_homogeneous e) m a.

(** Source for [symmetric_monomial_componentE]: Federer 1.9.2,
    p. 42, the component inclusion returns the displayed monomial. *)
Lemma symmetric_monomial_componentE m (a : symmetric_degree_indices n m) :
  component_val (symmetric_monomial_component a) = symmetric_monomial e (val a).
Proof. by []. Qed.

(** Source for [symmetric_monomial_component_basis]: Federer
    1.9.2, p. 42, monomials with exponent sum m form a basis
    of the m-th symmetric power, using the unbounded index predicate. *)
Theorem symmetric_monomial_component_basis m : is_basis (@symmetric_monomial_component m).
Proof.
exact (@component_basisP K (Choice.clone (symmetric_multi_index n) _)
  (symmetric_space V) (symmetric_grading V) (symmetric_monomial e)
  (@symmetric_multi_degree n) (proj1 symmetric_monomials_basis)
  (symmetric_monomial_homogeneous e) m).
Qed.

(** Source for [symmetric_finite_monomial]: Federer 1.9.2,
    p. 42, the monomial e^alpha indexed by the finite set Xi(n,m). *)
Definition symmetric_finite_monomial m (a : symmetric_indices n m) : symmetric_power V m :=
  symmetric_monomial_component (symmetric_indices_forget a).

(** Source for [symmetric_finite_monomial_basis]: Federer 1.9.2,
    p. 42, the stated finite monomial basis of the m-th symmetric
    power. The zero-dimensional and degree-zero cases are included. *)
Theorem symmetric_finite_monomial_basis m : is_basis (@symmetric_finite_monomial m).
Proof.
exact: (@basis_reindex K (Choice.clone (symmetric_degree_indices n m) _)
  (Choice.clone (symmetric_indices n m) _) (symmetric_power V m)
  (@symmetric_monomial_component m) (symmetric_monomial_component_basis m)
  (@symmetric_indices_bound n m) (@symmetric_indices_forget n m)
  (@symmetric_indices_boundK n m) (@symmetric_indices_forgetK n m)).
Qed.
End MonomialBasis.
