(** Boundary regressions for the corrected opening assertion of Federer
    1.4.5, p. 20. These concrete examples belong to the project. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior OrdinaryTensorClassification
  OrdinaryTensorLeftObstruction OrdinaryTensorSmallSpaces
  SmallVectorSpaceAlternatives FiniteBasisComparison DualityAnnihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Examples.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Local Notation U n := (alternating_unital_algebra h2
  (coordinate_space K n) (scalar_algebra K)).
Local Notation E n := (exterior_algebra (coordinate_space K n)).
Local Notation T n m := (algebra_tensor (U n) (E m)).
Local Notation G n m := (tensor_grading_product
  (A_star_grading (coordinate_space K n) K^o)
  (exterior_grading (coordinate_space K m))).

(** Source for [coordinate_successor_space_not_zero]: supporting boundary
    fact for the regressions of Federer 1.4.5, p. 20. An actual coordinate
    basis vector in positive dimension is nonzero. *)
Lemma coordinate_successor_space_not_zero n :
    ~ vector_space_is_zero (coordinate_space K n.+1).
Proof.
move=> hz.
have hn := basis_vector_nonzero (@coordinate_basisP K n.+1)
  (ord0 : 'I_n.+1).
by rewrite (hz (@coordinate_basis K n.+1 ord0)) eqxx in hn.
Qed.

(** Source for [zero_left_plane_ordinary_exception]: regression for the
    missing zero-space exception in Federer 1.4.5, p. 20. V=0 and W=K^2
    gives graded anticommutativity and fails ordinary commutativity. *)
Theorem zero_left_plane_ordinary_exception :
    graded_anticommutative (G 0 2) (alg_mul (T 0 2)) /\
      ~ commutative (alg_mul (T 0 2)).
Proof.
split.
- exact: (@ordinary_tensor_zero_left_anticommutative K h2
    (coordinate_space K 0) (coordinate_space K 2) (@coordinate_zero K)).
- apply: (@ordinary_tensor_right_pair_not_commutative K h2
    (coordinate_space K 0) (coordinate_space K 2) (@coordinate_basis K 2)).
  exact: finite_basis_independent (@coordinate_basisP K 2).
Qed.

(** Source for [plane_zero_right_ordinary_exception]: symmetric boundary
    regression for Federer 1.4.5, p. 20. V=K^2 and W=0 gives graded
    anticommutativity and fails ordinary commutativity. The first factor
    is the original full scalar alternating algebra. *)
Theorem plane_zero_right_ordinary_exception :
    graded_anticommutative (G 2 0) (alg_mul (T 2 0)) /\
      ~ commutative (alg_mul (T 2 0)).
Proof.
split.
- exact: (@ordinary_tensor_zero_right_anticommutative K h2
    (coordinate_space K 2) (coordinate_space K 0) (@coordinate_zero K)).
- apply: (@ordinary_tensor_left_pair_not_commutative K h2
    (coordinate_space K 2) (coordinate_space K 0) (@coordinate_basis K 2)).
  exact: finite_basis_independent (@coordinate_basisP K 2).
Qed.

(** Source for [line_plane_ordinary_neither]: sharpness regression for
    Federer 1.4.5, p. 20. V=K and W=K^2 still gives neither product law,
    although one original space is a line. *)
Theorem line_plane_ordinary_neither :
    ~ commutative (alg_mul (T 1 2)) /\
      ~ graded_anticommutative (G 1 2) (alg_mul (T 1 2)).
Proof.
apply/ordinary_tensor_neither_iff; split.
- exact: coordinate_successor_space_not_zero.
split; first exact: coordinate_successor_space_not_zero.
right; exists (@coordinate_basis K 2).
exact: finite_basis_independent (@coordinate_basisP K 2).
Qed.

(** Source for [two_lines_ordinary_commutative]: boundary regression for
    Federer 1.4.5, p. 20. Two actual lines give an ordinarily commutative
    product which is not graded anticommutative. *)
Theorem two_lines_ordinary_commutative :
    commutative (alg_mul (T 1 1)) /\
      ~ graded_anticommutative (G 1 1) (alg_mul (T 1 1)).
Proof.
split.
- apply/ordinary_tensor_commutative_iff; split; right;
    exists (@coordinate_basis K 1); exact: coordinate_basisP.
- apply: ordinary_tensor_nonzero_factors_not_anticommutative;
    exact: coordinate_successor_space_not_zero.
Qed.
End Examples.
