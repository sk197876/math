(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg finmap.
From Federer Require Import ExteriorCore.
From Federer Require Import LinearBasis GradedBasis FiniteCoordinates
  ExteriorIndices FiniteExteriorBasis.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.2: e_lambda is the indicated exterior product, regarded as
    an element of the actual homogeneous component. This definition also
    applies to the increasing sequences in an infinite ordered basis. *)
Section Products.
Variable K : fieldType.
Variable I : choiceType.
Variable V : lmodType K.
Variable e : I -> V.
Variable m : nat.
(** Source for [e_lambda_homogeneous]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma e_lambda_homogeneous (t : m.-tuple I) :
  homogeneous (exterior_grading V) m (exterior_word [seq e i | i <- t]).
Proof.
have h := exterior_word_homogeneous [seq e i | i <- t].
by rewrite size_map size_tuple in h.
Qed.
(** Source for [e_lambda]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition e_lambda (t : m.-tuple I) : exterior_power V m :=
  @Component K (exterior_space V) (exterior_grading V) m
    (exterior_word [seq e i | i <- t]) (introT eqP (e_lambda_homogeneous t)).
(** Source for [e_lambdaE]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma e_lambdaE t : component_val (e_lambda t) = exterior_word [seq e i | i <- t].
Proof. by []. Qed.
End Products.

Section FunctorInverse.
Variable K : fieldType.
Variables V W : lmodType K.
Variables (f : {linear V -> W}) (g : {linear W -> V}).
Hypothesis fg : cancel f g.
(** Source for [exterior_algebra_mapK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_algebra_mapK : cancel (exterior_algebra_map f) (exterior_algebra_map g).
Proof.
apply: (exterior_algebra_ext (@exterior_algebra_exists K V)
  (algebra_comp (exterior_algebra_map g) (exterior_algebra_map f))
  (algebra_id (exterior_algebra V))).
change (forall v, exterior_algebra_map g
  (exterior_algebra_map f (exterior_generator v)) = exterior_generator v).
by move=> v; rewrite !exterior_algebra_mapE fg.
Qed.
(** Source for [exterior_power_mapK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma exterior_power_mapK m : cancel (exterior_power_map f m) (exterior_power_map g m).
Proof. move=> x; apply: val_inj; exact: exterior_algebra_mapK. Qed.
End FunctorInverse.

Section FinitePowerBasis.
Variable K : fieldType.
Hypothesis h2 : (1 + 1 : K) != 0.
Variable n m : nat.
Local Notation C := (coordinate_space K n).
Local Notation e := (@coordinate_basis K n).
(** Source for [coordinate_e_lambda]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition coordinate_e_lambda (t : Lambda n m) := e_lambda e (val t).

(** Source for [coordinate_e_lambda_basis]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem coordinate_e_lambda_basis : is_basis coordinate_e_lambda.
Proof.
have hb := @component_basisP K (Choice.clone (selection_index n) _)
  (exterior_space C) (exterior_grading C) (finite_exterior_basis K n)
  (fun b => size (selected_indices n b)) (finite_exterior_basisP h2 n)
  (@finite_exterior_basis_homogeneous K n) m.
have hr := @basis_reindex K (Choice.clone (degree_selection n m) _)
  (Choice.clone (Lambda n m) _) (exterior_power C m)
  (@component_basis K (Choice.clone (selection_index n) _)
    (exterior_space C) (exterior_grading C) (finite_exterior_basis K n)
    (fun b => size (selected_indices n b)) (@finite_exterior_basis_homogeneous K n) m)
  hb (@selection_Lambda n m) (@Lambda_selection n m)
  (@selection_LambdaK n m) (@Lambda_selectionK n m).
apply: basis_congr _ hr => t; apply: val_inj.
change (finite_exterior_basis K n (val (Lambda_selection t)) =
  exterior_word [seq e i | i <- val t]).
by rewrite /finite_exterior_basis selection_LambdaE.
Qed.
End FinitePowerBasis.

(** Federer 1.3.2: transporting the preceding construction preserves each
    named basis vector, hence preserves precisely the products e_lambda. *)
Section BasisCoordinates.
Variable K : fieldType.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.
Local Notation C := (coordinate_space K n).
Local Notation c := (@coordinate_basis K n).
(** Source for [basis_from_coordinates]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition basis_from_coordinates : {linear C -> V} :=
  linear_comp (basis_synthesis e) (basis_coordinates (coordinate_basisP K n)).
(** Source for [basis_to_coordinates]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Definition or construction used to
    formalise this passage. *)
Definition basis_to_coordinates : {linear V -> C} :=
  linear_comp (basis_synthesis c) (basis_coordinates he).
(** Source for [basis_from_coordinatesE]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma basis_from_coordinatesE i : basis_from_coordinates (c i) = e i.
Proof. by rewrite /basis_from_coordinates /= basis_coordinatesE basis_synthesisE. Qed.
(** Source for [basis_from_coordinatesK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma basis_from_coordinatesK : cancel basis_from_coordinates basis_to_coordinates.
Proof.
move=> x; change (basis_synthesis c (basis_coordinates he
  (basis_synthesis e (basis_coordinates (coordinate_basisP K n) x))) = x).
by rewrite basis_synthesisK basis_coordinatesK.
Qed.
(** Source for [basis_to_coordinatesK]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma basis_to_coordinatesK : cancel basis_to_coordinates basis_from_coordinates.
Proof.
move=> x; change (basis_synthesis e (basis_coordinates (coordinate_basisP K n)
  (basis_synthesis c (basis_coordinates he x))) = x).
by rewrite basis_synthesisK basis_coordinatesK.
Qed.

(** Source for [finite_e_lambda]: Federer (1969), 1.3.2, pp. 14-15, ordered
    products of basis vectors and the final dimension display. In words:
    Increasing products of basis vectors form a basis of each exterior
    power; for dimension n the m-th power has dimension binomial(n,m), and
    is zero for m>n. Definition or construction used to formalise this
    passage. *)
Definition finite_e_lambda m (t : Lambda n m) := e_lambda e (val t).
(** Source for [finite_e_lambda_map]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Supporting lemma for this passage;
    not separately stated in the book. *)
Lemma finite_e_lambda_map m (t : Lambda n m) :
  exterior_power_map basis_from_coordinates m (coordinate_e_lambda K t) = finite_e_lambda t.
Proof.
apply: val_inj; change (exterior_algebra_map basis_from_coordinates
  (exterior_word [seq c i | i <- val t]) = exterior_word [seq e i | i <- val t]).
rewrite exterior_algebra_map_word -map_comp.
congr 1 (exterior_word _); apply: eq_map => i; exact: basis_from_coordinatesE.
Qed.

Hypothesis h2 : (1 + 1 : K) != 0.
(** Source for [finite_e_lambda_basis]: Federer (1969), 1.3.2, pp. 14-15,
    ordered products of basis vectors and the final dimension display. In
    words: Increasing products of basis vectors form a basis of each
    exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem finite_e_lambda_basis m : is_basis (@finite_e_lambda m).
Proof.
have hb := @basis_transport K (Choice.clone (Lambda n m) _)
  (exterior_power C m) (exterior_power V m) (@coordinate_e_lambda K n m)
  (exterior_power_map basis_from_coordinates m) (exterior_power_map basis_to_coordinates m)
  (exterior_power_mapK (m:=m) basis_from_coordinatesK)
  (exterior_power_mapK (m:=m) basis_to_coordinatesK) (coordinate_e_lambda_basis h2 n m).
exact: basis_congr (@finite_e_lambda_map m) hb.
Qed.

(** Source for [exterior_power_above_dimension]: Federer (1969), 1.3.2, pp.
    14-15, ordered products of basis vectors and the final dimension
    display. In words: Increasing products of basis vectors form a basis of
    each exterior power; for dimension n the m-th power has dimension
    binomial(n,m), and is zero for m>n. Formalises the indicated part of the
    passage under the hypotheses in the statement below. *)
Theorem exterior_power_above_dimension m : (n < m)%N -> forall x : exterior_power V m, x = 0.
Proof.
move=> hnm; apply: (basis_induction (finite_e_lambda_basis m)) => [|x y -> ->|a x ->|t].
- by [].
- by rewrite addr0.
- by rewrite scaler0.
have hs := selected_size (val (Lambda_selection t)).
have hm := eqP (valP (Lambda_selection t)).
by rewrite hm (ltn_geF hnm) in hs.
Qed.
End BasisCoordinates.
