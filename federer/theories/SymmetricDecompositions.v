(** Federer (1969), 1.10.5, p. 48, decompositions in the infimum formula for
    the mass norm. Positive degree is essential: scalar coefficients can
    then be absorbed into the first vector of a product. Degree zero is
    treated separately in SymmetricZeroDegreeDecomposition.v. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear Graded GradedComponents
  SymmetricAlgebra SymmetricGrading SymmetricFormIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Decompositions.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [symmetric_decomposition]: Federer 1.10.5,
    p. 48, the equality constraining the finite decompositions in
    the infimum. The empty sum represents zero. *)
Definition symmetric_decomposition m (x : symmetric_power V m)
    (s : seq (m.-tuple V)) : Prop :=
  x = \sum_(t <- s) symmetric_tuple_component t.

(** Source for [symmetric_scale_first_tuple]: Federer 1.10.5,
    p. 48, supporting absorption of a scalar coefficient into
    the first factor of a positive-degree product. *)
Definition symmetric_scale_first_tuple m (c : K) (t : m.+1.-tuple V) : m.+1.-tuple V :=
  [tuple of (c *: thead t) :: behead t].

(** Source for [symmetric_scale_first_word]: Federer 1.10.5,
    p. 48, supporting scalar absorption: scaling the first vector
    scales the resulting symmetric word. *)
Lemma symmetric_scale_first_word m c (t : m.+1.-tuple V) :
  symmetric_word (symmetric_scale_first_tuple c t) = c *: symmetric_word t.
Proof.
rewrite /symmetric_scale_first_tuple /= symmetric_word_cons linearZ
  (bilZl (symmetric_product_bilinear V)).
by rewrite [t in RHS](tuple_eta t) /= symmetric_word_cons.
Qed.

(** Source for [symmetric_scale_first_component]: Federer 1.10.5,
    p. 48, scalar absorption expressed inside the positive-degree
    symmetric power itself. *)
Lemma symmetric_scale_first_component m c (t : m.+1.-tuple V) :
  symmetric_tuple_component (symmetric_scale_first_tuple c t) =
    c *: symmetric_tuple_component t.
Proof.
apply: val_inj.
change (component_val (symmetric_tuple_component (symmetric_scale_first_tuple c t)) =
  component_val (c *: symmetric_tuple_component t)).
rewrite linearZ !symmetric_tuple_componentE symmetric_scale_first_word.
change (c *: symmetric_word t = c *: component_val (symmetric_tuple_component t)).
by rewrite symmetric_tuple_componentE.
Qed.

(** Source for [symmetric_word_decomposition_exists]: Federer 1.10.5,
    p. 48, supporting existence of the finite sums in the infimum.
    Homogeneous word spanning and scalar absorption give an unweighted
    sum of positive-degree products for every homogeneous vector. *)
Lemma symmetric_word_decomposition_exists m (x : symmetric_space V) :
  homogeneous (symmetric_grading V) m.+1 x ->
  exists s : seq (m.+1.-tuple V), x = \sum_(t <- s) symmetric_word t.
Proof.
apply: (@symmetric_component_induction K V m.+1
  (fun x => exists s : seq (m.+1.-tuple V), x = \sum_(t <- s) symmetric_word t)).
- exists [::]; by rewrite big_nil.
- move=> u v [s ->] [t ->]; exists (s++t); by rewrite big_cat.
- move=> c u [s ->]; exists [seq symmetric_scale_first_tuple c t | t <- s].
  rewrite big_map scaler_sumr; apply: eq_bigr=> t _.
  exact: esym (symmetric_scale_first_word c t).
- move=> s hs; exists [:: @Tuple m.+1 V s (introT eqP hs)].
  by rewrite big_cons big_nil addr0.
Qed.

(** Source for [symmetric_decomposition_exists]: Federer 1.10.5,
    p. 48, every vector of a positive-degree symmetric power
    has a finite decomposition into products of vectors. No basis,
    finite-dimensionality, norm, or characteristic hypothesis is needed. *)
Theorem symmetric_decomposition_exists m (hm : (0<m)%N) (x : symmetric_power V m) :
  exists s, symmetric_decomposition x s.
Proof.
case: m hm x=> [|m] hm x //.
have [s hs] := @symmetric_word_decomposition_exists m (component_val x) (component_homogeneous x).
exists s; apply: val_inj.
change (component_val x = component_val (\sum_(t <- s) symmetric_tuple_component t)).
rewrite linear_sum.
change (component_val x = \sum_(t <- s) component_val (symmetric_tuple_component t)).
under eq_bigr do rewrite symmetric_tuple_componentE.
exact hs.
Qed.
(** Source for [symmetric_decomposition_zero]: Federer 1.10.5,
    p. 48, the empty sum is a decomposition of zero. *)
Lemma symmetric_decomposition_zero m :
  symmetric_decomposition (0 : symmetric_power V m) [::].
Proof. by rewrite /symmetric_decomposition big_nil. Qed.

(** Source for [symmetric_decomposition_add]: Federer 1.10.5,
    p. 48, concatenating decompositions represents the sum of the vectors. *)
Lemma symmetric_decomposition_add m (x y : symmetric_power V m) s t :
  symmetric_decomposition x s -> symmetric_decomposition y t ->
  symmetric_decomposition (x+y) (s++t).
Proof. rewrite /symmetric_decomposition=> -> ->; by rewrite big_cat. Qed.

(** Source for [symmetric_decomposition_scale]: Federer 1.10.5,
    p. 48, absorbing a scalar into the first factor of every
    summand gives a decomposition of the scaled positive-degree vector. *)
Lemma symmetric_decomposition_scale m c (x : symmetric_power V m.+1) s :
  symmetric_decomposition x s ->
  symmetric_decomposition (c *: x) [seq symmetric_scale_first_tuple c t | t <- s].
Proof.
rewrite /symmetric_decomposition=> ->; rewrite scaler_sumr big_map.
apply: eq_bigr=> t _; exact: esym (symmetric_scale_first_component c t).
Qed.
End Decompositions.
