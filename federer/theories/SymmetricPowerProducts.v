(** Federer (1969), 1.9.1, p. 41: multiplication adds the degrees of
    symmetric powers. The component types and degree transports below
    express this grading explicitly. Arbitrary fields are allowed. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear AlgebraUP GradedAlgebra GradedComponents
  SymmetricAlgebra SymmetricGrading SymmetricMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Products.
Variable K : fieldType.
Variable V : lmodType K.

(** Source for [symmetric_power_product]: Federer 1.9.1, p. 41, the
    homogeneous decomposition and multiplication paragraphs. Supporting
    definition or lemma, in words: The product of a degree-p element and a
    degree-q element lies in degree p+q. *)
Definition symmetric_power_product p q (xi : symmetric_power V p) (eta : symmetric_power V q) : symmetric_power V (p+q) :=
  @Component K (symmetric_space V) (symmetric_grading V) (p+q)
    (symmetric_product (component_val xi) (component_val eta))
    (introT eqP (symmetric_product_graded (component_homogeneous xi) (component_homogeneous eta))).

(** Source for [symmetric_power_productE]: Federer 1.9.1, p. 41, the
    homogeneous decomposition and multiplication paragraphs. Supporting
    definition or lemma, in words: The homogeneous product agrees with
    multiplication in the full algebra. *)
Lemma symmetric_power_productE p q (xi : symmetric_power V p) (eta : symmetric_power V q) :
  component_val (symmetric_power_product xi eta) = symmetric_product (component_val xi) (component_val eta).
Proof. by []. Qed.

(** Source for [symmetric_power_product_bilinear]: Federer 1.9.1, p. 41, the
    homogeneous decomposition and multiplication paragraphs. Supporting
    definition or lemma, in words: Multiplication of homogeneous symmetric
    powers is bilinear. *)
Lemma symmetric_power_product_bilinear p q : bilinear (@symmetric_power_product p q).
Proof.
split.
- move=> eta c xi zeta; apply: val_inj.
  change (symmetric_product (component_val (c *: xi+zeta)) (component_val eta) =
    component_val (c *: symmetric_power_product xi eta + symmetric_power_product zeta eta)).
  by rewrite !linearP ?symmetric_power_productE ?(proj1 (symmetric_product_bilinear V)).
- move=> xi c eta zeta; apply: val_inj.
  change (symmetric_product (component_val xi) (component_val (c *: eta+zeta)) =
    component_val (c *: symmetric_power_product xi eta + symmetric_power_product xi zeta)).
  by rewrite !linearP ?symmetric_power_productE ?(proj2 (symmetric_product_bilinear V)).
Qed.

(** Source for [symmetric_reindex]: Federer 1.9.1, p. 41, the homogeneous
    decomposition and multiplication paragraphs. Supporting definition or
    lemma, in words: Transport a homogeneous element across an equality of
    degree indices. *)
Definition symmetric_reindex m n (h : m=n) (xi : symmetric_power V m) : symmetric_power V n :=
  match h in _ = n return symmetric_power V n with erefl => xi end.

(** Source for [symmetric_reindexE]: Federer 1.9.1, p. 41, the homogeneous
    decomposition and multiplication paragraphs. Supporting definition or
    lemma, in words: Degree transport does not change the underlying algebra
    element. *)
Lemma symmetric_reindexE m n (h : m=n) (xi : symmetric_power V m) :
  component_val (symmetric_reindex h xi) = component_val xi.
Proof. by case: n / h. Qed.

(** Source for [symmetric_reindex_linear]: Federer 1.9.1, p. 41, the
    homogeneous decomposition and multiplication paragraphs. Supporting
    definition or lemma, in words: Degree transport is linear. *)
Lemma symmetric_reindex_linear m n (h : m=n) : linear (@symmetric_reindex m n h).
Proof. by case: n / h => c x y. Qed.
HB.instance Definition _ m n (h : m=n) := GRing.isLinear.Build K (symmetric_power V m)
  (symmetric_power V n) *:%R (symmetric_reindex h) (symmetric_reindex_linear h).
End Products.

(** Source for [symmetric_power_product_commute]: Federer 1.9.1,
    p. 41, symmetric multiplication is commutative. The equality
    p+q=q+p identifies the two homogeneous target spaces. *)
Lemma symmetric_power_product_commute (K : fieldType) (V : lmodType K)
    p q (x : symmetric_power V p) (y : symmetric_power V q) :
  symmetric_reindex (addnC p q) (symmetric_power_product x y) =
    symmetric_power_product y x.
Proof.
apply: val_inj.
change (component_val (symmetric_reindex (addnC p q) (symmetric_power_product x y)) =
  component_val (symmetric_power_product y x)).
rewrite symmetric_reindexE !symmetric_power_productE.
exact: symmetric_product_commute.
Qed.

(** Source for [symmetric_power_product_naturality]: Federer 1.9.1, p. 42,
    induced symmetric maps are algebra homomorphisms and split into
    homogeneous maps. Hence they preserve each homogeneous product. *)
Lemma symmetric_power_product_naturality (K : fieldType) (V W : lmodType K)
    (f : {linear V -> W}) p q (x : symmetric_power V p) (y : symmetric_power V q) :
  symmetric_power_map f (p+q) (symmetric_power_product x y) =
    symmetric_power_product (symmetric_power_map f p x) (symmetric_power_map f q y).
Proof.
apply: val_inj.
change (symmetric_algebra_map f (symmetric_product (component_val x) (component_val y)) =
  symmetric_product (symmetric_algebra_map f (component_val x))
    (symmetric_algebra_map f (component_val y))).
exact: algebra_map_mul.
Qed.
