(** Federer (1969), 1.7.5, p. 32: supporting transport of wedge estimates
    along finite-dimensional inclusions and interchange of the factors. The
    algebra identities are consequences of 1.3.1. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerExterior InnerExteriorPositivity
  InnerExteriorNaturality ExteriorNorm OrthogonalMaps ExteriorGrading
  ExteriorAlgebra ExteriorMaps ExteriorHomogeneousProducts ExteriorAnticommutativity
  AlgebraUP GradedComponents GradedAlgebra FiniteExteriorPowers
  SimpleElementary AssociatedSubspace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_power_map_product]: Federer 1.7.5,
    p. 32, supporting finite-dimensional reduction: induced exterior
    maps preserve homogeneous products, as specified in 1.3.1. *)
Lemma exterior_power_map_product (R : fieldType) (V U : lmodType R)
    (f : {linear V -> U}) p q (x : exterior_power V p) (y : exterior_power V q) :
  exterior_power_map f (p+q) (exterior_product x y) =
    exterior_product (exterior_power_map f p x) (exterior_power_map f q y).
Proof.
apply: val_inj; change (exterior_algebra_map f (wedge (component_val x) (component_val y)) =
  wedge (exterior_algebra_map f (component_val x)) (exterior_algebra_map f (component_val y))).
exact: algebra_map_mul.
Qed.

(** Source for [exterior_power_map_simple]: Federer 1.7.5,
    p. 32, supporting transport of simple factors: an induced
    exterior map sends a product to the product of the images. *)
Lemma exterior_power_map_simple (R : fieldType) (V U : lmodType R)
    (f : {linear V -> U}) m (x : exterior_power V m) :
  simple x -> simple (exterior_power_map f m x).
Proof.
move=> [t ->]; exists (map_tuple f t); apply: val_inj.
change (exterior_algebra_map f (component_val (e_lambda idfun t)) =
  component_val (e_lambda idfun (map_tuple f t))).
by rewrite !e_lambdaE !map_id exterior_algebra_map_word.
Qed.

(** Source for [exterior_norm_orthogonal_natural]: Federer
    1.7.5, p. 32, supporting isometric reduction: an orthogonal
    map preserves the induced norms on all exterior powers. *)
Lemma exterior_norm_orthogonal_natural (R : rcfType)
    (h2 : (1+1 : R) != 0) (V U : lmodType R)
    (B : V -> V -> R) (C : U -> U -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    (f : {linear V -> U}) (hf : is_orthogonal_map B C f)
    m (x : exterior_power V m) :
  exterior_norm h2 hC (exterior_power_map f m x) = exterior_norm h2 hB x.
Proof.
apply: inner_norm_value; first exact: exterior_norm_nonnegative.
by rewrite exterior_norm_square (exterior_inner_orthogonal_natural h2 hB hC hf).
Qed.

(** Source for [exterior_norm_reindex]: Federer 1.7.5,
    p. 32, supporting transport across equal degree indices;
    this changes no vector or norm. *)
Lemma exterior_norm_reindex (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    m n (h : m=n) (x : exterior_power V m) :
  exterior_norm h2 hB (exterior_reindex h x) = exterior_norm h2 hB x.
Proof. by case: n / h. Qed.

(** Source for [exterior_product_norm_swap]: Federer 1.7.5,
    p. 32, either factor may be simple: interchanging factors
    changes only the sign from 1.3.1 and preserves the norm. *)
Lemma exterior_product_norm_swap (R : rcfType)
    (h2 : (1+1 : R) != 0) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    p q (x : exterior_power V p) (y : exterior_power V q) :
  exterior_norm h2 hB (exterior_product x y) = exterior_norm h2 hB (exterior_product y x).
Proof.
have he : exterior_reindex (addnC q p) (exterior_product y x) =
    (-1 : R)^+(p*q) *: exterior_product x y.
  apply: val_inj.
  change (component_val (exterior_reindex (addnC q p) (exterior_product y x)) =
    component_val ((-1 : R)^+(p*q) *: exterior_product x y)).
  rewrite exterior_reindexE linearZ !exterior_productE.
  rewrite mulnC.
  exact (@exterior_anticommutative R V q p (component_val y) (component_val x)
    (component_homogeneous y) (component_homogeneous x)).
have hh := congr1 (@exterior_norm R h2 V B hB (p+q)) he.
rewrite exterior_norm_reindex exterior_norm_scale normrX normrN normr1 expr1n mul1r in hh.
exact: esym hh.
Qed.
