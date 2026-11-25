(** Federer (1969), 1.10.5, p. 47, existence of the graded algebra extension
    of the polarity. This private existence proof uses the abstract
    universal property, with no chosen basis. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Hom BoundedHom TensorUP InnerProductUP InnerSymmetricPolarity InnerSymmetricUP
  AlgebraUP SymmetricAlgebra SymmetricGrading SymmetricMaps GradedAlgebra
  SymmetricForms SymmetricFormSum SymmetricFormProduct SymmetricFormUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [inner_symmetric_generator_map]: Federer 1.10.5,
    p. 47, supporting degree-one map for the extension of the polarity.
    Include the symmetric one-form in the full symmetric-form algebra. *)
Definition inner_symmetric_generator_map (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (v : V) : S_star V R^o :=
  sform_include (inner_symmetric_polarity hB v).

(** Source for [inner_symmetric_generator_map_linear]: Federer 1.10.5,
    p. 47, the polarity is linear, and so is its inclusion in the
    graded algebra; this is the input to the universal property of 1.9.1. *)
Lemma inner_symmetric_generator_map_linear (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  linear (inner_symmetric_generator_map hB).
Proof. move=> a x y; by rewrite /inner_symmetric_generator_map !linearP. Qed.
HB.instance Definition _ (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :=
  GRing.isLinear.Build R V (S_star V R^o) *:%R
    (inner_symmetric_generator_map hB) (inner_symmetric_generator_map_linear hB).

(** Source for [inner_symmetric_extension_exists]: Federer 1.10.5, p. 47,
    the polarity extends to a graded unital algebra map. This applies 1.9.1
    and 1.10.2. *)
Theorem inner_symmetric_extension_exists (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) :
  exists gamma : algebra_map (symmetric_algebra V)
    (symmetric_forms_unital_algebra V (scalar_algebra R)), is_inner_symmetric_extension hB gamma.
Proof.
pose A := symmetric_forms_unital_algebra V (scalar_algebra R).
pose G := S_star_grading V R^o.
have hc : commutative (alg_mul A).
  exact: (@symmetric_forms_product_commutative R V R^o
    (fun x y : R => x*y) (scalar_bilinear R) (@mulrC R)).
have hm : graded_product G (alg_mul A).
  exact: symmetric_forms_product_graded.
pose f : {linear V -> A} := GRing.Linear.clone _ _ _ _ (inner_symmetric_generator_map hB) _.
have hf : forall v, homogeneous G 1 (f v).
  move=> v; exact: sform_include_homogeneous.
have [g [hg [hgr hu]]] := @graded_symmetric_algebra_universal R V A G hm hc f hf.
exists g; constructor=> //.
Qed.
