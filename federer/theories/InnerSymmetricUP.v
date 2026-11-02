(** Federer (1969), 1.10.5, p. 47, first paragraph: extend the polarity to a
    unit-preserving graded algebra map. The specification is independent of
    a construction. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerSymmetricPolarity AlgebraUP
  SymmetricUP SymmetricAlgebra SymmetricGrading GradedAlgebra SymmetricForms
  SymmetricFormSum SymmetricFormProduct SymmetricFormUnit ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [is_inner_symmetric_extension]: Federer
    1.10.5, p. 47, gamma is the unit-preserving
    graded algebra map extending the given polarity. The algebra
    homomorphism laws are carried by its type. *)
Record is_inner_symmetric_extension (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (gamma : algebra_map (symmetric_algebra V)
      (symmetric_forms_unital_algebra V (scalar_algebra R))) : Prop := {
  inner_symmetric_extension_generator : forall v,
    gamma (symmetric_generator v) = sform_include (inner_symmetric_polarity hB v);
  inner_symmetric_extension_graded : preserves_grading
    (symmetric_grading V) (S_star_grading V R^o) gamma
}.

(** Source for [inner_symmetric_extension_unique]: Federer
    1.10.5, p. 47, the extension is uniquely
    determined by the polarity, by the universal property of 1.9.1. *)
Theorem inner_symmetric_extension_unique (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (g h : algebra_map (symmetric_algebra V)
      (symmetric_forms_unital_algebra V (scalar_algebra R))) :
  is_inner_symmetric_extension hB g -> is_inner_symmetric_extension hB h -> g =1 h.
Proof.
move=> hg hh.
have hc : commutative (alg_mul (symmetric_forms_unital_algebra V (scalar_algebra R))).
  exact: (@symmetric_forms_product_commutative R V R^o
    (fun x y : R => x*y) (scalar_bilinear R) (@mulrC R)).
apply: (symmetric_algebra_ext (@symmetric_algebra_exists R V) hc).
move=> v; by rewrite (inner_symmetric_extension_generator hg)
  (inner_symmetric_extension_generator hh).
Qed.
