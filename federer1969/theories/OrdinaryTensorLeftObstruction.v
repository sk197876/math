(** Federer 1.4.5, p. 20: the missing left-factor obstruction for the
    ordinary product. Reuse the scalar tensor functional and one-form
    evaluation already used for the right-factor obstruction. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import DualExterior OrdinaryTensorObstruction
  IndependentDual PairingSeparation AlgebraTensor CentralTensor TraceBasisProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section LeftObstruction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).

(** Source for [ordinary_tensor_left_pair_not_commutative]: supporting
    sharp exceptional-case assertion for Federer 1.4.5, p. 20. If V has
    two independent vectors, the alternating one-forms dual to them have
    opposite nonzero products. Evaluation on their two-vector word and
    augmentation on the right tensor factor detect the same obstruction
    in the ordinary product. W may be zero or infinite dimensional. *)
Theorem ordinary_tensor_left_pair_not_commutative (e : 'I_2 -> V) :
    finite_independent e -> ~ commutative (alg_mul T).
Proof.
move=> he hc.
pose a := independent_dual he ord0.
pose b := independent_dual he ord_max.
pose detect : {linear T -> K^o} := scalar_tensor_functional
  (GRing.Linear.clone _ _ _ _
    (covector_evaluation (exterior_word [:: e ord0; e ord_max])) _)
  (exterior_augmentation W).
have h := congr1 detect (hc
  (@algebra_tensor_left K U E (one_generator a))
  (@algebra_tensor_left K U E (one_generator b))).
rewrite /algebra_tensor_left !ordinary_tensor_productE /detect
  !scalar_tensor_functionalE in h.
change (alternating_wedge h2 (scalar_bilinear K)
    (one_generator a) (one_generator b)
    (exterior_word [:: e ord0; e ord_max]) *
    exterior_augmentation W (wedge (exterior_unit W) (exterior_unit W)) =
  alternating_wedge h2 (scalar_bilinear K)
    (one_generator b) (one_generator a)
    (exterior_word [:: e ord0; e ord_max]) *
    exterior_augmentation W (wedge (exterior_unit W) (exterior_unit W))) in h.
rewrite wedge_unitl exterior_augmentation_unit !mulr1
  !one_forms_wedge_two /a /b !independent_dualE /=
  !mulr1 !mulr0 subr0 sub0r in h.
have hz : (1+1 : K)=0 by rewrite {1}h addNr.
by move: h2; rewrite hz eqxx.
Qed.
End LeftObstruction.
