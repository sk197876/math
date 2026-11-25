(** Left translations used in the extra rotation average of Federer (1969),
    2.10.16, p. 178. The normalized Haar measure of 2.7.16(6), p. 139, is
    invariant on all sets by 2.7.1–2.7.2, pp. 121–122. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import TopologicalGroupUP TopologicalGroupLaws HaarIntegralUP HaarIntegralLaws
  GroupMultiplicationHomogeneous InvariantMeasureTranslates MeasureUP MeasurePushforward MeasureBijectionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [left_haar_translation_bijection]: supporting
    measure-preserving rotation of each normal frame in
    2.10.16, p. 178. Package left Haar invariance
    with the actual inverse translation from 2.7.2, p. 122. *)
Lemma left_haar_translation_bijection (R : realType) (G : topologicalType)
    (mul : G -> G -> G) (inv : G -> G) (e : G)
    (hT : is_topological_group mul inv e) (theta : set G -> \bar R) :
  is_left_haar_measure mul theta -> forall g,
  is_measure_bijection theta theta (mul g) (mul (inv g)).
Proof.
move=> ht g.
have hG := topological_group_laws hT.
constructor.
- by move=> x; rewrite (group_mulA hG) (group_mulVg hG) (group_mul1g hG).
- by move=> x; rewrite (group_mulA hG) (group_mulgV hG) (group_mul1g hG).
- apply/funext=> A.
  exact (@invariant_measure_preimage R G G mul inv e (left_multiplication_action mul) hG
    (left_multiplication_homogeneous hT) theta (nonzero_invariant_measure_invariant ht) g A).
Qed.
