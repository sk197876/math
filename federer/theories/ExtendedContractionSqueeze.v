(** Federer (1969), final sentence of the proof of 2.4.6, p. 84: let the
    positive scalar t approach one from below. We derive it from the earlier
    elementary geometric squeeze using reciprocal scalars. Source context:
    ExtendedLowerLimitUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import ExtendedGeometricSqueeze.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

(** Source for [extended_contraction_squeeze]: supporting final
    inference in Federer 2.4.6, p. 84, with arbitrary
    infinite nonnegative bound and candidate values. *)
Lemma extended_contraction_squeeze (R : realType) (a b : \bar R) :
  0 <= b -> (forall t : R, (0 < t < 1)%R -> t%:E*a <= b) -> a <= b.
Proof.
move=> hb h; apply: (@extended_geometric_squeeze R b a hb)=> t ht.
have ht0 : (0 < t)%R := lt_trans ltr01 ht.
have hti : (0 < t^-1 < 1)%R by rewrite invr_gt0 invf_lt1 // ht0 ht.
have hi := h (t^-1)%R hti; by rewrite lee_pdivrMl // in hi.
Qed.
