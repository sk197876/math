(** Federer (1969), 2.4.19, p. 91: the finite-image case of Jensen's
    inequality follows from convexity. This supporting algebraic lemma
    removes the zero-in-the-set premise from the finite-combination result
    proved for 1.8.1, p. 38. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import InnerConvex ConvexFiniteCombinations.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [convex_translate_to_origin]: supporting translation of the
    convex set in the finite-image case of Federer 2.4.19, p. 91 *)
Lemma convex_translate_to_origin (R : realFieldType) (V : lmodType R)
    (C : set V) (z : V) :
  is_inner_convex C -> is_inner_convex [set x | C (x+z)].
Proof.
move=> hC x y hx hy t ht ht1.
have h := hC _ _ hx hy t ht ht1.
have he : (1-t) *: (x+z)+t *: (y+z)=(1-t) *: x+t *: y+z.
  rewrite !scalerDr addrACA -scalerDl subrK scale1r; by [].
by rewrite he in h.
Qed.

(** Source for [convex_weighted_sum]: supporting closure under finite convex
    combinations for the finite-image case of Federer 2.4.19, p. 91 No
    zero-membership assumption is added to the convex set. *)
Theorem convex_weighted_sum (R : realFieldType) (V : lmodType R)
    (C : set V) (z : V) n (u : 'I_n -> V) (a : 'I_n -> R) :
  is_inner_convex C -> C z -> (forall i, C (u i)) ->
  (forall i, 0 <= a i) -> \sum_i a i= 1 -> C (\sum_i a i *: u i).
Proof.
move=> hC hz hu ha hs.
pose D := [set x | C (x+z)].
have hD : is_inner_convex D := @convex_translate_to_origin R V C z hC.
have h0 : D 0 by rewrite /D /= add0r.
have hv i : D (u i-z) by rewrite /D /= subrK.
have hsum : \sum_i a i <= 1 by rewrite hs.
have hh := @convex_subconvex_sum R V D hD h0 n (fun i => u i-z) a hv ha hsum.
change (C ((\sum_i a i *: (u i-z))+z)) in hh.
have he : \sum_i a i *: (u i-z)=(\sum_i a i *: u i)-z.
  rewrite (eq_bigr (fun i => a i *: u i-a i *: z)); last by move=> i _; rewrite scalerBr.
  by rewrite sumrB -scaler_suml hs scale1r.
by rewrite he subrK in hh.
Qed.
