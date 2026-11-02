(** Federer (1969), 1.7.3, p. 29: the sum of mutually orthogonal invariant
    summands is a direct sum. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ModuleQuotient InnerProductUP InnerProductLaws
  OrthonormalFamilies MinimalInvariantUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_summands_sum_zero]: Federer
    1.7.3, p. 29, supporting directness: if vectors in distinct
    mutually orthogonal summands sum to zero, then each is zero. *)
Theorem orthogonal_summands_sum_zero (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) s (W : 'I_s -> subspace V)
    (ho : forall i j, i != j -> forall x y, W i x -> W j y -> B x y = 0)
    (w : 'I_s -> V) (hw : forall i, W i (w i)) :
  (\sum_i w i) = 0 -> forall i, w i = 0.
Proof.
move=> hs j.
have hh := congr1 (inner_coordinate hB (w j)) hs.
rewrite linear_sum linear0 (bigD1 j) // in hh.
have hz : (\sum_(i | i != j) inner_coordinate hB (w j) (w i)) = 0.
  apply: big1 => i hij; rewrite inner_coordinateE; exact (@ho i j hij (w i) (w j) (hw i) (hw j)).
rewrite hz inner_coordinateE /= addr0 in hh.
apply/eqP; rewrite -(inner_self_eq0 hB) hh eqxx; by [].
Qed.

(** Source for [orthogonal_decomposition_unique]: Federer
    1.7.3, p. 29, the decomposition into its invariant summands
    has unique components, completing the direct-sum assertion. *)
Theorem orthogonal_decomposition_unique (R : realFieldType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (f : {linear V -> V})
    s (W : 'I_s -> subspace V) (hW : is_orthogonal_invariant_decomposition B f W)
    (u v : 'I_s -> V) (hu : forall i, W i (u i)) (hv : forall i, W i (v i)) :
  (\sum_i u i) = \sum_i v i -> u =1 v.
Proof.
move=> hs.
have hw i : W i (u i-v i) := subspace_sub (hu i) (hv i).
have hz : (\sum_i (u i-v i)) = 0 by rewrite sumrB hs subrr.
have hh := @orthogonal_summands_sum_zero R V B hB s W
  (invariant_decomposition_orthogonal hW) (fun i => u i-v i) hw hz.
move=> i; apply/eqP; rewrite -subr_eq0; apply/eqP; exact (hh i).
Qed.
