(** Federer (1969), 1.7.3, p. 29: supporting extension of a quadratic
    maximum on the unit sphere to a homogeneous bound. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InnerProductUP InnerNorm InnerNormalization
  TensorUP Bilinear.
From Federer Require Import BilinearDiagonal.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Rayleigh.
Variable R : rcfType.
Variable V : lmodType R.
Variable B S : V -> V -> R.
Hypothesis hB : is_inner_product B.
Hypothesis hS : @bilinear R V V R^o S.
Local Notation N := (inner_norm hB).

(** Source for [quadratic_unit_bound]: Federer 1.7.3,
    p. 29, supporting homogeneous estimate: if lambda bounds S(x,x)
    on the unit sphere, then S(x,x) <= lambda B(x,x) for every x. *)
Theorem quadratic_unit_bound lambda :
  (forall x, N x = 1 -> S x x <= lambda) ->
  forall x, S x x <= lambda * B x x.
Proof.
move=> hl x; have [->|hx] := eqVneq x 0.
- by rewrite (bil0l hS) (bil0l (inner_bilinear hB)) mulr0.
- have hu := hl (inner_normalize hB x) (inner_normalize_norm hB hx).
  have hs : S x x = (N x)^+2 * S (inner_normalize hB x) (inner_normalize hB x).
    rewrite -bilinear_diagonal_scale // !inner_normalizeK //.
  rewrite hs -(inner_norm_sqr hB x) [lambda * _]mulrC.
  have hm := ler_wpM2l (sqr_ge0 (N x)) hu.
  exact hm.
Qed.
End Rayleigh.
