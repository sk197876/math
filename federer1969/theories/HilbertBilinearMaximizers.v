(** Federer (1969), 1.10.5, p. 48, the Hilbert-input equality attributed to
    [H 1]. This module proves a supporting replacement step: an extremal
    pair of unit vectors for a symmetric bilinear slice can be replaced by
    two copies of its normalized sum. It is a local proof from polarization
    and the parallelogram identity, not a separately numbered assertion in
    Federer. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP Bilinear BilinearNegation InnerProductUP
  InnerProductLaws InnerNorm InnerNormalization InnerParallelogram.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [symmetric_bilinear_polarization_four]: Federer
    1.10.5, p. 48, supporting real quadratic polarization
    identity used in the extremal-pair argument. *)
Lemma symmetric_bilinear_polarization_four (R : fieldType) (V : lmodType R)
    (g : V -> V -> R) (hg : is_symmetric_bilinear g) x y :
  g (x+y) (x+y)-g (x-y) (x-y)=4*g x y.
Proof.
have hd : g (x+y) (x+y) =
  (g x x+g y y)+(g x y+g x y).
  rewrite (bilDl (proj1 hg)) !(bilDr (proj1 hg)) (proj2 hg y x).
  by rewrite !addrA [g x x+g x y+g x y+g y y]addrAC
    [g x x+g x y+g y y]addrAC.
have hs : g (x-y) (x-y) =
  (g x x+g y y)-(g x y+g x y).
  rewrite (bilBl (proj1 hg)) !(bilBr (proj1 hg)) (proj2 hg y x).
  by rewrite opprB opprD !addrA [g x x-g x y+g y y]addrAC.
rewrite hd hs opprB [g x x+g y y+(g x y+g x y)]addrC
  addrACA subrr addr0.
by rewrite -!mulr2n -mulrnA mulr_natl.
Qed.

Section Replacement.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).
Variable g : V -> V -> R.
Hypothesis hg : is_symmetric_bilinear g.
Variable M : R.
Hypothesis hbound : forall u v, `|g u v|<=M*N u*N v.
Variables x y : V.
Hypotheses (hx : N x= 1) (hy : N y= 1) (he : `|g x y|=M).

(** Source for [symmetric_bilinear_maximizer_sum_square]: Federer
    1.10.5, p. 48, supporting extremal-pair identity. If a
    unit pair attains the bilinear norm M, its unnormalized sum has
    diagonal value of absolute size M times its squared length. *)
Lemma symmetric_bilinear_maximizer_sum_square :
  `|g (x+y) (x+y)|=M*N (x+y)^+2.
Proof.
have hp := inner_parallelogram hB x y.
rewrite hx hy !expr1n in hp.
have h4 : (2:R)*(1+1)=4 by rewrite mulrDr !mulr1 -natrD.
rewrite h4 in hp.
have ht := ler_normB (g (x+y) (x+y)) (g (x-y) (x-y)).
rewrite (symmetric_bilinear_polarization_four hg) normrM normr_nat he in ht.
have hd := hbound (x-y) (x-y).
rewrite -mulrA -expr2 in hd.
have hh := le_trans ht (lerD (lexx _) hd).
have hu := hbound (x+y) (x+y).
rewrite -mulrA -expr2 in hu.
apply/eqP; rewrite eq_le hu /=.
rewrite -(lerD2r (M*N (x-y)^+2)) -mulrDr hp.
by rewrite mulrC in hh.
Qed.

(** Source for [symmetric_bilinear_maximizer_normalized_sum]: Federer
    1.10.5, p. 48, supporting replacement of a nonopposite
    extremal unit pair by two copies of the normalized sum. This pair
    is again unit and has the same absolute bilinear value. *)
Theorem symmetric_bilinear_maximizer_normalized_sum : x+y!=0 ->
  N (inner_normalize hB (x+y))= 1 /\
  `|g (inner_normalize hB (x+y)) (inner_normalize hB (x+y))|=M.
Proof.
move=> hs; split; first exact: inner_normalize_norm hs.
rewrite /inner_normalize (bilZl (proj1 hg)) (bilZr (proj1 hg)).
change (`|(N (x+y))^-1*((N (x+y))^-1*g (x+y) (x+y))|=M).
rewrite !normrM !normfV (ger0_norm (inner_norm_nonnegative hB _))
  symmetric_bilinear_maximizer_sum_square.
have hn : N (x+y)!=0 by rewrite inner_norm_eq0.
rewrite !mulrA [(N (x+y))^-1*(N (x+y))^-1*M]mulrC
  -mulrA -(expr2 ((N (x+y))^-1)).
by rewrite -(expr2 (N (x+y))) -mulrA -exprMn mulVf // expr1n mulr1.
Qed.
End Replacement.
