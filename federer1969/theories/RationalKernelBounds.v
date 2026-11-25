(** Federer (1969), 2.6.3(2), p. 118: the two displayed absolute-value
    bounds on the rational kernel, for 0<x<=1 and x>1. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring lra.
From Federer Require Import RationalFubiniKernel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [rational_kernel_numerator_bound]: supporting triangle
    estimate for the two bounds of Federer 2.6.3(2), p. 118 Positivity of
    both coordinates is explicit. *)
Lemma rational_kernel_numerator_bound (R : realType) (x y : R) :
  0 <= x -> 0 <= y -> `|4*x*y-x^+2-y^+2| <= 4*x*y+x^+2+y^+2.
Proof.
move=> hx hy; have hxy : 0 <= 4*x*y by rewrite !mulr_ge0.
have hx2 := sqr_ge0 x; have hy2 := sqr_ge0 y.
rewrite ler_norml; apply/andP; split; lra.
Qed.

(** Source for [rational_kernel_small_bound]: the first displayed absolute
    bound in Federer 2.6.3(2), p. 118 The endpoint x=0 is included using the
    prescribed zero value of the piecewise kernel. *)
Lemma rational_kernel_small_bound (R : realType) (x y : R) :
  0 < y -> 0 <= x -> x <= 1 ->
  `|rational_fubini_kernel x y| <= (4*y+1+y^+2)*((y^-1)^+4).
Proof.
move=> hy hx hx1; have hy0 := ltW hy.
have hC : 0 <= 4*y+1+y^+2 by rewrite !addr_ge0 ?mulr_ge0 ?sqr_ge0.
case: (eqVneq x 0)=> [->|hx0].
- rewrite rational_fubini_kernel_nonpositive_left ?lexx // normr0.
  apply: mulr_ge0=> //; by rewrite exprn_ge0 // invr_ge0.
have hxp : 0 < x by rewrite lt_neqAle eq_sym hx0 hx.
have hp : 0 < x+y by rewrite addr_gt0.
have hxy : 4*x*y <= 4*y.
  have hh := ler_wpM2l (mulr_ge0 (ler0n R 4) hy0) hx1.
  have he : 4*y*x=4*x*y by ring.
  by rewrite he mulr1 in hh.
have hx2 : x^+2 <= 1.
  rewrite expr2 -[X in _ <= X]mul1r; exact (ler_pM hx hx hx1 hx1).
have hnum : `|4*x*y-x^+2-y^+2| <= 4*y+1+y^+2.
  apply: le_trans (rational_kernel_numerator_bound hx hy0) _; exact: lerD (lerD hxy hx2) (lexx _).
have hyxy : y <= x+y by lra.
have hpow : y^+4 <= (x+y)^+4 := lerXn2r 4 hy0 (ltW hp) hyxy.
have hinv : ((x+y)^+4)^-1 <= ((y^-1)^+4).
  by rewrite exprVn (@lef_pV2 R _ _ (exprn_gt0 4 hp) (exprn_gt0 4 hy)).
rewrite rational_fubini_kernel_positive // /rational_fubini_density normrM normfV
  (ger0_norm (exprn_ge0 4 (ltW hp))).
have hi0 : 0 <= ((x+y)^+4)^-1 by rewrite invr_ge0; exact (exprn_ge0 4 (ltW hp)).
exact (ler_pM (normr_ge0 _) hi0 hnum hinv).
Qed.

(** Source for [rational_kernel_large_bound]: the second displayed bound in
    Federer 2.6.3(2), p. 118 The stronger boundary convention x>=1 is valid
    and useful for the tail integral. *)
Lemma rational_kernel_large_bound (R : realType) (x y : R) :
  0 < y -> 1 <= x ->
  `|rational_fubini_kernel x y| <= (4*y+1+y^+2)*((x^-1)^+2).
Proof.
move=> hy hx1; have hx : 0 < x := lt_le_trans ltr01 hx1.
have hx0 := ltW hx; have hy0 := ltW hy.
have hp : 0 < x+y by rewrite addr_gt0.
have hxx : x <= x^+2.
  have hh := ler_wpM2l hx0 hx1; by rewrite mulr1 -expr2 in hh.
have hxx1 : 1 <= x^+2 := le_trans hx1 hxx.
have hxy : 4*x*y <= (4*y)*x^+2.
  have hh := ler_wpM2l (mulr_ge0 (ler0n R 4) hy0) hxx.
  have he : 4*y*x=4*x*y by ring.
  by rewrite he in hh.
have hyy : y^+2 <= y^+2*x^+2.
  have hh := ler_wpM2l (sqr_ge0 y) hxx1; by rewrite mulr1 in hh.
have hnum : `|4*x*y-x^+2-y^+2| <= (4*y+1+y^+2)*x^+2.
  apply: le_trans (rational_kernel_numerator_bound hx0 hy0) _.
  have hh := lerD (lerD hxy (lexx (x^+2))) hyy.
  have he : (4*y)*x^+2+x^+2+y^+2*x^+2=(4*y+1+y^+2)*x^+2 by ring.
  by rewrite he in hh.
have hxxy : x <= x+y by lra.
have hpow : x^+4 <= (x+y)^+4 := lerXn2r 4 hx0 (ltW hp) hxxy.
have hinv : ((x+y)^+4)^-1 <= (x^+4)^-1 by rewrite (@lef_pV2 R _ _ (exprn_gt0 4 hp) (exprn_gt0 4 hx)).
have hb : `|4*x*y-x^+2-y^+2|*((x+y)^+4)^-1 <= ((4*y+1+y^+2)*x^+2)*(x^+4)^-1.
  have hi0 : 0 <= ((x+y)^+4)^-1 by rewrite invr_ge0; exact (exprn_ge0 4 (ltW hp)).
exact (ler_pM (normr_ge0 _) hi0 hnum hinv).
rewrite rational_fubini_kernel_positive // /rational_fubini_density normrM normfV
  (ger0_norm (exprn_ge0 4 (ltW hp))).
have he : ((4*y+1+y^+2)*x^+2)*(x^+4)^-1=(4*y+1+y^+2)*((x^-1)^+2).
  by field; rewrite (gt_eqF hx).
by rewrite he in hb.
Qed.
