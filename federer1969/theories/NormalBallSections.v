(** Inner-product ball sections supporting Federer (1969), 2.10.30, p. 195.
    Pythagoras identifies the centred scalar radius on a normal line,
    including tangent lines with radius zero. All balls here are closed, as
    in the bold B in the printed containing-ball assertion. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals lra.
From Federer Require Import InnerProductUP InnerNorm OrthonormalFamilies UnitNormalGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section BallSections.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable u : V.
Hypothesis hu : B u u= 1.
Local Notation N := (inner_norm hB).
Local Notation c := (inner_coordinate hB u).

(** Source for [normal_line_base_norm_bound]: supporting
    projection into the containing ball in 2.10.30,
    p. 195. A point on the normal line
    bounds the norm of its hyperplane foot. *)
Lemma normal_line_base_norm_bound y t r :
  c y=0 -> 0<=r -> N (y+t*:u)<=r -> N y<=r.
Proof.
move=> hy hr ht.
have hh : N (y+t*:u)^+2<=r^+2.
  rewrite (ler_sqr _ _) //; by rewrite nnegrE ?inner_norm_nonnegative.
rewrite (@normal_line_norm_square R V B hB u hu y t hy) in hh.
have ht0 := sqr_ge0 t.
rewrite -(ler_sqr _ _) //; first by lra.
by rewrite nnegrE ?inner_norm_nonnegative.
Qed.

(** Source for [normal_line_closed_ball_section]: supporting
    centred closed-segment description of a ball section
    in 2.10.30, p. 195. Tangent sections
    remain a singleton instead of being discarded. *)
Theorem normal_line_closed_ball_section y r t :
  c y=0 -> 0<=r -> N y<=r ->
  (N (y+t*:u)<=r <-> `|t|<=Num.sqrt (r^+2-N y^+2)).
Proof.
move=> hy hr hyr.
have hd : 0<=r^+2-N y^+2.
  rewrite subr_ge0 (ler_sqr _ _) //; by rewrite nnegrE ?inner_norm_nonnegative.
have htsq : `|t|^+2=t^+2 by rewrite -normrX ger0_norm ?sqr_ge0.
have hs := @normal_line_norm_square R V B hB u hu y t hy.
split=> ht.
- have hh : N (y+t*:u)^+2<=r^+2.
    rewrite (ler_sqr _ _) //; by rewrite nnegrE ?inner_norm_nonnegative.
  rewrite -(ler_sqr _ _) ?nnegrE ?normr_ge0 ?sqrtr_ge0 // htsq sqr_sqrtr //.
  rewrite hs in hh; lra.
- have hh : t^+2<=r^+2-N y^+2.
    rewrite -htsq -(sqr_sqrtr hd) (ler_sqr _ _) //; by rewrite nnegrE ?normr_ge0 ?sqrtr_ge0.
  rewrite -(ler_sqr _ _) ?nnegrE ?inner_norm_nonnegative // hs; lra.
Qed.
End BallSections.
