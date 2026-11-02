(** Private existence proof for the general operator norm used in
    Federer (1969), 3.1.1, pp. 209–210. Scalar completeness supplies the
    supremum on the closed unit ball, without compactness or attainment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOperatorNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_operator_norm_exists]: existence of the finite
    operator norm for a continuous linear map in Federer 3.1.1,
    pp. 209–210. Its finite bound is equivalent to continuity by the
    proved norm-topology bridge. Source and target may be zero dimensional. *)
Theorem norm_operator_norm_exists (R : realType) (X Y : lmodType R)
    (NX : X -> R) (NY : Y -> R) (hNX : is_real_norm NX)
    (hNY : is_real_norm NY) (L : Hom X Y) :
  norm_bounded_linear NX NY L -> exists n, is_norm_operator_norm NX NY L n.
Proof.
move=> [C [hC hL]].
pose S := [set r : R | exists x : X, NX x <= 1 /\ r = NY (L x)].
have hs0 : S 0.
  exists 0; split; first by rewrite (real_seminorm_zero hNX.1).
  by rewrite linear0 (real_seminorm_zero hNY.1).
have hs : S !=set0 by exists 0.
have hbC : ubound S C.
  move=> r [x [hx ->]]; apply: le_trans (hL x) _.
  have hh := ler_wpM2l hC hx; by rewrite mulr1 in hh.
have hbounded : has_ubound S by exists C.
have hn : 0 <= sup S := ub_le_sup hbounded hs0.
have hb x : NY (L x) <= sup S * NX x.
  have [->|hx] := eqVneq x 0.
    by rewrite linear0 (real_seminorm_zero hNY.1) (real_seminorm_zero hNX.1) mulr0.
  have hp : 0 < NX x by rewrite (real_norm_positive hNX.1 hNX.2).
  have hu : NX ((NX x)^-1 *: x) <= 1.
    by rewrite (real_seminorm_scale hNX.1) normfV (ger0_norm (ltW hp)) mulVf ?gt_eqF.
  have hh : NY (L ((NX x)^-1 *: x)) <= sup S.
    apply: (ub_le_sup hbounded); exists ((NX x)^-1 *: x); by split.
  rewrite linearZ /= (real_seminorm_scale hNY.1)
    normfV (ger0_norm (ltW hp)) mulrC in hh.
  by rewrite ler_pdivrMr // in hh.
exists (sup S); split=> // D hD hd.
apply: (ge_sup hs)=> r [x [hx ->]].
apply: le_trans (hd x) _.
have hh := ler_wpM2l hD hx; by rewrite mulr1 in hh.
Qed.
