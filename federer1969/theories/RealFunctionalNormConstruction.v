(** Private existence proof for the dual norm of Federer (1969), 2.4.12, p.
    87. The supremum construction is hidden behind the least-bound
    specification. Source context and expanded context:
    RealFunctionalNormUP.v. The unit ball includes zero, also in dimension
    zero; continuity supplies a finite upper bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP ContinuousRealFunctional
  ContinuousRealFunctionalBound RealFunctionalNormUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_functional_norm_exists]: existence of the finite dual
    norm in Federer 2.4.12, p. 87 *)
Theorem real_functional_norm_exists (R : realType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N) (a : {linear V -> R^o}) :
  is_continuous_real_functional hN a ->
  exists n : R, is_real_functional_norm N a n.
Proof.
move=> ha; have [C [hC hbound]] := continuous_real_functional_bound ha.
pose S := [set r : R | exists y : V, N y <= 1 /\ r = `|a y|].
have hs0 : S 0.
  exists 0; split; first by rewrite (real_seminorm_zero hN.1).
  by rewrite linear0 normr0.
have hs : S !=set0 by exists 0.
have hCbound : ubound S C.
  move=> r [y [hy ->]]; apply: le_trans (hbound y) _.
  by rewrite -[X in _ <= X]mulr1 ler_pM2l.
have hbounded : has_ubound S by exists C.
have hn : 0 <= sup S := ub_le_sup hbounded hs0.
have hb y : `|a y| <= sup S * N y.
  have [->|hy] := eqVneq y 0.
  - by rewrite linear0 normr0 (real_seminorm_zero hN.1) mulr0.
  have hp : 0 < N y by rewrite (real_norm_positive hN.1 hN.2).
  have hunit : N ((N y)^-1 *: y) <= 1.
    by rewrite (real_seminorm_scale hN.1) normfV (ger0_norm (ltW hp)) mulVf ?gt_eqF.
  have hh : `|a ((N y)^-1 *: y)| <= sup S.
    apply: (ub_le_sup hbounded); exists ((N y)^-1 *: y); by split.
  rewrite linearZ /= normrM normfV (ger0_norm (ltW hp)) mulrC in hh.
  by rewrite ler_pdivrMr // in hh.
exists (sup S); split=> // D hD hd.
apply: (ge_sup hs) => r [y [hy ->]].
apply: le_trans (hd y) _.
have hh := ler_wpM2l hD hy.
by rewrite mulr1 in hh.
Qed.
