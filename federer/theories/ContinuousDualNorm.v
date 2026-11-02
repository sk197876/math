(** Federer (1969), 2.4.12, p. 87: the dual supremum defines a norm. All
    arguments below use the abstract evaluation and least-bound laws. Source
    context and expanded context: ContinuousDualUP.v. No finite-dimensional
    hypothesis is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP RealFunctionalNormUP ContinuousDualUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section NormLaws.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Variable D : lmodType R.
Variable evaluation : Hom D (Hom V R^o).
Variable DN : D -> R.
Hypothesis hD : is_continuous_dual hN evaluation DN.

(** Source for [continuous_dual_scale_bound]: supporting
    homogeneity estimate for the dual norm, Federer 2.4.12, p. 87. *)
Lemma continuous_dual_scale_bound c d : DN (c *: d) <= `|c|*DN d.
Proof.
apply: (real_functional_norm_least (continuous_dual_norm_laws hD (c *: d))).
- exact: mulr_ge0 (normr_ge0 c) (real_functional_norm_nonnegative (continuous_dual_norm_laws hD d)).
- move=> y; rewrite hom_as_linearE linearZ.
  change (`|c * evaluation d y| <= (`|c|*DN d)*N y).
  rewrite normrM -mulrA.
  exact: (ler_wpM2l (normr_ge0 c) (real_functional_norm_bound (continuous_dual_norm_laws hD d) y)).
Qed.

(** Source for [continuous_dual_norm_is_norm]: the dual norm
    assertion in Federer 2.4.12, p. 87, including the zero space. *)
Theorem continuous_dual_norm_is_norm : is_real_norm DN.
Proof.
have hn d := real_functional_norm_nonnegative (continuous_dual_norm_laws hD d).
have hz : DN 0 = 0.
  apply/eqP; rewrite eq_le hn andbT.
  apply: (real_functional_norm_least (continuous_dual_norm_laws hD 0) (lexx _)).
  move=> y; rewrite hom_as_linearE linear0.
  by change (`|(0:R)| <= 0*N y); rewrite normr0 mul0r.
split.
- split; first exact hn.
  + move=> c d; have [->|hc] := eqVneq c 0.
    * by rewrite scale0r hz normr0 mul0r.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact: continuous_dual_scale_bound.
    have hh := continuous_dual_scale_bound c^-1 (c *: d).
    rewrite scalerA mulVf // scale1r normfV mulrC in hh.
    have hp : 0 < `|c| by rewrite normr_gt0.
    by rewrite ler_pdivlMr // mulrC in hh.
  + move=> d e; apply: (real_functional_norm_least (continuous_dual_norm_laws hD (d+e))).
    * exact: addr_ge0 (hn d) (hn e).
    * move=> y; rewrite hom_as_linearE linearD.
      change (`|evaluation d y + evaluation e y| <= (DN d+DN e)*N y).
      rewrite mulrDl.
      apply: le_trans (ler_normD _ _) _.
      exact: lerD (real_functional_norm_bound (continuous_dual_norm_laws hD d) y)
        (real_functional_norm_bound (continuous_dual_norm_laws hD e) y).
- move=> d hd; apply: (continuous_dual_injective hD).
  apply: hom_ext=> y; rewrite linear0.
  change (evaluation d y = 0).
  have hh := real_functional_norm_bound (continuous_dual_norm_laws hD d) y.
  rewrite hd mul0r in hh.
  have hzabs : `|hom_as_linear (evaluation d) y| = 0.
    apply/eqP; by rewrite eq_le hh normr_ge0.
  by move/eqP: hzabs; rewrite normr_eq0=> /eqP.
Qed.
End NormLaws.
