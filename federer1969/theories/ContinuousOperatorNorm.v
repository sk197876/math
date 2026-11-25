(** Federer (1969), 3.1.1, pp. 210-211: the least-bound operator
    norm satisfies the norm axioms. The proof uses only the abstract
    operator-space specification, without exposing its carrier. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP NormOperatorNormUP ContinuousOperatorUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section NormLaws.
Variable R : realType.
Variables X Y Z : lmodType R.
Variable NX : X -> R.
Variable NY : Y -> R.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : Hom Z (Hom X Y).
Variable ZN : Z -> R.
Hypothesis hZ : is_continuous_operator_space NX NY evaluation ZN.

(** Source for [continuous_operator_scale_bound]: homogeneous
    upper bound for the operator norm used in 3.1.1, pp. 210-211. *)
Lemma continuous_operator_scale_bound c z : ZN (c *: z) <= `|c|*ZN z.
Proof.
apply: (norm_operator_least (continuous_operator_norm_laws hZ (c *: z))).
- exact: (mulr_ge0 (normr_ge0 c) (norm_operator_nonnegative (continuous_operator_norm_laws hZ z))).
- move=> x; rewrite linearZ /= (real_seminorm_scale hNY.1) -mulrA.
  apply: ler_wpM2l; first exact: normr_ge0.
  exact: (norm_operator_bound (continuous_operator_norm_laws hZ z) x).
Qed.

(** Source for [continuous_operator_norm_is_norm]: the normed
    operator space in 3.1.1, pp. 210-211, including zero-dimensional
    sources or targets. No completeness is required for the norm laws. *)
Theorem continuous_operator_norm_is_norm : is_real_norm ZN.
Proof.
have hn z := norm_operator_nonnegative (continuous_operator_norm_laws hZ z).
have hz : ZN 0=0.
  apply/eqP; rewrite eq_le hn andbT.
  apply: (norm_operator_least (continuous_operator_norm_laws hZ 0) (lexx _)).
  by move=> x; rewrite linear0 hom_zeroE (real_seminorm_zero hNY.1) mul0r.
split.
- constructor; first exact hn.
  + move=> c z; case: (eqVneq c 0)=> [->|hc].
    * by rewrite scale0r hz normr0 mul0r.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact: continuous_operator_scale_bound.
    have hb := continuous_operator_scale_bound c^-1 (c *: z).
    rewrite scalerA mulVf // scale1r normfV mulrC in hb.
    have hp : 0 < `|c| by rewrite normr_gt0.
    by rewrite ler_pdivlMr // mulrC in hb.
  + move=> z w; apply: (norm_operator_least (continuous_operator_norm_laws hZ (z+w))).
    * exact: (addr_ge0 (hn z) (hn w)).
    * move=> x; rewrite linearD /= mulrDl.
      apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
      exact: (lerD (norm_operator_bound (continuous_operator_norm_laws hZ z) x)
        (norm_operator_bound (continuous_operator_norm_laws hZ w) x)).
- move=> z hz0; apply: (continuous_operator_injective hZ).
  apply: hom_ext=> x; rewrite linear0 hom_zeroE.
  apply: hNY.2; apply/eqP; rewrite eq_le; apply/andP; split.
  + have hb := norm_operator_bound (continuous_operator_norm_laws hZ z) x.
    by rewrite hz0 mul0r in hb.
  + exact: real_seminorm_nonnegative hNY.1 _.
Qed.
End NormLaws.
