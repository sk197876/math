(** Federer (1969), 3.1.11, p. 219: norm
    laws for the abstract space of continuous multilinear maps.
    All results below use only its evaluation and least-bound
    specification, not its construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section NormLaws.
Variable R : realType.
Variable k : nat.
Variables X Y Z : lmodType R.
Variables NX : X->R.
Variable NY : Y->R.
Hypothesis hNY : is_real_norm NY.
Variable evaluation : {ffun 'I_k->X}->Hom Z Y.
Variable ZN : Z->R.
Hypothesis hZ : is_continuous_multilinear_space NX NY evaluation ZN.

(** Source for [continuous_multilinear_scale_bound]:
    homogeneous norm estimate from the corrected supremum
    in Federer 3.1.11, p. 219, erratum p. 4,
    book p. 219 line 4. *)
Lemma continuous_multilinear_scale_bound c z : ZN (c*:z)<=`|c|*ZN z.
Proof.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ (c*:z))).
- exact: mulr_ge0 (normr_ge0 c)
    (multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z)).
- move=> u; rewrite linearZ /= (real_seminorm_scale hNY.1) -mulrA.
  apply: ler_wpM2l; first exact: normr_ge0.
  exact: multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u.
Qed.

(** Source for [continuous_multilinear_norm_is_norm]: the
    claim that the continuous multilinear-map space is normed
    in Federer 3.1.11, p. 219. The proof
    includes zero arguments and zero source or target spaces. *)
Theorem continuous_multilinear_norm_is_norm : is_real_norm ZN.
Proof.
have hn z := multilinear_operator_nonnegative (continuous_multilinear_norm_laws hZ z).
have hz : ZN 0= 0.
  apply/eqP; rewrite eq_le hn andbT.
  apply: (multilinear_operator_least (continuous_multilinear_norm_laws hZ 0) (lexx _)).
  by move=> u; rewrite linear0 (real_seminorm_zero hNY.1) mul0r.
split.
- constructor; first exact hn.
  + move=> c z; case: (eqVneq c 0)=> [->|hc].
    * by rewrite scale0r hz normr0 mul0r.
    apply/eqP; rewrite eq_le; apply/andP; split; first exact: continuous_multilinear_scale_bound.
    have hb := continuous_multilinear_scale_bound c^-1 (c*:z).
    rewrite scalerA mulVf // scale1r normfV mulrC in hb.
    have hp : 0<`|c| by rewrite normr_gt0.
    by rewrite ler_pdivlMr // mulrC in hb.
  + move=> z w; apply: (multilinear_operator_least
      (continuous_multilinear_norm_laws hZ (z+w))).
    * exact: addr_ge0 (hn z) (hn w).
    * move=> u; rewrite linearD /= mulrDl.
      apply: le_trans (real_seminorm_triangle hNY.1 _ _) _.
      exact: lerD
        (multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u)
        (multilinear_operator_bound (continuous_multilinear_norm_laws hZ w) u).
- move=> z hz0; apply: (continuous_multilinear_extensional hZ)=> u.
  rewrite linear0; apply: hNY.2.
  apply/eqP; rewrite eq_le; apply/andP; split.
  + have hb := multilinear_operator_bound (continuous_multilinear_norm_laws hZ z) u.
    by rewrite hz0 mul0r in hb.
  + exact: real_seminorm_nonnegative hNY.1 _.
Qed.
End NormLaws.
