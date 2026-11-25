(** Federer (1969), 2.4.16, pp. 89–90: measurable sign functions occur in
    the attaining and sign-aligned tests. The sign convention is from 2.1.1,
    p. 51. The proof uses the three sign fibres, namely two open rays and
    the closed singleton zero. The narrow num_normedtype import supplies
    only the standard real order-topology facts, as in RealOpenIntervals.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology num_normedtype.
From Federer Require Import RealNormUP NormMetric NormMetricScaleContinuity RealMetricBackground
  NormPowerScalar BorelFunctionUP BorelFunctionBasic TopologicalBorel BorelFamilyBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_norm_real_identity_continuous]: supporting
    identification of real scalar norm topologies for Federer 2.4.16,
    p. 89; both metrics are absolute difference. *)
Lemma scalar_norm_real_identity_continuous (R : realType) :
  continuous (fun x : real_norm_metric_space (scalar_absolute_value_norm R) =>
    (x : real_line_metric R)).
Proof.
apply: (@metric_fixed_lipschitz_continuous R _ _ _ 1 ler01)=> x y.
change (is_true (`|x-y| <= 1*`|x-y|)); by rewrite mul1r.
Qed.

(** Source for [real_sign_borel]: supporting Borel measurability
    of sign in Federer 2.4.16, pp. 89–90; the value at zero is zero. *)
Lemma real_sign_borel (R : realType) :
  is_borel_function (fun x : real_line_metric R => (Num.sg x : real_line_metric R)).
Proof.
move=> U hU.
have hpiece (S : set (real_line_metric R)) (c : R) :
    borel_set S -> borel_set [set x | S x /\ U c].
  move=> hS; have [hc|hc] := pselect (U c).
  - have he : [set x | S x /\ U c] = S by apply/seteqP; split=> x; [by move=> []|by move=> hx; split].
    by rewrite he.
  - have he : [set x | S x /\ U c] = set0.
      apply/seteqP; split=> x; first by move=> [_ hx]; exact: hc hx.
      by move=> [].
    rewrite he; exact: open_borel_set open0.
have he : (fun x : real_line_metric R => (Num.sg x : real_line_metric R)) @^-1` U =
  [set x | 0 < x /\ U 1] `|` [set x | x < 0 /\ U (-1)] `|` [set x | x = 0 /\ U 0].
  apply/seteqP; split=> x.
  - have [hx|hx|hx] := ltgtP 0 x.
    + rewrite /preimage /= (gtr0_sg hx)=> hu; left; left; by split.
    + rewrite /preimage /= (ltr0_sg hx)=> hu; left; right; by split.
    + rewrite /preimage /= -hx sgr0=> hu; right; split=> //; exact: esym hx.
  - move=> [[[hx hu]|[hx hu]]|[-> hu]]; rewrite /preimage /=.
    + by rewrite (gtr0_sg hx).
    + by rewrite (ltr0_sg hx).
    + by rewrite sgr0.
rewrite he; apply: (borel_family_binary_union (borel_sets_family _)).
- apply: (borel_family_binary_union (borel_sets_family _)); apply: hpiece;
    apply: open_borel_set; [exact: open_gt | exact: open_lt].
- apply: hpiece; apply: closed_borel_set.
  change (closed [set (0 : real_line_metric R)]); apply: accessible_closed_set1; apply: hausdorff_accessible; exact: metric_hausdorff.
Qed.

(** Source for [scalar_norm_sign_borel]: supporting sign map on
    the scalar normed target used for Lp tests, Federer 2.4.16, pp. 89–90. *)
Lemma scalar_norm_sign_borel (R : realType) :
  is_borel_function (fun x : real_norm_metric_space (scalar_absolute_value_norm R) =>
    (Num.sg x : real_norm_metric_space (scalar_absolute_value_norm R))).
Proof.
have h1 := continuous_borel_function (@scalar_norm_real_identity_continuous R).
have h2 := borel_function_composition h1 (@real_sign_borel R).
have h3 := continuous_borel_function (@real_scalar_norm_identity_continuous R).
exact: (borel_function_composition h2 h3).
Qed.
