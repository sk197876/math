(** Federer (1969), 2.5.14, p. 108, uses the products g_n f in the
    partition-of-unity argument. These supporting laws track continuity and
    support without adding a multiplication axiom to Federer's general
    function-lattice definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From mathcomp.analysis.normedtype_theory Require Import normed_module.
From Federer Require Import RealMetricBackground CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_product_support_right]: the support of a product is
    contained in the second factor's support, supporting g_n f in Federer
    2.5.14, p. 108 *)
Lemma real_product_support_right (R : realType) (X : topologicalType) (f g : X -> R) :
  real_function_support (fun x => f x*g x) `<=` real_function_support g.
Proof.
apply: (@real_function_support_in_closed_set R X _ _ (@real_function_support_closed R X g))=> x hx.
by rewrite (real_function_zero_off_support hx) mulr0.
Qed.

(** Source for [compact_support_continuous_multiplier]: products g_n f stay
    in K(X), as used in Federer 2.5.14, p. 108 Only one factor needs compact
    support. General-topology continuity of multiplication is the sole
    external ingredient. *)
Lemma compact_support_continuous_multiplier (R : realType) (X : topologicalType) (f g : X -> R) :
  continuous (f : X -> real_line_metric R) -> compactly_supported_continuous_functions g ->
  compactly_supported_continuous_functions (fun x => f x*g x).
Proof.
move=> hf [hg hs]; split.
- move=> x; exact (@continuousM R X f g x (hf x) (hg x)).
- apply: (@subclosed_compact X _ (real_function_support g)
    (@real_function_support_closed R X _) hs); exact: real_product_support_right.
Qed.

(** Source for [unit_interval_complement_product]: supporting range bound
    for the finite partition of unity in Federer 2.5.14, p. 108 If f and g
    take values in [0,1], so does (1-f)g. *)
Lemma unit_interval_complement_product (R : realType) (a b : R) :
  0 <= a <= 1 -> 0 <= b <= 1 -> 0 <= (1-a)*b <= 1.
Proof.
move=> /andP[ha0 ha1] /andP[hb0 hb1].
have hc0 : 0 <= 1-a by rewrite subr_ge0.
have hc1 : 1-a <= 1 by rewrite lerBlDr lerDl.
apply/andP; split; first exact: mulr_ge0 hc0 hb0.
have hb := ler_wpM2l hc0 hb1; rewrite mulr1 in hb.
exact (le_trans hb hc1).
Qed.
