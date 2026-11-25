(** Federer (1969), 2.3.6, p. 77: Tietze extends the continuous restriction
    obtained by Lusin. Source context: TietzeNormalisation.v. The extension
    implementation is sealed. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealMetricBackground PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed PartialContinuityUP
  PartialContinuityTotal PartialContinuityAgreement RealContinuousExtensionUP RealContinuousExtensionSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import numFieldTopology.Exports.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [lusin_real_closed_extension]: the agreement
    h|C=f|C in Federer 2.3.6, p. 77, second corollary,
    for a partial real-valued function continuous on closed C. *)
Theorem lusin_real_closed_extension (R : realType) (X : topologicalType)
    (hn : normal_space X) (C : set X) (f : partial_function X (real_line_metric R)) :
  closed C -> partial_function_continuous_on C f ->
  exists h : X -> real_line_metric R, continuous h /\
    C `<=` partial_function_agreement f (partial_function_total h).
Proof.
move=> hC hf; pose g := @PartialFunctionExtension.value X (real_line_metric R) f 0.
have hg := @PartialFunctionExtension.laws X (real_line_metric R) f 0.
have ha : C `<=` partial_function_agreement f (partial_function_total g).
  move=> x hx; have [y hy] := @partial_continuity_domain X (real_line_metric R) C f hf x hx.
  exists y; split=> //; exact: hg x y hy.
have hgc := @partial_continuity_agreement X (real_line_metric R) C f (partial_function_total g) ha hf.
have hcts : {within C, continuous (g : X -> R^o)}.
  exact: (proj1 (partial_continuity_total_iff C g)) hgc.
pose h := @RealContinuousExtension.value R X hn C hC g hcts.
have hh := @RealContinuousExtension.laws R X hn C hC g hcts.
exists h; split; first exact: hh.1.
move=> x hx; have [y [hy hgy]] := ha x hx.
exists y; split=> //; change (h x = y).
by rewrite /h (hh.2 x hx); exact hgy.
Qed.
