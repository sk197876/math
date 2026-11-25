(** Federer (1969), 2.7.12, printed p. 129: "A group G is called unimodular
    if and only if the left and right Haar integrals of G coincide; this is
    equivalent to the condition that the modular function Delta_G is
    constant with value 1. In particular, every compact group is
    unimodular." The predicate is_unimodular is that of UnimodularGroupUP.v
    and the modular function that of ModularFunctionUP.v (2.7.8, p. 126); G
    is a locally compact Hausdorff topological group. The equivalence uses
    2.7.8(1), (2) and a left Haar integral given by 2.7.5, p. 125. Federer
    gives no argument for the compact case; it follows from the equivalence
    and from the fact, stated in the same paragraph, that continuous
    homomorphisms of a compact group into the positive numbers are constant
    with value 1 (CompactGroupCharacters.v), applied to Delta_G. Neither.
    The local erratum has no entry for p. 129. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealMetricBackground TopologicalGroupUP CovariantIntegralUP
  HaarIntegralUP HaarIntegralExistence ModularFunctionUP ModularFunction CompactGroupCharacters
  UnimodularGroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section UnimodularGroups.
Variable R : realType.
Variable G : topologicalType.
Variables (mul : G -> G -> G) (inv : G -> G) (e : G).
Hypothesis hGc : is_locally_compact_hausdorff_group mul inv e.

(** Source for [unimodular_iff_modular_unit]: "this is equivalent to
    the condition that the modular function Delta_G is constant with
    value 1", Federer 2.7.12, p. 129. Direct formalisation for any
    modular function Delta of G. If the Haar integrals coincide, a left
    Haar integral lambda (2.7.5) is right invariant and right Delta
    covariant (2.7.8(1)), whence Delta(g) lambda(u) = lambda(u) with
    lambda(u) <> 0. If Delta = 1, then 2.7.8(1), (2) say that left Haar
    integrals are right invariant and right Haar integrals are left
    invariant. *)
Theorem unimodular_iff_modular_unit (Delta : G -> R) :
  is_modular_function mul inv Delta -> is_unimodular R mul inv <-> forall g, Delta g = 1.
Proof.
move=> hD; split.
  move=> hU g; have [lambda hl] := left_haar_integral_exists R hGc.
  have hr := (hU lambda).1 hl.
  have [u hu hu0] := nonzero_invariant_integral_nonzero hl.
  have h1 := covariant_integral_law (modular_function_left_haar hD hl) g hu.
  have h2 := covariant_integral_law (nonzero_invariant_integral_invariant hr) g hu.
  rewrite h1 in h2; exact: (mulIf (introN eqP hu0) h2).
move=> hD1; have hDe : Delta = (fun _ => 1) by apply: funext=> g; exact: hD1.
move=> lambda; split=> h.
- split; [|exact: nonzero_invariant_integral_monotone h|exact: nonzero_invariant_integral_nonzero h].
  by have := modular_function_left_haar hD h; rewrite hDe.
- split; [|exact: nonzero_invariant_integral_monotone h|exact: nonzero_invariant_integral_nonzero h].
  by have := modular_function_right_haar hD h; rewrite hDe.
Qed.

(** Source for [compact_group_unimodular]: "In particular, every
    compact group is unimodular", Federer 2.7.12, p. 129. Direct
    formalisation: Delta_G is a continuous homomorphism of G into the
    positive numbers (2.7.8 and 2.7.1, p. 122), hence constant with
    value 1 when G is compact. *)
Theorem compact_group_unimodular : compact [set: G] -> is_unimodular R mul inv.
Proof.
move=> hc; have [D hD] := modular_function_exists R hGc.
apply/(unimodular_iff_modular_unit hD).
have [hDM _] := modular_function_homomorphism hGc hD.
apply: (compact_group_positive_character_unit (topological_group_laws (lch_group_topological hGc))
  (modular_function_continuous hD) hDM (modular_function_positive hD) hc).
Qed.

End UnimodularGroups.
