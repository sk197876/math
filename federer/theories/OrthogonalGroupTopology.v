(** Federer (1969), 2.7.16, printed p. 139, example (6): "Since the
    orthogonal group O(n) is a compact subset of Hom(R^n, R^n), there exists
    a unique left and right Haar measure theta_n over O(n) such that
    theta_n[O(n)] = 1", and p. 140, example (7): "for g in G^0, x in R^n, y
    in R^n, t in R the equations ... show, when expanded in terms of inner
    products, that g(x) . g(y) = x . y, |g(x) + g(y) - g(x + y)|^2 = 0, |g(t
    x) - t g(x)|^2 = 0, hence g in O(n)". Here V is a space with an inner
    product and a finite basis (V = R^n gives O(n)). The module proves the
    algebraic part of example (7): a map g of V with |g(x) - g(y)| = |x - y|
    and g(0) = 0 preserves inner products and is linear, hence orthogonal
    (1.7.2, p. 28); a linear map preserving lengths is orthogonal. The
    orthogonal group O(V), the set of orthogonal members of the linear group
    of V (LinearGroupTopology.v), is a compact subset of Hom(V, V): it is
    closed, being the set of maps with |f(x)| = |x| for all x, and bounded,
    since ||f|| <= 1. It is a closed subgroup of the linear group, hence,
    with any restricted group structure (is_subgroup_restriction of
    IsotropyGroupTopology.v), a compact Hausdorff, in particular locally
    compact, topological group.  *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals
  topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import InnerProductUP InnerProductLaws InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology InnerBoundedness LinearBasis Bilinear TensorUP Hom HomInner OrthogonalMaps
  SubtypeCompactHausdorff IsotropyGroupTopology TopologicalProductMaps TopologicalGroupUP
  TopologicalGroupLaws HomSpaceTopology LinearGroupTopology LinearGroupSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Isometries.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation N := (inner_norm hB).
Local Notation hbil := (inner_bilinear hB).

(** Source for [inner_difference_square]: (u - v) . (u - v) =
    u . u - 2 (u . v) + v . v, Federer 1.7.1, p. 28, the expansion used
    in example (7) of 2.7.16, p. 140. Supporting lemma. *)
Lemma inner_difference_square (u v : V) : B (u - v) (u - v) = B u u - (B u v + B u v) + B v v.
Proof.
rewrite (bilBl hbil) !(bilBr hbil) (inner_symmetric hB v u).
change (B u u - B u v - (B u v - B v v) = B u u - (B u v + B u v) + B v v).
lra.
Qed.

(** Source for [distance_preserving_inner]: Federer 2.7.16, p. 140,
    example (7): if |g(x) - g(y)| = |x - y| for all x, y and g(0) = 0,
    then g(x) . g(y) = x . y. Direct formalisation. *)
Theorem distance_preserving_inner (g : V -> V) :
  (forall x y, N (g x - g y) = N (x - y)) -> g 0 = 0 -> forall x y, B (g x) (g y) = B x y.
Proof.
move=> hg h0.
have hn x : B (g x) (g x) = B x x.
  by rewrite -!(inner_norm_sqr hB); have := hg x 0; rewrite h0 !subr0 => ->.
move=> x y.
have h := congr1 (fun r => r ^+ 2) (hg x y).
rewrite /= !(inner_norm_sqr hB) !inner_difference_square !hn in h.
lra.
Qed.

(** Source for [inner_preserving_linear]: Federer 2.7.16, p. 140,
    example (7): if g(x) . g(y) = x . y for all x, y, then
    |g(t x + y) - t g(x) - g(y)|^2 = 0, so g is linear. Direct
    formalisation. *)
Theorem inner_preserving_linear (g : V -> V) : (forall x y, B (g x) (g y) = B x y) -> linear g.
Proof.
move=> hg t x y.
pose u := t *: x + y.
pose q := t *: g x + g y.
have hpq : B (g u) q = B u u.
  rewrite /q (bilDr hbil) (bilZr hbil) !hg.
  by rewrite /u [in RHS](bilDr hbil) [in RHS](bilZr hbil).
have hqq : B q q = B u u.
  rewrite /q /u !(bilDl hbil) !(bilDr hbil) !(bilZl hbil) !(bilZr hbil) !hg.
  by [].
have hz : B (g u - q) (g u - q) = 0.
  rewrite inner_difference_square hg hpq hqq.
  change (B u u - (B u u + B u u) + B u u = 0).
  by rewrite opprD addrA subrr sub0r addNr.
apply/eqP; rewrite -subr_eq0 -(inner_self_eq0 hB); apply/eqP; exact: hz.
Qed.

(** Source for [length_preserving_orthogonal]: a linear map f with
    |f(x)| = |x| for all x is orthogonal, f(x) . f(y) = x . y, Federer
    1.7.2, p. 28, by the argument of 2.7.16, p. 140, example (7).
    Supporting lemma. *)
Lemma length_preserving_orthogonal (f : {linear V -> V}) :
  (forall x, N (f x) = N x) -> is_orthogonal_map B B f.
Proof.
move=> hf x y; apply: distance_preserving_inner; last exact: linear0.
by move=> a c; rewrite -linearB hf.
Qed.

End Isometries.

Section OrthogonalGroup.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable n : nat.
Variable b : 'I_n -> V.
Hypothesis hb : is_basis b.
Local Notation H := (inner_metric_space (hom_inner_productP hB hB hb)).
Local Notation VT := (inner_metric_space hB).
Local Notation GL := (set_type (linear_group hB hb)).
Local Notation mul := (linear_group_mul hB hb).
Local Notation inv := (linear_group_inv hB hb).
Local Notation unit := (linear_group_unit hB hb).
Local Notation hG := (linear_group_operations hB hb).
Local Notation onorm := (hom_operator_norm hB hB hb).
Local Notation N := (inner_norm hB).

(** Source for [orthogonal_maps]: the orthogonal members of Hom(V, V),
    Federer 1.7.2, p. 28; for V = R^n this is "the orthogonal group
    O(n)" of 2.7.16, p. 139, as a subset of Hom(R^n, R^n). Definition. *)
Definition orthogonal_maps : set H := [set f | is_orthogonal_map B B (hom_as_linear (f : Hom V V))].

(** Source for [orthogonal_mapsE]: f is orthogonal if and only if
    |f(x)| = |x| for all x, Federer 1.7.2, p. 28, and 2.7.16, p. 140.
    Supporting lemma. *)
Lemma orthogonal_mapsE : orthogonal_maps = \bigcap_(x in [set: V]) [set f : H | N ((f : Hom V V) x) = N x].
Proof.
apply/seteqP; split=> f hf.
- by move=> x _; exact: (orthogonal_map_norm hB hB hf).
- by apply: length_preserving_orthogonal=> x; exact: hf x I.
Qed.

(** Source for [orthogonal_maps_closed]: O(n) is closed in
    Hom(R^n, R^n), Federer 2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_maps_closed : closed orthogonal_maps.
Proof.
rewrite orthogonal_mapsE; apply: closed_bigI=> x _.
have he : [set f : H | N ((f : Hom V V) x) = N x] =
    (fun f : H => `|((f : Hom V V) x : VT)|) @^-1` [set c | c = N x] by [].
rewrite he; apply: preimage_closed; last exact: closed_eq.
move=> f _; apply: (@continuous_comp H VT R (fun f : H => ((f : Hom V V) x : VT)) Num.norm).
  apply: (@continuous_comp H (H * VT)%type VT (fun f : H => (f, x))
    (fun q : H * VT => ((q.1 : Hom V V) q.2 : VT))).
    apply: (@topological_pair_continuous H H VT id (fun _ => x)); last exact: cst_continuous.
    by move=> g; exact: cvg_id.
  exact: (@hom_evaluation_continuous R V V B B hB hB n b hb).
exact: norm_continuous.
Qed.

(** Source for [orthogonal_maps_operator_norm]: ||f|| <= 1 for f in
    O(n), Federer 1.7.6, p. 33, used for "O(n) is a compact subset" in
    2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_maps_operator_norm (f : H) : orthogonal_maps f -> onorm f <= 1.
Proof.
move=> hf; apply: hom_operator_norm_least; first exact: ler01.
by move=> x; rewrite mul1r (orthogonal_map_norm hB hB hf).
Qed.

(** Source for [orthogonal_maps_compact]: "the orthogonal group O(n)
    is a compact subset of Hom(R^n, R^n)", Federer 2.7.16, p. 139: it is
    closed and bounded, |f| <= (dim V)^{1/2} ||f|| <= (dim V)^{1/2}.
    Direct formalisation. *)
Theorem orthogonal_maps_compact : compact orthogonal_maps.
Proof.
apply: (hom_space_boundedly_compact hb); first exact: orthogonal_maps_closed.
exists (Num.sqrt n%:R)=> f hf.
apply: le_trans (hom_space_le_operator f) _.
by rewrite -[X in _ <= X]mulr1 ler_wpM2l ?sqrtr_ge0 // orthogonal_maps_operator_norm.
Qed.

(** Source for [orthogonal_maps_linear_group]: orthogonal maps are
    univalent, Federer 1.7.2, p. 28, so O(n) is a subset of GL(n, R),
    2.7.16, p. 139. Supporting lemma. *)
Lemma orthogonal_maps_linear_group : orthogonal_maps `<=` linear_group hB hb.
Proof. by move=> f hf; exact: (orthogonal_map_injective hB hB hf). Qed.

(** Source for [orthogonal_group]: the orthogonal group of V, Federer
    2.7.16, p. 139, "the orthogonal group O(n)", as a subset of the
    linear group of V. Definition. *)
Definition orthogonal_group : set GL := set_val @^-1` orthogonal_maps.

(** Source for [orthogonal_group_compact]: O(n) is a compact subset of
    GL(n, R) with the relative topology, Federer 2.7.16, p. 139.
    Direct formalisation. *)
Theorem orthogonal_group_compact : compact orthogonal_group.
Proof.
exact: (set_type_compact_preimage orthogonal_maps_compact orthogonal_maps_linear_group).
Qed.

(** Source for [orthogonal_group_closed]: O(n) is closed in GL(n, R),
    Federer 2.7.16, p. 139, being compact in a Hausdorff space.
    Supporting lemma. *)
Lemma orthogonal_group_closed : closed orthogonal_group.
Proof.
apply: compact_closed; last exact: orthogonal_group_compact.
exact: (lch_group_hausdorff (linear_group_operations_lch hB hb)).
Qed.

(** Source for [orthogonal_group_subgroup]: O(n) is a subgroup of
    GL(n, R), Federer 1.7.2, p. 28, and 2.7.16, p. 139. Supporting
    lemma. *)
Lemma orthogonal_group_subgroup : is_subgroup mul inv unit orthogonal_group.
Proof.
split.
- move=> x y; rewrite /= (linear_group_unitE hG).
  exact: (orthogonal_identity B x y).
- move=> g h hg hh x y; rewrite /= (linear_group_mulE hG).
  exact: (orthogonal_composition hh hg x y).
- move=> g hg; have [hgi hig] := linear_group_inv_cancel hG g.
  exact: (orthogonal_inverse hg hig).
Qed.

(** Source for [orthogonal_group_restriction_exists]: O(n) is a group
    with the operations of GL(n, R), Federer 2.7.16, p. 139. Existence
    of the restricted operations (subgroup_restriction_exists). *)
Theorem orthogonal_group_restriction_exists :
  exists mulS invS eS, is_subgroup_restriction mul inv unit orthogonal_group mulS invS eS.
Proof. exact: subgroup_restriction_exists orthogonal_group_subgroup. Qed.

Section Restriction.
Variables (mulS : orthogonal_group -> orthogonal_group -> orthogonal_group)
  (invS : orthogonal_group -> orthogonal_group) (eS : orthogonal_group).
Hypothesis hS : is_subgroup_restriction mul inv unit orthogonal_group mulS invS eS.

(** Source for [orthogonal_group_lch]: O(n), a closed subgroup of
    GL(n, R), is a locally compact Hausdorff topological group, Federer
    2.7.16, p. 139, with 2.7.1, p. 121. Direct formalisation. *)
Theorem orthogonal_group_lch : is_locally_compact_hausdorff_group mulS invS eS.
Proof.
apply: (subgroup_restriction_locally_compact_hausdorff hS); last exact: orthogonal_group_closed.
exact: linear_group_operations_lch.
Qed.

(** Source for [orthogonal_group_compact_space]: O(n) is compact with
    its own topology, "O(n) is a compact subset", Federer 2.7.16, p. 139.
    Direct formalisation. *)
Theorem orthogonal_group_compact_space : compact [set: orthogonal_group].
Proof.
have -> : [set: orthogonal_group] = set_val @^-1` orthogonal_group.
  by apply/seteqP; split=> // a _; exact: set_valP.
exact: set_type_compact_preimage orthogonal_group_compact (@subset_refl _ _).
Qed.

End Restriction.

End OrthogonalGroup.

Arguments orthogonal_maps {R V B} hB {n b} hb.
Arguments orthogonal_group {R V B} hB {n b} hb.
