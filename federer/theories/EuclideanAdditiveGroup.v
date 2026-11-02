(** Federer (1969), 2.7.16, pp. 133–134: "It should be clear from the
    preceding remarks that the topological assumptions of our general theory
    are satisfied in each of the following particular examples: (1) L^1 is
    the unique (left and right) Haar measure of the additive group of R ...
    the additive group of R^n is the direct sum of n factors equal to R".
    This module verifies the standing hypothesis of 2.7.1, p. 121, for the
    additive group of R^n with the topology of the dot-product norm of
    1.7.1, p. 28: addition and negation are continuous, R^n is Hausdorff,
    and closed balls are compact (Federer 1.7.1, p. 28, bounded
    compactness). It also records the translations tau_z(v) = z + v of p.
    133 and that compact sets lie in coordinate boxes. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module tvs.
From Federer Require Import FiniteCoordinates GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNorm InnerMetric InnerNormedTopology InnerBoundedness InnerFiniteCompactness
  EuclideanCoordinateMetric TopologicalGroupUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section AdditiveGroup.
Variable R : realType.
Variable n : nat.
Local Notation E := (inner_metric_space (@euclidean_inner_productP R n)).

(** Source for [euclidean_translation]: Federer 2.7.16, p. 133, "the
    univalent map tau: V -> A(V,V), tau_z(v) = z + v for z, v in V",
    for V = R^n. Direct definition. *)
Definition euclidean_translation (z x : E) : E := z + x.

(** Source for [euclidean_translationK]: Federer 2.7.16, pp. 133–134,
    tau transforms vector addition into composition, so tau_{-z} is the
    inverse of tau_z. Supporting lemma. *)
Lemma euclidean_translationK (z : E) :
  cancel (euclidean_translation z) (euclidean_translation (- z)).
Proof. by move=> x; rewrite /euclidean_translation addKr. Qed.

(** Source for [euclidean_translation_continuous]: continuity of the
    translations of the topological group R^n, Federer 2.7.1, p. 121,
    as used in 2.7.16, p. 134. Supporting lemma. *)
Lemma euclidean_translation_continuous (z : E) : continuous (euclidean_translation z).
Proof.
move=> x; rewrite /euclidean_translation.
apply: (@continuousD R E E (fun _ => z) (fun y => y) x); first exact: cst_continuous.
exact: cvg_id.
Qed.

(** Source for [euclidean_additive_group_laws]: "the additive group of
    R^n", Federer 2.7.16, p. 134, with the group laws of 2.7.1, p. 121.
    Supporting lemma. *)
Lemma euclidean_additive_group_laws : is_group_laws (fun x y : E => x + y) (fun x => - x) 0.
Proof. by split; [exact: addrA | exact: add0r | exact: addNr]. Qed.

(** Source for [euclidean_additive_topological_group]: "the additive
    group of R^n" is a topological group, Federer 2.7.16, p. 134:
    addition is continuous on R^n x R^n and negation is continuous.
    Supporting lemma for the hypotheses of 2.7.1, p. 121. *)
Lemma euclidean_additive_topological_group :
  is_topological_group (fun x y : E => x + y) (fun x => - x) 0.
Proof.
split; first exact: euclidean_additive_group_laws.
- exact: add_continuous.
- exact: opp_continuous.
Qed.

(** Source for [euclidean_closed_ball_compact]: bounded compactness
    of R^n, Federer 1.7.1, p. 28, applied to the closed ball
    {x : |x - a| <= r}; it supplies the local compactness required in
    2.7.16, p. 134. Supporting lemma. *)
Lemma euclidean_closed_ball_compact (a : E) (r : R) : compact [set x : E | `|x - a| <= r].
Proof.
have hb := @inner_finite_basis_boundedly_compact R _ _ (@euclidean_inner_productP R n) n _ (@coordinate_basisP R n).
apply: hb.
- have he : [set x : E | `|x - a| <= r] = closed_ball_ Num.norm a r.
    by apply/seteqP; split=> x /=; rewrite /closed_ball_ distrC.
  rewrite he; exact: closed_closed_ball_.
- exists (`|a| + r)=> x hx.
  have h := ler_normD (x - a) a.
  rewrite subrK in h; apply: (le_trans h); rewrite addrC lerD2l.
  exact: hx.
Qed.

(** Source for [euclidean_locally_compact]: R^n is locally compact,
    as required of the group in Federer 2.7.1, p. 121, and asserted in
    2.7.16, p. 134. Every point has the compact closed neighbourhood
    {x : |x - a| <= 1}. Supporting lemma. *)
Lemma euclidean_locally_compact : locally_compact [set: E].
Proof.
move=> x _; rewrite withinET; exists [set y : E | `|y - x| <= 1].
  apply: (@filterS _ _ _ (ball x 1)); last exact: nbhsx_ballx.
  by move=> y; rewrite -ball_normE /= distrC=> h; exact: ltW.
split; first exact: euclidean_closed_ball_compact.
have he : [set y : E | `|y - x| <= 1] = closed_ball_ Num.norm x 1.
  by apply/seteqP; split=> y /=; rewrite /closed_ball_ distrC.
rewrite he; exact: closed_closed_ball_.
Qed.

(** Source for [euclidean_hausdorff]: R^n is Hausdorff, Federer
    2.7.1, p. 121, as asserted in 2.7.16, p. 134; it is a metric space
    by 1.7.1, p. 28. Supporting lemma. *)
Lemma euclidean_hausdorff : hausdorff_space E.
Proof. exact: (@metric_hausdorff R [the metricType R of E]). Qed.

(** Source for [euclidean_additive_lch_group]: "the topological
    assumptions of our general theory are satisfied" for the additive
    group of R^n, Federer 2.7.16, p. 134: it is a locally compact
    Hausdorff topological group in the sense of 2.7.1, p. 121. Direct
    formalisation. *)
Theorem euclidean_additive_lch_group :
  is_locally_compact_hausdorff_group (fun x y : E => x + y) (fun x => - x) 0.
Proof.
split; first exact: euclidean_additive_topological_group.
- exact: euclidean_hausdorff.
- exact: euclidean_locally_compact.
Qed.

(** Source for [euclidean_compact_coordinate_bound]: supporting lemma
    for Federer 2.7.16, p. 134: a compact subset of R^n is contained in
    a coordinate box {x : |x_i| <= r for every i}, by 1.7.1, p. 28,
    since |x_i| <= |x|. *)
Lemma euclidean_compact_coordinate_bound (K : set E) :
  compact K -> exists r : R, 0 <= r /\ forall x, K x -> forall i, `|x i| <= r.
Proof.
move=> hK; have [M [_ hM]] := compact_bounded hK.
exists (`|M| + 1); split; first by rewrite addr_ge0 ?normr_ge0 ?ler01.
move=> x hx i; apply: le_trans (euclidean_coordinate_norm_bound i x) _.
have hlt : M < `|M| + 1 by apply: le_lt_trans (ler_norm M) _; rewrite ltrDl ltr01.
exact: (hM _ hlt x hx).
Qed.

End AdditiveGroup.
