(** Federer (1969), 1.7.1, p. 28: the topology induced by the inner-product
    norm. This adapter makes the locally proved norm laws available to
    general topological continuity and compactness tools. It retains exactly
    the metric already verified in InnerMetric. No external inner-product
    theorem is used. Source context are recorded in InnerProductUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets topology tvs num_normedtype
  pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section NormedTopology.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).

(** Source for [inner_norm_mnat]: Federer 1.7.1, p. 28,
    supporting compatibility of the norm with repeated addition. *)
Lemma inner_norm_mnat (x : M) n : inner_norm hB (x *+ n) = inner_norm hB x *+ n.
Proof. by rewrite -[x *+ n]scaler_nat inner_normZ normr_nat mulr_natl. Qed.

(** Source for [inner_norm_metric_separates]: Federer
    1.7.1, p. 28, norm definiteness in the form required by the
    general normed-group interface. *)
Lemma inner_norm_metric_separates (x : M) : inner_norm hB x = 0 -> x = 0.
Proof. move=> h; apply/eqP; by rewrite -(inner_norm_eq0 hB) h eqxx. Qed.

HB.instance Definition _ := Num.Zmodule_isNormed.Build R M
  (@inner_norm_triangle R V B hB) inner_norm_metric_separates
  inner_norm_mnat (@inner_normN R V B hB).
HB.instance Definition _ := isPointed.Build M 0.

(** Source for [inner_metric_normE]: Federer 1.7.1,
    p. 28, the normed-group and metric structures have the same distance. *)
Lemma inner_metric_normE (x y : M) : mdist x y = `|y-x|.
Proof. by rewrite inner_metric_distanceE -[x-y]opprB inner_normN. Qed.

HB.instance Definition _ := NormedZmoduleMetric.Build R M inner_metric_normE.
HB.instance Definition _ := PseudoMetricNormedZmod_Lmodule_isNormedModule.Build
  R M (@inner_normZ R V B hB).

(** Source for [inner_norm_topologyE]: Federer 1.7.1,
    p. 28, the norm used by the topology is exactly the specified
    inner-product norm, with no change of scale or metric. *)
Lemma inner_norm_topologyE (x : M) : `|x| = inner_norm hB x.
Proof. by []. Qed.
End NormedTopology.
