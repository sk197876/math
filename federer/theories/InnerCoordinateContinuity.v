(** Federer (1969), 1.7.3, p. 29: supporting continuity of linear
    coordinates in the principal-axis compactness argument. Cauchy's
    inequality supplies the bound; general normed-space topology supplies
    the continuity rule. *)
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp classical_sets reals topology
  num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities
  InnerMetric InnerNormedTopology OrthonormalFamilies.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Coordinates.
Variable R : rcfType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Local Notation M := (inner_metric_space hB).

(** Source for [inner_coordinate_continuous]: Federer 1.7.3,
    p. 29, supporting continuity of x -> x.v for a fixed vector v.
    The statement holds in arbitrary dimension by Cauchy's inequality. *)
Theorem inner_coordinate_continuous v :
  continuous (fun x : M => inner_coordinate hB v x).
Proof.
apply: bounded_linear_continuous.
apply/linear_boundedP.
apply: (filterS _ (nbhs_pinfty_ge (num_real (inner_norm hB v)))) => r hr x.
rewrite inner_norm_topologyE inner_coordinateE.
have hc := @inner_cauchy R V B hB x v.
apply: (le_trans hc).
have hm := ler_wpM2r (inner_norm_nonnegative hB x) hr.
by rewrite mulrC in hm.
Qed.
End Coordinates.
