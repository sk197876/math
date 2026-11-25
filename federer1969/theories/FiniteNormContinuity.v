(** Federer (1969), 1.10.5, p. 48: supporting continuity for the
    finite-dimensional compactness argument. The proof uses the local
    seminorm difference bound and the previously proved Euclidean upper
    estimate. Only general metric topology is imported from the surrounding
    library. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  RealNormUP RealSeminormDifference FiniteNormUpperBound LinearBasis
  OrthonormalFamilies OrthonormalisationUP GramSchmidt.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Continuity.
Variable R : realType.
Variable V : lmodType R.
Variable B : V -> V -> R.
Hypothesis hB : is_inner_product B.
Variable N : V -> R.
Hypothesis hN : is_real_seminorm N.
Local Notation M := (inner_metric_space hB).

(** Source for [seminorm_inner_bound_continuous]: Federer 1.10.5,
    p. 48, supporting continuity criterion. A seminorm bounded by
    C times an inner-product norm is continuous in that metric. The
    proof works also for C zero by using C+1 in the error estimate. *)
Theorem seminorm_inner_bound_continuous C (hC : 0<=C)
    (hb : forall x, N x <= C * inner_norm hB x) :
  continuous (fun x : M => (N x : R^o)).
Proof.
move=> x; apply/cvgrPdist_lt; first exact: nbhs_filter.
move=> eps he.
have hD : 0 < C+1 by rewrite addrC ltr_pwDl.
have hd : 0 < eps/(C+1) by rewrite divr_gt0.
have hn : \forall y \near (nbhs x), inner_norm hB (x-y) < eps/(C+1).
  have hi : (fun y : M => y) @ (nbhs x) --> x := cvg_id.
  exact (@cvgr_dist_lt R (PseudoMetricNormedZmod.clone R M _) M (nbhs x)
    (nbhs_filter x) (fun y : M => y) x hi _ hd).
apply: (filterS _ hn)=> y hy.
change (`|N x-N y| < eps).
apply: le_lt_trans (@real_seminorm_absolute_difference R V N hN x y) _.
apply: le_lt_trans (hb (x-y)) _.
have hCD : C <= C+1 by rewrite lerDl ler01.
have hm := ler_wpM2r (inner_norm_nonnegative hB (x-y)) hCD.
apply: le_lt_trans hm _.
rewrite mulrC -(@ltr_pdivlMr R (C+1) (inner_norm hB (x-y)) eps hD).
exact hy.
Qed.

(** Source for [finite_seminorm_inner_continuous]: Federer 1.10.5,
    p. 48, every seminorm on a finite-dimensional vector space
    is continuous in an auxiliary Euclidean metric. Gram-Schmidt provides
    the orthonormal basis needed for the explicit upper bound. *)
Theorem finite_seminorm_inner_continuous n (e : 'I_n -> V) (he : is_basis e) :
  continuous (fun x : M => (N x : R^o)).
Proof.
have [u [hu ho]] := orthonormal_basis_exists hB he.
pose C := \sum_i N (u i).
have hC : 0 <= C by apply: sumr_ge0=> i _; exact: real_seminorm_nonnegative hN (u i).
apply: (@seminorm_inner_bound_continuous C hC)=> x.
exact (@finite_seminorm_inner_upper_bound R V B hB N hN n u hu
  (orthonormalisation_orthonormal ho) x).
Qed.
End Continuity.
