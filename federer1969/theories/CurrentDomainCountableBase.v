(** Federer (1969), 4.1.8, p. 361: the original
    open factor domains have countable bases for their
    relative Euclidean topology. Reuse the already proved
    exact norm-metric base and the general subspace law. *)
From mathcomp Require Import all_boot all_order all_algebra functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct EuclideanNormCountableBase CountableOpenBaseUP OpenSubspaceMeasure CurrentDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [current_domain_countable_open_base]: the
    actual original domain has a countable open base,
    supporting product Radon regularity in Federer 4.1.8,
    p. 361. The inherited base works even for
    empty domains and zero-dimensional ambient spaces. *)
Theorem current_domain_countable_open_base (R:realType) n (U:set (R_n R n)):
  exists B:nat->set (current_domain R n U),is_countable_open_base B.
Proof.
have[B hB]:=@euclidean_norm_countable_open_base R n.
exists (fun j=>set_val @^-1` B j).
exact:(@open_subspace_countable_open_base R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) U B hB).
Qed.
