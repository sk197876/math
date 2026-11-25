(** General topology supporting Federer (1969), 3.4.3,
    p. 317: the countable Euclidean base in the exact
    norm metric used by the differential predicates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormMetric InnerMetric EuclideanLebesgueHaar InnerOwnNormTopology
  HomeomorphismUP HomeomorphicCountableBase CountableOpenBaseUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_norm_countable_open_base]: the
    countable-neighbourhood assembly implicit in 3.4.3, p. 317.
    Transfer the existing Euclidean base through the proved identity
    homeomorphism; no additional topological assumption is introduced. *)
Lemma euclidean_norm_countable_open_base (R:realType) m:
  exists U:nat->set (real_norm_metric_space
    (inner_norm_real_norm (@euclidean_inner_productP R m))),is_countable_open_base U.
Proof.
have [U hU]:=@euclidean_countable_open_base R m.
have hHomeo:=inner_own_norm_homeomorphism (@euclidean_inner_productP R m).
exists (fun i=>U i).
exact:(homeomorphic_countable_base (homeomorphism_left_inverse hHomeo)
  (homeomorphism_right_inverse hHomeo) (homeomorphism_continuous hHomeo)
  (homeomorphism_inverse_continuous hHomeo) hU).
Qed.
