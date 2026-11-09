(** Proved existence and uniqueness of the independently specified
    Grassmann probability used by Federer (1969), 3.3.1, p. 287.
    This is precisely the prior 2.7.16(6) existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct FiniteCoordinates
  OrthogonalGroupTopology EuclideanOrthogonalInvariantMeasures
  EuclideanGrassmannProbabilityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [euclidean_grassmann_probability_exists]: existence
    of gamma_(n,k) in Federer 3.3.1, p. 287, by the independently
    proved invariant probability of 2.7.16(6), p. 139. All
    k<=n remain, including the single zero-plane and full-plane spaces. *)
Theorem euclidean_grassmann_probability_exists (R:realType) n k:
  (k<=n)%N ->exists gamma:set (euclidean_grassmann_space R n k)->\bar R,
    is_euclidean_grassmann_probability gamma.
Proof.
move=>hkn.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [gamma [hGamma _ _]]:=@euclidean_gamma_nm_exists_unique R n k
  mulS invS eS hS hkn.
by exists gamma.
Qed.

(** Source for [euclidean_grassmann_probability_unique]: uniqueness
    of gamma_(n,k) in the same use of 2.7.16(6), p. 139,
    by Federer 3.3.1, p. 287. No kernel-image equality is assumed. *)
Theorem euclidean_grassmann_probability_unique (R:realType) n k (hkn:(k<=n)%N)
    (gamma eta:set (euclidean_grassmann_space R n k)->\bar R):
  is_euclidean_grassmann_probability gamma ->
  is_euclidean_grassmann_probability eta ->gamma=eta.
Proof.
move=>hGamma hEta.
have [mulS [invS [eS hS]]]:=orthogonal_group_restriction_exists
  (@euclidean_inner_productP R n) (@coordinate_basisP R n).
have [nu [hNu hUnique _]]:=@euclidean_gamma_nm_exists_unique R n k
  mulS invS eS hS hkn.
by rewrite (hUnique gamma hGamma) (hUnique eta hEta).
Qed.
