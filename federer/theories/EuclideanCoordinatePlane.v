(** Federer (1969), 3.1.19, p. 231: the complementary plane
    obtained from a regular-level-set source chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates LinearRankUP LinearInjectiveRank
  EuclideanBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [euclidean_last_coordinate_plane]: supporting
    (2) implies (1) in Federer 3.1.19, p. 231. The kernel of the
    first r coordinates is an actual mu-plane, including r=0 or mu=0. *)
Lemma euclidean_last_coordinate_plane (R:realType) r mu :
  exists Z:G (R_n R (r+mu)) mu, forall x,
    grassmann_val Z x <-> @euclidean_first_block_map R r mu x=0.
Proof.
pose X:=R_n R (r+mu); pose Y:=R_n R mu.
pose p:=@euclidean_first_block_map R r mu.
pose q:=@euclidean_last_block_map R r mu.
pose j:=@euclidean_last_injection_map R r mu.
have hqj:cancel j q:=@euclidean_last_block_injectionK R r mu.
have hr:=@linear_injective_rank R Y X mu (@coordinate_basis R mu) (@coordinate_basisP R mu)
  (r+mu) (@coordinate_basis R (r+mu)) (@coordinate_basisP R (r+mu)) j (can_inj hqj).
pose Z:=@GrassmannSubspace R X mu (range_subspace (hom_as_linear j)) hr.
exists Z=>x; split.
- move=>[u hu]; change (x=j u) in hu; rewrite hu.
  exact (@euclidean_first_block_last_injection R r mu u).
- move=>hx; exists (q x).
  have he:=@euclidean_block_linear_decomposition R r mu x.
  change (x=@euclidean_first_injection_map R r mu (p x)+j (q x)) in he.
  by rewrite hx linear0 add0r in he.
Qed.
