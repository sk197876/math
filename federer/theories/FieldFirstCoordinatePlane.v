(** Federer (1969), 3.4.12, p. 339, using 3.1.19, p. 231: the complementary plane
    obtained from a regular-level-set source chart. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannSubspaces GrassmannAbbreviations FiniteCoordinates LinearRankUP LinearInjectiveRank
  FieldBlockLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [field_first_coordinate_plane]: supporting
    (2) implies (1) in Federer 3.1.19, p. 231. The kernel of the
    last r coordinates is an actual mu-plane, including r=0 or mu=0. *)
Lemma field_first_coordinate_plane (R:fieldType) r mu :
  exists Z:G (coordinate_space R (mu+r)) mu, forall x,
    grassmann_val Z x <-> @field_last_block_map R mu r x=0.
Proof.
pose X:=coordinate_space R (mu+r); pose Y:=coordinate_space R mu.
pose p:=@field_last_block_map R mu r.
pose q:=@field_first_block_map R mu r.
pose j:=@field_first_injection_map R mu r.
have hqj:cancel j q:=@field_first_block_injectionK R mu r.
have hr:=@linear_injective_rank R Y X mu (@coordinate_basis R mu) (@coordinate_basisP R mu)
  (mu+r) (@coordinate_basis R (mu+r)) (@coordinate_basisP R (mu+r)) j (can_inj hqj).
pose Z:=@GrassmannSubspace R X mu (range_subspace (hom_as_linear j)) hr.
exists Z=>x; split.
- move=>[u hu]; change (x=j u) in hu; rewrite hu.
  exact (@field_last_block_first_injection R mu r u).
- move=>hx; exists (q x).
  have he:=@field_block_linear_decomposition R mu r x.
  change (x=j (q x)+@field_last_injection_map R mu r (p x)) in he.
  by rewrite hx linear0 addr0 in he.
Qed.
