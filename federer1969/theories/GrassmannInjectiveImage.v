(** Supporting finite linear algebra for Federer (1969),
    3.1.21, p. 234: injective coordinate changes preserve
    the dimension of a tangent plane. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier LinearBasis
  GrassmannSubspaces LinearRankUP LinearInjectiveRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [grassmann_injective_image]: supporting the
    mu-dimensional tangent-space assertion in Federer 3.1.21,
    p. 234. An injective linear map sends a mu-plane
    to a mu-plane; existence follows from a basis of the
    actual image rather than an assumed dimension formula. *)
Lemma grassmann_injective_image (K:fieldType) (X Y:lmodType K)
    mu (Z:G X mu) (M:Hom X Y) n (b:'I_n->Y) (hb:is_basis b) :
  injective M -> exists W:G Y mu,(grassmann_val W:set Y)=M @` (grassmann_val Z:set X).
Proof.
move=>hM.
pose L:=hom_comp M (hom_of_linear (subspace_inclusion (grassmann_val Z))).
have hL:injective L.
  move=>x y he; apply: subspace_val_injective; apply: hM.
  exact he.
have [z hz]:=grassmann_proof Z.
have hr:=@linear_injective_rank K (subspace_space (grassmann_val Z)) Y mu z hz n b hb L hL.
pose W:=@GrassmannSubspace K Y mu (range_subspace (hom_as_linear L)) hr.
exists W; apply/seteqP; split=>y.
- move=>[x hx].
  exists (subspace_val x); first exact: subspace_valP.
  exact: esym hx.
- move=>[x hx hxy].
  exists (subspace_lift hx); change (y=L (subspace_lift hx)).
  by rewrite /L hom_compE hom_of_linearE /= hxy.
Qed.
