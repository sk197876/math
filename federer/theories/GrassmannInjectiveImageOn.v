(** Federer (1969), 3.2.48, p. 285: transverse
    coordinates preserve the dimension of the original tangent
    plane. Supporting relative version of the linear tangent
    transport in 3.1.21, p. 234: injectivity is required
    only on the actual source plane. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier LinearBasis
  GrassmannSubspaces LinearRankUP LinearInjectiveRank.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [grassmann_injective_image_on]: the k- and
    m-dimensional actual transverse tangent planes in 3.2.48,
    p. 285, by 3.1.21, p. 234. The
    ambient coordinate projection may have a kernel; only
    its restriction to the original plane must be injective. *)
Lemma grassmann_injective_image_on (K:fieldType) (X Y:lmodType K)
    mu (Z:G X mu) (M:Hom X Y) n (b:'I_n->Y) (hb:is_basis b) :
  (forall x y,grassmann_val Z x ->grassmann_val Z y ->M x=M y ->x=y) ->
  exists W:G Y mu,(grassmann_val W:set Y)=M @` (grassmann_val Z:set X).
Proof.
move=>hM.
pose L:=hom_comp M (hom_of_linear (subspace_inclusion (grassmann_val Z))).
have hL:injective L.
  move=>x y he; apply:subspace_val_injective.
  exact (hM (subspace_val x) (subspace_val y) (subspace_valP x) (subspace_valP y) he).
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
