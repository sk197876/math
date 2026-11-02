(** Federer (1969), 3.2.28(2), p. 264:
    rank of the actual differential is unchanged by
    isomorphic ambient coordinates or by parametrising
    the same tangent image. Supporting finite linear algebra. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP ModuleQuotient SubspaceSums SubspaceCarrier SubspaceFamilies
  LinearBasis FiniteDimension FiniteIndependence FiniteBasisComparison
  LinearRankUP LinearRankAtLeast LinearRankImageInclusion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_same_image_rank]: parametrising the
    same differential image leaves its dimension unchanged,
    supporting Federer 3.2.28(2), p. 264, via the
    basis-size theorem of 1.6.1, p. 23. *)
Lemma linear_same_image_rank (K:fieldType) (X Y Z:lmodType K)
    (L:Hom X Z) (M:Hom Y Z) n (b:'I_n->Z) (hb:is_basis b) r:
  has_linear_rank L r ->
  (forall x,exists y,M y=L x) ->(forall y,exists x,L x=M y) ->
  has_linear_rank M r.
Proof.
move=>hL hLM hML.
have [s [hM hs]]:=linear_rank_exists M hb.
have h1: (r<=s)%N:=linear_rank_image_inclusion hL hM hLM.
have h2: (s<=r)%N:=linear_rank_image_inclusion hM hL hML.
have he:s=r by apply/eqP; rewrite eqn_leq h2 h1.
by rewrite -he.
Qed.

(** Source for [linear_injective_postcomposition_rank]:
    injective target coordinates preserve the rank used
    in Federer 3.2.28(2), p. 264. The finite target
    basis supplies existence; independence proves equality. *)
Lemma linear_injective_postcomposition_rank (K:fieldType) (X Y Z:lmodType K)
    (L:Hom X Y) (f:Hom Y Z) n (b:'I_n->Z) (hb:is_basis b) r:
  injective f ->has_linear_rank L r ->has_linear_rank (hom_comp f L) r.
Proof.
move=>hInj hL.
have [s [hM hs]]:=linear_rank_exists (hom_comp f L) hb.
have hr:(r<=s)%N.
  apply:(linear_rank_at_leastP r hM).1.
  have [e he]:=(linear_rank_at_leastP r hL).2 (leqnn r).
  exists e.
  exact:(@finite_independent_map K [the finType of 'I_r] Y Z
    (hom_as_linear f) (fun i=>L (e i)) hInj he).
have hsr:(s<=r)%N.
  have [e he]:=(linear_rank_at_leastP s hM).2 (leqnn s).
  have hmem i:range_subspace (hom_as_linear L) (L (e i)) by exists (e i).
  pose a:=subspace_family hmem.
  have hi:finite_independent a.
    move=>c hc; apply:he.
    have hv:=congr1 (fun v:subspace_space (range_subspace (hom_as_linear L))=>f (subspace_val v)) hc.
    rewrite !linear_sum !linear0 in hv.
    have hSum:(\sum_i f (subspace_val (c i*:a i)))=
        \sum_i c i*:hom_comp f L (e i).
      apply:eq_bigr=>i _; by rewrite !linearZ.
    by rewrite hSum in hv.
  have [d hd]:=hL.
  have hDim:=@finite_independent_dimension K (finite_basis_vect hd) s a hi.
  by rewrite finite_basis_dimension card_ord in hDim.
have he:s=r by apply/eqP; rewrite eqn_leq hsr hr.
by rewrite -he.
Qed.
