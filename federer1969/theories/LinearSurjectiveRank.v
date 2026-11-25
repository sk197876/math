(** Federer (1969), 3.1.18, pp. 229–230: p Df has full target rank,
    first at a and then on a sufficiently small constant-rank neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier
  SubspaceFamilies LinearBasis FiniteDualDimension Annihilator FiniteSpans
  FiniteIndependence FiniteBasisComparison FiniteBasisCriterion FiniteDimension
  LinearRankUP LinearRankAtLeast.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_surjective_rank_at_least]: an epimorphism onto
    a v-dimensional space has rank at least v, supporting the map p Df
    in Federer 3.1.18, p. 229. Preimages of a basis witness this. *)
Lemma linear_surjective_rank_at_least (K:fieldType) (X Y:lmodType K)
    v (b:'I_v->Y) (hb:is_basis b) (L:Hom X Y) :
  (forall y, exists x, L x=y) -> linear_rank_at_least L v.
Proof.
move=>hs.
have hex i:exists x:X, L x=b i := hs (b i).
have [e he] := choice hex.
exists e; move=>c hc.
apply: (finite_basis_independent hb).
have h : (\sum_i c i*:b i)=\sum_i c i*:L (e i).
  apply: eq_bigr=>i _; by rewrite he.
by rewrite h.
Qed.

(** Source for [linear_full_target_rank_surjective]: full target
    rank means surjectivity, supporting the displayed rank equalities
    in Federer 3.1.18, p. 230. Empty target dimensions are included. *)
Lemma linear_full_target_rank_surjective (K:fieldType) (X Y:lmodType K)
    v (b:'I_v->Y) (hb:is_basis b) (L:Hom X Y) :
  has_linear_rank L v -> forall y, exists x, L x=y.
Proof.
move=>[e he].
pose W:=range_subspace (hom_as_linear L).
pose a:=fun i=>subspace_val (e i).
have hi:=@finite_independent_map K (Finite.clone 'I_v _) (subspace_space W) Y
  (subspace_inclusion W) e (@subspace_val_injective K Y W) (finite_basis_independent he).
have ha:is_basis a.
  apply: (@finite_independent_basis K (finite_basis_vect hb) v a).
  - by rewrite finite_basis_dimension card_ord.
  - exact hi.
move=>y.
have hW:W y.
  rewrite (basis_vector_expansion ha y).
  elim/big_rec: _=>[|i z _ hz]; first exact: subspace_zero.
  apply: subspace_add=>//; apply: subspace_scale; exact: subspace_valP.
have [x hx]:=hW; exists x; exact: esym hx.
Qed.

(** Source for [linear_rank_from_full_threshold]: a rank threshold
    at the target dimension forces exactly that rank, supporting
    v=rank(p Df(x)) in Federer 3.1.18, p. 230. *)
Lemma linear_rank_from_full_threshold (K:fieldType) (X Y:lmodType K)
    v (b:'I_v->Y) (hb:is_basis b) (L:Hom X Y) :
  linear_rank_at_least L v -> has_linear_rank L v.
Proof.
move=>ht.
have [r [hr hrv]]:=linear_rank_exists L hb.
have hvr: (v<=r)%N := (linear_rank_at_leastP v hr).1 ht.
have he:r=v by apply/eqP; rewrite eqn_leq hrv hvr.
by rewrite -he.
Qed.
