(** Federer (1969), 3.1.18, p. 229: the dimension of the actual
    image of a linear map. Rank is specified by a finite basis of that
    image, independently of any matrix or chosen basis. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier FiniteIndependence
  FiniteBasisComparison FiniteBasisCriterion FiniteDimension BoundedIndependentBasis
  FiniteCoordinates GrassmannAbbreviations LinearBasis FiniteSpans TensorUP Bilinear FiniteDualDimension Annihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [has_linear_rank]: rank dim im L in Federer 3.1.18,
    p. 229. This abstract predicate specifies a basis size of the
    actual range, without making an existence assumption. *)
Definition has_linear_rank (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) r :=
  exists e : 'I_r -> subspace_space (range_subspace (hom_as_linear L)), is_basis e.

(** Source for [linear_rank_unique]: supporting the well-defined rank
    in Federer 3.1.18, p. 229, by the basis-size theorem of 1.6.1. *)
Lemma linear_rank_unique (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) r s : has_linear_rank L r -> has_linear_rank L s -> r=s.
Proof. move=>[e he] [d hd]; exact: finite_basis_size he hd. Qed.

(** Source for [linear_rank_codomain_bound]: the bound rank L<=n,
    supporting v<=inf{m,n} in Federer 3.1.18, p. 229. *)
Lemma linear_rank_codomain_bound (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) n (b : 'I_n->Y) (hb : is_basis b) r :
  has_linear_rank L r -> (r<=n)%N.
Proof.
move=>[e he].
have hi := @finite_independent_map K [the finType of 'I_r]
  (subspace_space (range_subspace (hom_as_linear L))) Y
  (subspace_inclusion _) e (@subspace_val_injective K Y (range_subspace (hom_as_linear L))) (finite_basis_independent he).
have h := @finite_independent_dimension K (finite_basis_vect hb) r
  (fun i=>subspace_val (e i)) hi.
by rewrite finite_basis_dimension card_ord in h.
Qed.

(** Source for [linear_rank_exists]: supporting existence of rank for
    finite-dimensional targets in Federer 3.1.18, p. 229. A bound on
    independent families in the range produces a basis (1.6.1). *)
Lemma linear_rank_exists (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) n (b : 'I_n->Y) (hb : is_basis b) :
  exists r, has_linear_rank L r /\ (r<=n)%N.
Proof.
pose U := subspace_space (range_subspace (hom_as_linear L)).
have hbound k (e : 'I_k->U) : finite_independent e -> (k<=n)%N.
  move=>he.
  have hi := @finite_independent_map K [the finType of 'I_k] U Y
    (subspace_inclusion _) e (@subspace_val_injective K Y (range_subspace (hom_as_linear L))) he.
  have h := @finite_independent_dimension K (finite_basis_vect hb) k
    (fun i=>subspace_val (e i)) hi.
  by rewrite finite_basis_dimension card_ord in h.
have [r [e [he hr]]] := @bounded_independent_basis K U n hbound.
exists r; split=>//; by exists e.
Qed.

(** Source for [linear_rank_domain_bound]: the bound rank L<=m,
    supporting v<=inf{m,n} in Federer 3.1.18, p. 229. Lift a range
    basis to the source and use its independence. *)
Lemma linear_rank_domain_bound (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) m (b : 'I_m->X) (hb : is_basis b) r :
  has_linear_rank L r -> (r<=m)%N.
Proof.
move=>[e he].
have hex i : exists x:X, L x=subspace_val (e i).
  have [x hx] := subspace_valP (e i); by exists x.
pose d i : X := projT1 (cid (hex i)).
have hd i : L (d i)=subspace_val (e i) by rewrite /d; case: (cid (hex i)).
have hi : finite_independent d.
  move=>c hc; apply: (finite_basis_independent he).
  apply: (@subspace_val_injective K Y (range_subspace (hom_as_linear L))).
  rewrite linear_sum linear0.
  have hL := congr1 L hc.
  rewrite linear_sum linear0 in hL.
  have hs : (\sum_i L (c i*:d i))=\sum_i c i*:subspace_val (e i).
    apply: eq_bigr=>i _.
    exact (eq_trans (linZ (hom_linear L) (c i) (d i))
      (congr1 (fun z=>c i*:z) (hd i))).
  rewrite hs in hL.
  under eq_bigr do rewrite linearZ.
  exact hL.
have h := @finite_independent_dimension K (finite_basis_vect hb) r d hi.
by rewrite finite_basis_dimension card_ord in h.
Qed.

(** Source for [linear_rank_zeroP]: rank zero means the linear map
    vanishes, supporting the v=0 case of Federer 3.1.18, p. 229. *)
Lemma linear_rank_zeroP (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) : has_linear_rank L 0%N <-> forall x, L x=0.
Proof.
split.
- move=>[e he] x.
  have hL : range_subspace (hom_as_linear L) (L x) by exists x.
  have hu := basis_vector_expansion he (subspace_lift hL).
  rewrite big_ord0 in hu.
  have hv := congr1 subspace_val hu.
  by rewrite subspace_liftE linear0 in hv.
- move=>hz.
  exists (fun i:'I_0=>subspace_lift (subspace_zero (range_subspace (hom_as_linear L)))).
  apply: finite_basis_criterion.
  + move=>c hc i; by have := ltn_ord i; rewrite ltn0.
  + move=>u; exists (fun _=>0); rewrite big_ord0.
    apply: (@subspace_val_injective K Y (range_subspace (hom_as_linear L))).
    have [x hx] := subspace_valP u.
    change (subspace_val u=L x) in hx.
    by rewrite linear0 hx hz.
Qed.
