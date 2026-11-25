(** Federer (1969), 3.1.18, p. 229: rank at least v is witnessed by
    independent images of v vectors. This is the linear algebra behind
    the exterior-power test and the open rank superlevel sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom ModuleQuotient SubspaceSums SubspaceCarrier SubspaceFamilies
  FiniteIndependence FiniteBasisComparison FiniteBasisCriterion FiniteDimension
  FiniteDualDimension Annihilator LinearBasis LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [linear_rank_at_least]: supporting the rank threshold
    in Federer 3.1.18, p. 229, by independent images of vectors. *)
Definition linear_rank_at_least (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) v :=
  exists e : 'I_v->X, finite_independent (fun i=>L (e i)).

(** Source for [linear_rank_at_leastP]: independent images characterize
    v<=dim im L, supporting the first display of 3.1.18, p. 229. *)
Lemma linear_rank_at_leastP (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) r v : has_linear_rank L r ->
  (linear_rank_at_least L v <-> (v<=r)%N).
Proof.
move=>[b hb]; split.
- move=>[e he].
  have hmem i : range_subspace (hom_as_linear L) (L (e i)) by exists (e i).
  have hi := @subspace_family_independent K Y (range_subspace (hom_as_linear L))
    (Finite.clone 'I_v _) (fun i=>L (e i)) hmem he.
  have h := @finite_independent_dimension K (finite_basis_vect hb) v
    (subspace_family hmem) hi.
  by rewrite finite_basis_dimension card_ord in h.
- move=>hvr.
  pose t i := b (widen_ord hvr i).
  have hex i : exists x:X, L x=subspace_val (t i).
    have [x hx] := subspace_valP (t i); by exists x.
  pose e i := projT1 (cid (hex i)).
  have hE i : L (e i)=subspace_val (t i) by rewrite /e; case: (cid (hex i)).
  exists e.
  have ht : finite_independent t.
    apply: (@finite_independent_separating K (Finite.clone 'I_v _)
      (subspace_space (range_subspace (hom_as_linear L))) t
      (fun i=>hom_as_linear (dual_basis hb (widen_ord hvr i))))=>i j.
    change (dual_basis hb (widen_ord hvr i) (b (widen_ord hvr j)) =
      if i==j then 1 else 0).
    rewrite dual_basisE eq_sym.
    have hinj : injective (@widen_ord v r hvr).
      move=>x y h; apply: val_inj; exact (congr1 (fun z:'I_r=>(z:nat)) h).
    by rewrite (inj_eq hinj).
  have hi := @finite_independent_map K (Finite.clone 'I_v _)
    (subspace_space (range_subspace (hom_as_linear L))) Y
    (subspace_inclusion _) t (@subspace_val_injective K Y (range_subspace (hom_as_linear L))) ht.
  move=>c hc; apply: hi.
  have hs : (\sum_i c i*:subspace_val (t i))=\sum_i c i*:L (e i).
    apply: eq_bigr=>i _; by rewrite hE.
  by rewrite hs.
Qed.

(** Source for [linear_rank_zero_threshold]: every linear map has
    rank at least zero, including zero-dimensional spaces. Supporting
    the nonnegative-integer convention of 3.1.18, p. 229. *)
Lemma linear_rank_zero_threshold (K : fieldType) (X Y : lmodType K)
    (L : Hom X Y) : linear_rank_at_least L 0%N.
Proof.
exists (fun _:'I_0=>(0:X)); move=>c hc i.
by have := ltn_ord i; rewrite ltn0.
Qed.
