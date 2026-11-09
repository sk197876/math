(** Federer (1969), 3.4.1, p. 310: actual differential image dimensions
    exist for arbitrary normed targets because the source is finite dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Bilinear Hom ModuleQuotient SubspaceSums SubspaceCarrier FiniteIndependence
  FiniteBasisComparison FiniteBasisCriterion FiniteDimension BoundedIndependentBasis
  LinearBasis FiniteSpans FiniteCoordinates LinearRangeBasis LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [finite_source_linear_rank_exists]: supporting the actual
    dim im Df used in 3.4.1, p. 310, with arbitrary normed Y. An arbitrary
    linear map out of a space with a finite basis has a finite-dimensional
    actual range, bounded by the source dimension. Lift each finite
    independent range family locally and apply the basis-size result of
    1.6.1, pp. 23–24. No target basis or global choice of image basis is assumed. *)
Theorem finite_source_linear_rank_exists (K:fieldType) (X Y:lmodType K)
    (L:Hom X Y) m (b:'I_m->X) (hb:is_basis b):
  exists r,has_linear_rank L r /\(r<=m)%N.
Proof.
pose U:=subspace_space (range_subspace (hom_as_linear L)).
have hBound r (e:'I_r->U):finite_independent e ->(r<=m)%N.
  move=>he.
  have hex i:exists x:X,L x=subspace_val (e i).
    have [x hx]:=subspace_valP (e i);by exists x.
  pose d i:X:=projT1 (cid (hex i)).
  have hd i:L (d i)=subspace_val (e i) by rewrite /d;case:(cid (hex i)).
  have hi:finite_independent d.
    move=>c hc;apply:he.
    apply:(@subspace_val_injective K Y (range_subspace (hom_as_linear L))).
    rewrite linear_sum linear0.
    have hL:=congr1 L hc;rewrite linear_sum linear0 in hL.
    have hs:(\sum_i L (c i*:d i))=\sum_i c i*:subspace_val (e i).
      apply:eq_bigr=>i _.
      exact:(eq_trans (linZ (hom_linear L) (c i) (d i))
        (congr1 (fun z=>c i*:z) (hd i))).
    rewrite hs in hL.
    under eq_bigr do rewrite linearZ.
    exact:hL.
  have h:=@finite_independent_dimension K (finite_basis_vect hb) r d hi.
  by rewrite finite_basis_dimension card_ord in h.
have [r [e [he hr]]]:=@bounded_independent_basis K U m hBound.
exists r;split;last exact:hr.
by exists e.
Qed.

(** Source for [finite_source_injective_linear_rank]: supporting the
    image dimension in 3.4.1, p. 310. An injective map carries a finite
    source basis to a basis of its range, even in an infinite-dimensional
    target; this uses the basis transfer proved with 1.7.4, p. 31. *)
Lemma finite_source_injective_linear_rank (K:fieldType) (X Y:lmodType K)
    (L:Hom X Y) m (b:'I_m->X) (hb:is_basis b):
  injective L ->has_linear_rank L m.
Proof.
move=>hL.
exact:(injective_range_basis_exists hL hb).
Qed.
