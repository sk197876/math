(** Federer (1969), 3.2.13, p. 251: sphere Hausdorff
    measure is invariant under orthogonal maps. Derive all-set
    invariance from both Lipschitz bounds of 2.10.11, p. 176. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps OrthogonalFinite LipschitzUP HausdorffMeasure HausdorffLipschitzImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [orthogonal_euclidean_lipschitz_one]: orthogonal
    maps preserve Euclidean distance, 1.7.2, p. 28, supporting
    Hausdorff invariance in Federer 3.2.13, p. 251. *)
Lemma orthogonal_euclidean_lipschitz_one (R:realType) m (f:{linear R_n R m->R_n R m}):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) f ->
  is_metric_lipschitz_bound setT (f:inner_metric_space (@euclidean_inner_productP R m)->
    inner_metric_space (@euclidean_inner_productP R m)) (1%R:R).
Proof.
move=>hf; split; first exact:ler01.
move=>x y _ _; rewrite !inner_metric_distanceE -linearB
  (orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R m) hf) mul1r.
exact:lexx.
Qed.

(** Source for [hausdorff_orthogonal_image]: invariance of
    every natural-degree Hausdorff measure under orthogonal images,
    2.10.11, p. 176, as used for the sphere in Federer
    3.2.13, p. 251. No measurability premise is needed. *)
Theorem hausdorff_orthogonal_image (R:realType) m k (f:{linear R_n R m->R_n R m})
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k (f @` A)=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k A.
Proof.
move=>hf.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
have [g [hfg [hgf hg]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m
  (@coordinate_basis R m) (@coordinate_basisP R m) f hf.
have hF:=@hausdorff_positive_lipschitz_image_bound R X X f 1%R k ltr01
  (orthogonal_euclidean_lipschitz_one hf) A.
have hG:=@hausdorff_positive_lipschitz_image_bound R X X g 1%R k ltr01
  (orthogonal_euclidean_lipschitz_one hg) (f @` A).
have hImage:g @` (f @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y [z hz <-] <-]; by rewrite hfg.
  - move=>hx; exists (f x); first by exists x.
    exact:hfg.
rewrite hImage expr1n mul1e in hG; rewrite expr1n mul1e in hF.
by apply/eqP; rewrite eq_le hF hG.
Qed.

(** Source for [hausdorff_orthogonal_preimage]: preimage form
    of orthogonal Hausdorff invariance, used to identify the
    sphere measure under O(m) in Federer 3.2.13, p. 251. *)
Corollary hausdorff_orthogonal_preimage (R:realType) m k (f:{linear R_n R m->R_n R m})
    (A:set (inner_metric_space (@euclidean_inner_productP R m))):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k (f @^-1` A)=
    @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R m)) k A.
Proof.
move=>hf.
have [g [hfg [hgf hg]]]:=@orthogonal_endomorphism_inverse_exists R (R_n R m)
  (@euclidean_inner_product R m) (@euclidean_inner_productP R m) m
  (@coordinate_basis R m) (@coordinate_basisP R m) f hf.
have hImage:f @` (f @^-1` A)=A.
  apply/seteqP; split=>x.
  - by move=>[y hy <-].
  - move=>hx; exists (g x); first by rewrite /= hgf.
    exact:hgf.
have h:=@hausdorff_orthogonal_image R m k f (f @^-1` A) hf.
by rewrite hImage in h.
Qed.
