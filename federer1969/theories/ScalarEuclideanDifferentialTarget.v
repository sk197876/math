(** Federer (1969), 3.2.13, p. 250: the
    scalar norm map is represented in the one-coordinate
    Euclidean target for the coarea theorem. This
    is an exact differential adapter, not a new calculus assumption. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct EuclideanOneCoordinate
  EuclideanOneNormDifferential NormDifferentialUP InnerNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_euclidean_target_hom]: prescribed
    linear identification of a scalar differential's target
    with R^1, supporting the norm differential in
    Federer 3.2.13, p. 250. *)
Definition scalar_euclidean_target_hom (R:realType) (X:lmodType R)
    (L:Hom X R^o):Hom X (R_n R 1).
Proof.
apply:(@HomMap R X (R_n R 1) (fun x=>euclidean_one_embed (L x))).
apply/asboolP=>c x y; apply/ffunP=>i.
change (euclidean_one_embed (L (c*:x+y)) i=
  (c*:euclidean_one_embed (L x)+euclidean_one_embed (L y)) i).
by rewrite /euclidean_one_embed !ffunE linearD linearZ.
Defined.

(** Source for [scalar_euclidean_target_differential]:
    exact target identification for the actual norm
    differential in Federer 3.2.13, p. 250.
    No property of the source beyond its given differential is added. *)
Lemma scalar_euclidean_target_differential (R:realType) (X:lmodType R)
    (NX:X->R) (A:set X) (f:X->R) a (L:Hom X R^o):
  has_norm_differential NX (fun r:R^o=>`|r|) A f a L ->
  has_norm_differential NX (inner_norm (@euclidean_inner_productP R 1)) A
    (fun x=>euclidean_one_embed (f x)) a (scalar_euclidean_target_hom L).
Proof.
move=>hD; constructor; first exact:norm_differential_interior hD.
- have [C [hC hBound]]:=norm_differential_bounded hD.
  exists C; split=>// x.
  rewrite euclidean_one_norm_coordinate.
  change (`|euclidean_one_embed (L x) ord0|<=C*NX x).
  by rewrite /euclidean_one_embed ffunE; exact:hBound.
- move=>e he; have [d [hd hRest]]:=norm_differential_remainder hD he.
  exists d; split=>// h ha hh.
  rewrite euclidean_one_norm_coordinate.
  change (`|(euclidean_one_embed (f (a+h))-euclidean_one_embed (f a)-
    euclidean_one_embed (L h)) ord0|<=e*NX h).
  by rewrite /euclidean_one_embed !ffunE; exact:hRest h ha hh.
Qed.
