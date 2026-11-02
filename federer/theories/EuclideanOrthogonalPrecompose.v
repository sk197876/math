(** Federer (1969), 3.2.21, p. 257: composing
    with orthogonal source coordinates preserves the Lipschitz bound,
    transforms every actual differential by composition, and preserves
    null Lebesgue mass. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric OrthogonalMaps LipschitzUP NormDifferentialUP NormDifferentialLinear
  EuclideanLebesgueDimensions EuclideanLebesgueLinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_orthogonal_precompose_lipschitz]:
    the map v composed with g in Federer 3.2.21,
    p. 257, has the same Lipschitz bound as v. *)
Lemma euclidean_orthogonal_precompose_lipschitz (R:realType) m n
    (v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (s:Hom (R_n R m) (R_n R m)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) (hom_as_linear s) ->
  is_metric_lipschitz setT v ->
  @is_metric_lipschitz R [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT (fun x=>v (s x)).
Proof.
move=>hS [L [hL hBound]]; exists L; split; first exact hL.
split; first exact hBound.1; move=>x y _ _.
have h:=hBound.2 (s x) (s y) Logic.I Logic.I.
rewrite !inner_metric_distanceE -[s x-s y]linearB /=
  (orthogonal_map_norm (@euclidean_inner_productP R m) (@euclidean_inner_productP R m) hS) in h.
exact h.
Qed.

(** Source for [euclidean_orthogonal_precompose_differential]:
    D(v composed with g)(x)=Dv(g(x)) composed with g in
    Federer 3.2.21, p. 257, at every actual
    differentiability point. No derivative field is assumed. *)
Lemma euclidean_orthogonal_precompose_differential (R:realType) m n
    (v:R_n R m->R_n R n) (s:Hom (R_n R m) (R_n R m)) x
    (D:Hom (R_n R m) (R_n R n)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) (hom_as_linear s) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT v (s x) D ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT (fun y=>v (s y)) x (hom_comp D s).
Proof.
move=>hS hD.
have hSN:norm_bounded_linear (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) s.
  exists 1; split; first exact:ler01.
  move=>h; rewrite (orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R m) hS) mul1r; exact:lexx.
constructor.
- exists 1; split; first exact:ltr01; by move=>h hh.
- exact:(norm_bounded_linear_compose hSN (norm_differential_bounded hD)).
- move=>e he; have [r [hr hRem]]:=norm_differential_remainder hD he.
  exists r; split; first exact hr; move=>h _ hh.
  have hSmall:inner_norm (@euclidean_inner_productP R m) (s h)<r.
    by rewrite (orthogonal_map_norm (@euclidean_inner_productP R m)
      (@euclidean_inner_productP R m) hS).
  have hValue:=hRem (s h) Logic.I hSmall.
  rewrite (orthogonal_map_norm (@euclidean_inner_productP R m)
    (@euclidean_inner_productP R m) hS) in hValue.
  by rewrite linearD /=; exact hValue.
Qed.

(** Source for [euclidean_orthogonal_image_null]: the identity
    A=g of the rotated set in Federer 3.2.21,
    p. 257, preserves its Lebesgue-null mass.
    This holds for every subset, without a measurability premise. *)
Lemma euclidean_orthogonal_image_null (R:realType) m
    (s:Hom (R_n R m) (R_n R m)) (A:set (R_n R m)):
  is_orthogonal_map (@euclidean_inner_product R m) (@euclidean_inner_product R m) (hom_as_linear s) ->
  @euclidean_lebesgue_measure R m A=0%E ->
  @euclidean_lebesgue_measure R m (s @` A)=0%E.
Proof.
move=>hS hA.
have hInj:=orthogonal_map_injective (@euclidean_inner_productP R m)
  (@euclidean_inner_productP R m) hS.
have hPre:s @^-1` (s @` A)=A.
  apply/seteqP; split=>x.
  - move=>[y hy hEq]; have hxy:=hInj y x hEq; by rewrite -hxy.
  - move=>hx; by exists x.
have h:=euclidean_orthogonal_pushforward hS (s @` A).
by rewrite hPre hA in h; exact:esym h.
Qed.
