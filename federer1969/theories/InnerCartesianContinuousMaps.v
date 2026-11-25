(** Federer (1969), 3.2.48, p. 286: continuity for the original
    Cartesian inner metric used by the source action. Supporting topology
    of 1.7.1, p. 28, and 1.7.11, p. 36; the specified inner metric
    is retained rather than replaced by an unrelated product metric. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  topology tvs num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm InnerMetric InnerNormedTopology
  ProductInner ProductInnerNormBounds ProductInnerPairRegularity RealNormUP NormDifferentialUP
  NormMetricScaleContinuity TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [inner_bounded_linear_continuous]: a finite actual
    norm bound gives continuity in the specified inner metrics, by
    1.7.1, p. 28, supporting the action in 3.2.48, p. 286. *)
Lemma inner_bounded_linear_continuous (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW) (L:Hom V W):
  norm_bounded_linear (inner_norm hV) (inner_norm hW) L ->
  continuous (fun x:inner_metric_space hV=>(L x:inner_metric_space hW)).
Proof.
move=>[C [hC hBound]].
apply:(@metric_fixed_lipschitz_continuous R (inner_metric_space hV) (inner_metric_space hW)
  (fun x=>L x) C hC).
move=>x y; rewrite !inner_metric_distanceE.
change (is_true (inner_norm hW (L x-L y)<=C*inner_norm hV (x-y))).
by rewrite -linearB; exact (hBound (x-y)).
Qed.

(** Source for [inner_cartesian_projections_continuous]: the actual
    Cartesian projections are continuous contractions, supporting the
    source action in 3.2.48, p. 286, by 1.7.11, p. 36. *)
Theorem inner_cartesian_projections_continuous (R:realType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW):
  continuous (fun z:inner_metric_space (product_inner_productP hV hW)=>(z.1:inner_metric_space hV)) /\
  continuous (fun z:inner_metric_space (product_inner_productP hV hW)=>(z.2:inner_metric_space hW)).
Proof.
split.
- apply:(@inner_bounded_linear_continuous R [the lmodType R of (V*W)%type] V
    _ BV (product_inner_productP hV hW) hV (@product_first_projection_hom R V W)).
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_first_norm_bound hV hW z).
- apply:(@inner_bounded_linear_continuous R [the lmodType R of (V*W)%type] W
    _ BW (product_inner_productP hV hW) hW (@product_second_projection_hom R V W)).
  exists 1; split; first exact:ler01.
  by move=>z; rewrite mul1r; exact (product_inner_second_norm_bound hV hW z).
Qed.

(** Source for [inner_cartesian_pair_continuous]: continuous factor
    maps give a continuous pair for the specified Cartesian inner metric,
    supporting the source action in 3.2.48, p. 286. The two actual
    isometric inclusions and continuity of addition prove the result. *)
Theorem inner_cartesian_pair_continuous (R:realType) (S:topologicalType) (V W:lmodType R)
    BV BW (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    (f:S->inner_metric_space hV) (g:S->inner_metric_space hW):
  continuous f ->continuous g ->
  continuous (fun s=>(f s,g s):inner_metric_space (product_inner_productP hV hW)).
Proof.
move=>hf hg.
pose P:=inner_metric_space (product_inner_productP hV hW).
pose i:=@product_first_injection_hom R V W.
pose j:=@product_second_injection_hom R V W.
have hi:continuous (fun x:inner_metric_space hV=>(i x:P)).
  apply:(@inner_bounded_linear_continuous R V [the lmodType R of (V*W)%type]
    BV _ hV (product_inner_productP hV hW) i).
  exists 1; split; first exact:ler01.
  by move=>x; rewrite (@product_first_injection_norm R V W BV BW hV hW) mul1r.
have hj:continuous (fun x:inner_metric_space hW=>(j x:P)).
  apply:(@inner_bounded_linear_continuous R W [the lmodType R of (V*W)%type]
    BW _ hW (product_inner_productP hV hW) j).
  exists 1; split; first exact:ler01.
  by move=>x; rewrite (@product_second_injection_norm R V W BV BW hV hW) mul1r.
have hLeft:continuous (fun s:S=>(i (f s):P)) by move=>s; exact (continuous_comp (hf s) (hi (f s))).
have hRight:continuous (fun s:S=>(j (g s):P)) by move=>s; exact (continuous_comp (hg s) (hj (g s))).
have hPair:=topological_pair_continuous hLeft hRight.
have hAdd:continuous (fun z:P*P=>z.1+z.2):=add_continuous.
have hSum:continuous (fun s:S=>(i (f s)+j (g s):P)).
  move=>s; exact (continuous_comp (hPair s) (hAdd (i (f s),j (g s)))).
have hEqual:(fun s:S=>(f s,g s):P)=(fun s:S=>(i (f s)+j (g s):P)).
  apply:funext=>s; change ((f s,g s)=(f s+0,0+g s)).
  by rewrite addr0 add0r.
by rewrite hEqual.
Qed.
