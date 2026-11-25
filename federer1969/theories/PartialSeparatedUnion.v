(** Federer (1969), 3.2.14, p. 252: supporting
    the union of two rectifiable sets. Two bounded
    Lipschitz graphs with positively separated source
    domains have a bounded Lipschitz union graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology lra.
From Federer Require Import PartialFunctionUP PartialMetricLipschitz
  CoveringFamilyUP MetricBoundedUnion PartialLipschitzBoundedImage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_separated_union_exists]: the
    separated-parameter gluing supporting S union T in
    Federer 3.2.14, p. 252. The domain and range are
    the exact unions, not merely supersets. *)
Theorem partial_separated_union_exists (R : realType)
    (X Y : metricType R) (f g : partial_function X Y)
    (L M d : R) :
  is_partial_metric_lipschitz_bound f L ->
  is_partial_metric_lipschitz_bound g M ->
  metric_set_bounded (partial_function_domain f) ->
  metric_set_bounded (partial_function_domain g) -> 0<d ->
  (forall x y, partial_function_domain f x -> partial_function_domain g y -> d<=mdist x y) ->
  exists h : partial_function X Y,
    partial_function_domain h=partial_function_domain f `|` partial_function_domain g /\
    partial_function_range h=partial_function_range f `|` partial_function_range g /\
    exists C, is_partial_metric_lipschitz_bound h C.
Proof.
move=> hf hg hfb hgb hd hsep.
have hdis x : partial_function_domain f x -> partial_function_domain g x -> False.
  move=> hx hy; have hh := hsep x x hx hy; rewrite mdistxx in hh.
  by have := lt_le_trans hd hh; rewrite ltxx.
have hsingle x a b :
    (partial_function_graph f x a \/ partial_function_graph g x a) ->
    (partial_function_graph f x b \/ partial_function_graph g x b) -> a=b.
  move=> [ha|ha] [hb|hb].
  - exact: partial_function_single_valued ha hb.
  - exfalso; apply: (@hdis x); [by exists a|by exists b].
  - exfalso; apply: (@hdis x); [by exists b|by exists a].
  - exact: partial_function_single_valued ha hb.
pose h := @Build_partial_function X Y (fun x y =>
  partial_function_graph f x y \/ partial_function_graph g x y) hsingle.
have hdom : partial_function_domain h=partial_function_domain f `|` partial_function_domain g.
  apply/seteqP; split=> x.
  - move=> [y [hy|hy]]; [left|right]; by exists y.
  - move=> [[y hy]|[y hy]]; exists y; [left|right]; exact hy.
have hrange : partial_function_range h=partial_function_range f `|` partial_function_range g.
  apply/seteqP; split=> y.
  - move=> [x [hx|hx]]; [left|right]; by exists x.
  - move=> [[x hx]|[x hx]]; exists x; [left|right]; exact hx.
exists h; split=> //; split=> //.
case: (pselect (partial_function_range h !=set0))=> [[a ha]|he]; last first.
  exists 0; split; first exact: lexx.
  move=> x y b c hb hc; exfalso; apply: he; exists b; by exists x.
have hb : metric_set_bounded (partial_function_range h).
  rewrite hrange; exact: metric_bounded_union
    (partial_lipschitz_bounded_image hf hfb) (partial_lipschitz_bounded_image hg hgb).
have [r [hr hbound]] := metric_bounded_distance_bound a hb.
pose B := r+r.
have hB : 0<=B by rewrite /B; exact: (addr_ge0 hr hr).
have hq : 0<=B/d := divr_ge0 hB (ltW hd).
pose C := L+M+B/d.
have hC : 0<=C := addr_ge0 (addr_ge0 hf.1 hg.1) hq.
have hLC : L<=C by rewrite /C; have := hg.1; lra.
have hMC : M<=C by rewrite /C; have := hf.1; lra.
have hqC : B/d<=C by rewrite /C; have := hf.1; have := hg.1; lra.
have hcross x y b c : partial_function_graph f x b -> partial_function_graph g y c ->
    mdist b c<=C*mdist x y.
  move=> hxb hyc.
  have hbr : mdist a b<=r by apply: hbound; exists x; by left.
  have hcr : mdist a c<=r by apply: hbound; exists y; by right.
  have hbc : mdist b c<=B.
    have ht := metric_triangle b a c; rewrite (metric_sym b a) in ht.
    exact: le_trans ht (lerD hbr hcr).
  have hxy : d<=mdist x y by apply: hsep; [by exists b|by exists c].
  have hBd : B<=(B/d)*mdist x y.
    have hh := ler_wpM2l hq hxy; by rewrite divfK ?gt_eqF in hh.
  exact (le_trans hbc (le_trans hBd (ler_wpM2r (mdist_ge0 x y) hqC))).
exists C; split=> // x y b c [hxb|hxb] [hyc|hyc].
- exact: le_trans (hf.2 x y b c hxb hyc) (ler_wpM2r (mdist_ge0 x y) hLC).
- exact: hcross x y b c hxb hyc.
- rewrite (metric_sym b c) (metric_sym x y); exact: hcross y x c b hyc hxb.
- exact: le_trans (hg.2 x y b c hxb hyc) (ler_wpM2r (mdist_ge0 x y) hMC).
Qed.
