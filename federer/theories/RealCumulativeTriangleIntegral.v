(** Federer (1969), 2.6.7, printed p. 121: the two evaluations of the
    measure of S = {a <= x < y <= b}. The half-line values are finite only
    on [a,b]; no finiteness of either whole measure is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureIntegralUP
  MeasureIntegralGraphEquivalence SummableRealFunctionUP PartialFunctionBasic
  CountablyMeasurableBasic ProductMeasure ProductSections ProductRectangleValue
  ProductSetFubini RealOrderTriangle FiniteMeasureSetDifference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [lower_open_interval_measure]: alpha[a,b) =
    f(b)-f(a), the strict lower-half-line convention in
    Federer 2.6.7, p. 121. The endpoint a may carry an atom. *)
Lemma lower_open_interval_measure (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu) (a b u v : R) :
  a <= b -> measure_measurable mu [set x | x < a] ->
  mu [set x | x < a]=u%:E -> mu [set x | x < b]=v%:E ->
  mu [set x | a <= x /\ x < b]=(v-u)%:E.
Proof.
move=> hab hA hu hv.
have he : [set x | a <= x /\ x < b]=[set x | x < b] `\` [set x | x < a].
  apply/seteqP; split=> x.
  - move=> [hax hxb]; split=> //; apply/negP; by rewrite -leNgt.
  - move=> [hxb /negP hxa]; split=> //; by rewrite leNgt.
rewrite he; apply: (@finite_measure_nested_difference R R mu hm _ _ u v hA _ hu hv).
move=> x hx; exact: lt_le_trans hx hab.
Qed.

(** Source for [lower_closed_interval_measure]: beta(a,b] =
    g(b)-g(a), the closed lower-half-line convention in
    Federer 2.6.7, p. 121. The endpoint b may carry an atom. *)
Lemma lower_closed_interval_measure (R : realType)
    (mu : set R -> \bar R) (hm : is_measure mu) (a b u v : R) :
  a <= b -> measure_measurable mu [set x | x <= a] ->
  mu [set x | x <= a]=u%:E -> mu [set x | x <= b]=v%:E ->
  mu [set x | a < x /\ x <= b]=(v-u)%:E.
Proof.
move=> hab hA hu hv.
have he : [set x | a < x /\ x <= b]=[set x | x <= b] `\` [set x | x <= a].
  apply/seteqP; split=> x.
  - move=> [hax hxb]; split=> //; apply/negP; by rewrite -ltNge.
  - move=> [hxb /negP hxa]; split=> //; by rewrite ltNge.
rewrite he; apply: (@finite_measure_nested_difference R R mu hm _ _ u v hA _ hu hv).
move=> x hx; exact: le_trans hx hab.
Qed.

Section Triangle.
Variable R : realType.
Variable alpha beta : set R -> \bar R.
Hypothesis ha : is_measure alpha.
Hypothesis hb : is_measure beta.
Hypothesis hAr : forall t, measure_measurable alpha [set x | x < t].
Hypothesis hBr : forall t, measure_measurable beta [set x | x <= t].
Variable a b : R.
Hypothesis hab : a <= b.
Variable f g : R -> R.
Hypothesis hf : forall r, a <= r -> r <= b -> alpha [set x | x < r]=(f r)%:E.
Hypothesis hg : forall r, a <= r -> r <= b -> beta [set x | x <= r]=(g r)%:E.

(** Source for [cumulative_triangle_horizontal_measure]: the
    inner integral f(y)-f(a) in the first application of
    Fubini in Federer 2.6.7, p. 121, and zero outside (a,b]. *)
Lemma cumulative_triangle_horizontal_measure (y : R) :
  alpha (product_horizontal_section (real_order_triangle a b) y)=
    (if (a < y) && (y <= b) then f y-f a else 0)%:E.
Proof.
rewrite real_order_triangle_horizontal; case: ifP=> [/andP [hay hyb]|_].
- exact (@lower_open_interval_measure R alpha ha a y (f a) (f y)
    (ltW hay) (hAr a) (@hf a (lexx _) hab) (@hf y (ltW hay) hyb)).
- exact: measure_empty ha.
Qed.

(** Source for [cumulative_triangle_vertical_measure]: the
    inner integral g(b)-g(x) in the second application of
    Fubini in Federer 2.6.7, p. 121, and zero outside [a,b). *)
Lemma cumulative_triangle_vertical_measure (x : R) :
  beta (product_vertical_section (real_order_triangle a b) x)=
    (if (a <= x) && (x < b) then g b-g x else 0)%:E.
Proof.
rewrite real_order_triangle_vertical; case: ifP=> [/andP [hax hxb]|_].
- exact (@lower_closed_interval_measure R beta hb x b (g x) (g b)
    (ltW hxb) (hBr x) (@hg x hax (ltW hxb)) (@hg b hab (lexx _))).
- exact: measure_empty hb.
Qed.

(** Source for [cumulative_triangle_fubini]: the two displayed
    repeated-integral equations for (alpha times beta)(S), Federer
    2.6.7, p. 121. Both are actual finite integrals. This
    supporting theorem needs only measurable half-lines and the
    specified finite cumulative values, which the Radon hypotheses supply. *)
Theorem cumulative_triangle_fubini :
  exists s : R,
    is_measure_integral beta
      (real_total_integrand (fun y => if (a < y) && (y <= b) then f y-f a else 0)) s%:E /\
    is_measure_integral alpha
      (real_total_integrand (fun x => if (a <= x) && (x < b) then g b-g x else 0)) s%:E.
Proof.
pose S := real_order_triangle a b.
pose A := [set x | a <= x /\ x < b].
pose B := [set y | a < y /\ y <= b].
have hA := lower_open_rays_left_interval ha hAr a b.
have hB := lower_closed_rays_right_interval hb hBr a b.
have hAvalue := @lower_open_interval_measure R alpha ha a b (f a) (f b)
  hab (hAr a) (@hf a (lexx _) hab) (@hf b hab (lexx _)).
have hBvalue := @lower_closed_interval_measure R beta hb a b (g a) (g b)
  hab (hBr a) (@hg a (lexx _) hab) (@hg b hab (lexx _)).
have hprod := product_measure_is_measure ha hb.
have hSm := real_order_triangle_measurable ha hb a b hAr hBr.
have hSfin : (product_measure ha hb S < +oo)%E.
  have hle := measure_mono hprod (@real_order_triangle_rectangle_bound R a b).
  have hval := @product_measure_rectangle_value R R R alpha beta ha hb A B hA hB.
  rewrite hAvalue hBvalue -EFinM in hval.
  rewrite hval in hle; exact: le_lt_trans hle (ltry _).
have hSnum : product_measure ha hb S \is a fin_num.
  by rewrite (ge0_fin_numE (measure_nonnegative hprod S)).
have hSc := finite_measurable_set_countably_measurable hSm hSfin.
have [_ [_ [hi hj]]] := @product_set_fubini R R R alpha beta ha hb S hSc.
exists (fine (product_measure ha hb S)); rewrite fineK //; split.
- apply: (measure_integral_graph_equivalent _ hj)=> y z.
  rewrite real_total_integrand_graph.
  change (alpha (product_horizontal_section S y)=z <->
    (if (a < y) && (y <= b) then f y-f a else 0)%:E=z).
  by rewrite cumulative_triangle_horizontal_measure.
- apply: (measure_integral_graph_equivalent _ hi)=> x z.
  rewrite real_total_integrand_graph.
  change (beta (product_vertical_section S x)=z <->
    (if (a <= x) && (x < b) then g b-g x else 0)%:E=z).
  by rewrite cumulative_triangle_vertical_measure.
Qed.
End Triangle.
