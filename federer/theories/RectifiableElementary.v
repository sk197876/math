(** Federer (1969), 3.2.14, pp. 251–252:
    elementary consequences of the four rectifiability
    definitions and the explicit zero-dimensional convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  PartialFunctionUP PartialFunctionBasic
  PartialFunctionSourceRestriction PartialMetricLipschitz RectifiableSetUP
  MetricBoundedClosureLaws MetricDiameterUP MetricDiameter CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [zero_rectifiable_finite]: the final
    convention of Federer 3.2.14, p. 252: zero
    rectifiable means finite, rather than a singleton image. *)
Lemma zero_rectifiable_finite (R : realType) (X : metricType R) (E : set X) :
  is_m_rectifiable 0 E <-> finite_set E.
Proof. by []. Qed.

(** Source for [rectifiable_empty]: the empty image
    boundary of Federer 3.2.14(1), p. 251, with
    the zero-dimensional convention of p. 252. *)
Lemma rectifiable_empty (R : realType) (X : metricType R) m :
  is_m_rectifiable m (@set0 X).
Proof.
case: m=> [|m]; first exact: finite_set0.
exists (@partial_function_empty
  (inner_metric_space (@euclidean_inner_productP R m.+1)) X).
split; first by rewrite partial_function_empty_domain; exact: metric_bounded_empty.
split.
- exists 0; split; first exact: lexx; by move=> x y a b [].
- apply/seteqP; split=> y; first by move=> [x []].
  by move=> [].
Qed.

(** Source for [rectifiable_subset]: restricting the
    parametrization in Federer 3.2.14(1), p. 251,
    gives a parametrization of every subset of its image. *)
Lemma rectifiable_subset (R : realType) (X : metricType R) m
    (E F : set X) : F `<=` E -> is_m_rectifiable m E -> is_m_rectifiable m F.
Proof.
move=> hFE; case: m=> [|m]; first exact: sub_finite_set hFE.
move=> [f [hb [[L hL] hr]]].
pose g := partial_function_source_restrict (partial_function_preimage f F) f.
exists g; split.
- apply: (metric_bounded_subset _ hb)=> x [y [_ hy]]; by exists y.
- split.
  + exists L; split; first exact: hL.1.
    move=> x y a b [_ ha] [_ hy]; exact: hL.2 x y a b ha hy.
  + apply/seteqP; split.
    * move=> y [x [[z [hz hFz]] hy]].
      have he : z=y := partial_function_single_valued hz hy.
      by rewrite -he.
    * move=> y hy.
      have hEy : partial_function_range f y by rewrite hr; exact: hFE y hy.
      have [x hx] := hEy; exists x; split=> //; by exists y; split.
Qed.

(** Source for [rectifiable_countably_rectifiable]: a
    one-member family in Federer 3.2.14(2), p. 251. *)
Lemma rectifiable_countably_rectifiable (R : realType) (X : metricType R) m (E : set X) :
  is_m_rectifiable m E -> is_countably_m_rectifiable m E.
Proof.
move=> hE; exists [set E]; split; first exact: countable1.
split; first by move=> F ->.
by rewrite bigcup_set1.
Qed.

(** Source for [countably_rectifiable_empty]: the empty
    family in Federer 3.2.14(2), p. 251. *)
Lemma countably_rectifiable_empty (R : realType) (X : metricType R) m :
  is_countably_m_rectifiable m (@set0 X).
Proof. exact: (@rectifiable_countably_rectifiable R X m set0 (@rectifiable_empty R X m)). Qed.

(** Source for [countably_rectifiable_subset]: image
    restrictions and the countable family in Federer
    3.2.14(1)–(2), p. 251. *)
Lemma countably_rectifiable_subset (R : realType) (X : metricType R) m
    (E F : set X) : F `<=` E -> is_countably_m_rectifiable m E ->
  is_countably_m_rectifiable m F.
Proof.
move=> hFE [C [hc [hC hr]]].
exists ((fun G : set X => G `&` F) @` C); split; first exact: sub_countable (card_image_le _ _) hc.
split.
- move=> G [H hH <-]; exact: (@rectifiable_subset R X m H (H `&` F) (fun x hx => hx.1) (hC H hH)).
- apply/seteqP; split.
  + move=> x hx.
    have hEx : (\bigcup_(G in C) G) x by rewrite -hr; exact: hFE x hx.
    have [G hG hGx] := hEx; exists (G `&` F); first by exists G.
    by split.
  + by move=> x [G [H hH <-] [_ hx]].
Qed.
