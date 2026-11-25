(** Federer (1969), 2.10.28, p. 193: f[A]=image f is the interval from zero
    to the total mass. For an atomless measure restricted to a nonempty
    compact A, cumulative values at the minimum and maximum are the endpoint
    values. Every value outside A is already attained on A. Continuity then
    gives the whole interval by the intermediate-value theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology num_normedtype pseudometric_normed_Zmodule normed_module lra.
From Federer Require Import RealMetricBackground MeasureUP MeasureBasic MeasureRestriction
  FiniteCumulativeFunctionUP FiniteCumulativeFunctionLaws CompactMaximum CountableOrderIntervals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_real_set_extremes]: supporting
    minimum and maximum of the compact A(m,n)
    in the range argument of 2.10.28, p. 193.
    This is general topology, proved by applying
    the existing compact maximum theorem to x and -x. *)
Lemma compact_real_set_extremes (R : realType) (A : set (real_line_metric R)) :
  A !=set0 -> compact A -> exists a b : R,
    A a /\ A b /\ forall z, A z -> a<=z /\ z<=b.
Proof.
move=> hne hA.
have hid : continuous (fun z : real_line_metric R=>(z : R^o)) by move=> z; exact: cvg_id.
have hneg : continuous (fun z : real_line_metric R=>(-z : R^o)).
  move=> z; exact: continuousN (hid z).
have [b [hb hmax]] := @continuous_compact_maximum R (real_line_metric R) A (fun z=>(z : R^o)) hne hA hid.
have [a [ha hmin]] := @continuous_compact_maximum R (real_line_metric R) A (fun z=>(-z : R^o)) hne hA hneg.
exists a,b; split=> //; split=> // z hz; split; last exact: hmax z hz.
have hh := hmin z hz; by rewrite lerN2 in hh.
Qed.

(** Source for [restricted_cumulative_extreme_values]: supporting
    endpoint values zero and total mass in
    2.10.28, p. 193. Atomlessness is
    necessary at the minimum because the
    cumulative convention uses a closed lower ray. *)
Lemma restricted_cumulative_extreme_values (R : realType) (mu : set R -> \bar R)
    (A : set R) (f : R -> R) (hf : is_finite_cumulative_function (measure_restrict mu A) f)
    (a b c : R) :
  A a -> A b -> (forall z, A z -> a<=z /\ z<=b) ->
  mu [set a]=0%E -> mu A=c%:E -> f a=0 /\ f b=c.
Proof.
move=> ha hb horder hatom hmass.
have hlow : A `&` [set z : R | z<=a]=[set a].
  apply/seteqP; split=> [z [hz hza]|z ->]; last by split=> //; exact: lexx.
  have he : z=a by apply/eqP; rewrite eq_le hza (horder z hz).1.
  by subst z.
have hhigh : A `&` [set z : R | z<=b]=A.
  apply/seteqP; split=> z hz; first exact hz.1.
  split=> //; exact: (horder z hz).2.
split; apply: EFin_inj.
- by rewrite -(hf a) /measure_restrict hlow hatom.
- by rewrite -(hf b) /measure_restrict hhigh hmass.
Qed.

(** Source for [restricted_cumulative_value_on_support]: supporting
    image f subset f[A] in 2.10.28, p. 193.
    If A has a point at most x, its
    greatest such point has the same cumulative
    value. Otherwise use the minimum of A,
    whose value is zero by atomlessness. *)
Theorem restricted_cumulative_value_on_support (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (A : set (real_line_metric R)) (f : R -> R)
    (hf : is_finite_cumulative_function (measure_restrict mu A) f) :
  A !=set0 -> compact A -> (forall a : R, mu [set a]=0%E) ->
  forall x, exists z, A z /\ f z=f x.
Proof.
move=> hne hA hatom x.
case: (pselect (exists z, A z /\ z<=x))=> [hleft|hno].
- pose C := A `&` [set z : R | z<=x].
  have hC : compact C.
    have hclosed : closed ([set z : real_line_metric R | z<=x]).
      exact: order_closed_lower_ray_closed.
    exact (compact_closedI hA hclosed).
  have hCne : C !=set0 by have [z [hz hzx]] := hleft; exists z; split.
  have hid : continuous (fun z : real_line_metric R=>(z : R^o)) by move=> z; exact: cvg_id.
  have [z [hz hmax]] := @continuous_compact_maximum R (real_line_metric R) C
    (fun z=>(z : R^o)) hCne hC hid.
  exists z; split; first exact hz.1.
  have he : A `&` [set w : R | w<=z]=A `&` [set w : R | w<=x].
    apply/seteqP; split=> w [hw hwl]; split=> //.
    + exact: le_trans hwl hz.2.
    + exact: hmax w (conj hw hwl).
  apply: EFin_inj; by rewrite -(hf z) -(hf x) /measure_restrict he.
- have [a [b [ha [hb horder]]]] := @compact_real_set_extremes R A hne hA.
  exists a; split=> //.
  have hlow : A `&` [set z : R | z<=a]=[set a].
    apply/seteqP; split=> [z [hz hza]|z ->]; last by split=> //; exact: lexx.
    have he : z=a by apply/eqP; rewrite eq_le hza (horder z hz).1.
    by subst z.
  have hempty : A `&` [set z : R | z<=x]=set0.
    apply/seteqP; split=> [z [hz hzx]|z []]; apply: hno; exists z; by split.
  apply: EFin_inj.
  by rewrite -(hf a) -(hf x) /measure_restrict hlow hempty (hatom a) (measure_empty hm).
Qed.

(** Source for [restricted_cumulative_full_range]: direct
    f[A]=image f=[0,total mass] in 2.10.28,
    p. 193, for the abstract atomless
    compactly supported cumulative function.
    No surjectivity is assumed in its definition. *)
Theorem restricted_cumulative_full_range (R : realType) (mu : set R -> \bar R)
    (hm : is_measure mu) (A : set (real_line_metric R)) (f : R -> R)
    (hf : is_finite_cumulative_function (measure_restrict mu A) f) (c : R) :
  A !=set0 -> compact A -> (forall a : R, mu [set a]=0%E) -> mu A=c%:E ->
  continuous (f : real_line_metric R -> real_line_metric R) ->
  f @` A=(`[0,c] : set R) /\ f @` setT=(`[0,c] : set R).
Proof.
move=> hne hA hatom hmass hcont.
have [a [b [ha [hb horder]]]] := @compact_real_set_extremes R A hne hA.
have [hfa hfb] := @restricted_cumulative_extreme_values R mu A f hf a b c ha hb horder (hatom a) hmass.
have hab := (horder a ha).2.
have hn := measure_restrict_is_measure hm A.
have htotal : measure_restrict mu A setT=c%:E by rewrite /measure_restrict setIT.
have hbound := @finite_cumulative_function_bounds R _ hn f hf c htotal.
have hc0 : 0<=c by have [h0 hc] := hbound a; lra.
have himage : f @` setT=(`[0,c] : set R).
  apply/seteqP; split=> [y [x _ <-]|y hy].
  - have [hl hr] := hbound x; by rewrite /= in_itv /= hl hr.
  - have /andP[hy0 hyc] : 0<=y<=c by move: hy; rewrite /= in_itv.
    have hseg : {within (`[a,b] : set (real_line_metric R)), continuous f} :=
      continuous_subspaceT hcont.
    have hbounds : Order.min (f a) (f b)<=y<=Order.max (f a) (f b).
      by rewrite hfa hfb min_l ?max_r // hy0 hyc.
    have [x hx hfx] := @IVT R f a b y hab hseg hbounds.
    exists x=> //; exact hfx.
have hsupp : f @` A=f @` setT.
  apply/seteqP; split=> [y [z hz <-]|y [x _ <-]].
  - by exists z.
  - have [z [hz hzx]] := @restricted_cumulative_value_on_support R mu hm A f hf hne hA hatom x.
    by exists z.
by split; [rewrite hsupp | exact himage].
Qed.
