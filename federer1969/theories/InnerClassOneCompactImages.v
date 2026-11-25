(** Federer (1969), 3.2.47(1),(2), p. 283:
    supporting transfer by the actual smooth product charts.
    On a compact part of the original domain, finite local
    Lipschitz refinements transfer genuine rectifiability and nullity
    of arbitrary original subsets. No measurability or whole-patch
    Lipschitz bound is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp finmap
  classical_sets cardinality constructive_ereal topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric NormClassOneUP
  InnerClassOneLipschitzCover LipschitzUP RectifiableSetUP RectifiableElementary
  LipschitzRectifiableImages CompactSubmanifoldRectifiable
  HausdorffMeasure HausdorffRestrictedLipschitz MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [inner_class_one_compact_rectifiable_image]: the
    finite local chart argument underlying 3.2.47(1),
    p. 283. Any genuinely m rectifiable original subset
    of a compact chart domain has genuinely m rectifiable
    image, including the printed finite-set degree-zero convention. *)
Theorem inner_class_one_compact_rectifiable_image (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A K E:set V) (f:V->W) m:
  norm_class_one (inner_norm hB) (inner_norm hC) A f ->
  K `<=` A ->@compact [the topologicalType of inner_metric_space hB] K ->
  E `<=` K ->@is_m_rectifiable R (inner_metric_space hB) m E ->
  @is_m_rectifiable R (inner_metric_space hC) m (f @` E).
Proof.
move=>hf hKA hK hEK hE.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space hC.
have [F [hF hCover]]:=@inner_class_one_compact_lipschitz_cover R V W B C hB hC A K f hf hKA hK.
have hImage:(f @` E:set Y)=\bigcup_(U in [set` F]) (f @` (E `&` U)).
  apply/seteqP; split=>y.
  - move=>[x hx <-]; have [U hU hxU]:=hCover x (hEK x hx).
    exists U; first exact hU.
    exists x; last reflexivity; by split.
  - move=>[U hU [x [hx _] hxy]]; by exists x.
rewrite hImage.
apply:(@rectifiable_finite_indexed_union R Y m [the choiceType of set X] [set` F]
  (fun U=>f @` (E `&` U)) (finite_fset F)).
move=>U hU.
have hUF:U \in F by exact hU.
have hSubset:E `&` U `<=` E by move=>x hx; exact hx.1.
have hRect:=@rectifiable_subset R X m E (E `&` U) hSubset hE.
have hLip:@is_metric_lipschitz R X Y (E `&` U) f.
  have [L [hL hBound]]:=(hF U hUF).2.2.
  exists L; split; first exact hL.
  split; first exact hBound.1.
  move=>x y hx hy; exact:hBound.2 x y hx.2 hy.2.
exact (@rectifiable_lipschitz_image R X Y m (E `&` U) f hLip hRect).
Qed.

(** Source for [inner_class_one_compact_null_image]: the finite
    local Lipschitz refinement underlying 3.2.47(2), p. 283.
    Actual m-dimensional Hausdorff nullity transfers for arbitrary
    original subsets of a compact chart domain, without a
    measurability or finite-mass assumption on the ambient space. *)
Theorem inner_class_one_compact_null_image (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C)
    (A K E:set V) (f:V->W) m:
  norm_class_one (inner_norm hB) (inner_norm hC) A f ->
  K `<=` A ->@compact [the topologicalType of inner_metric_space hB] K ->E `<=` K ->
  @hausdorff_measure R (inner_metric_space hB) m E=0%E ->
  @hausdorff_measure R (inner_metric_space hC) m (f @` E)=0%E.
Proof.
move=>hf hKA hK hEK hE.
pose X:=inner_metric_space hB.
pose Y:=inner_metric_space hC.
pose mu:=@hausdorff_measure R X m.
pose nu:=@hausdorff_measure R Y m.
have hMu:is_measure mu:=@hausdorff_measure_is_measure R X m.
have hNu:is_measure nu:=@hausdorff_measure_is_measure R Y m.
have [F [hF hCover]]:=@inner_class_one_compact_lipschitz_cover R V W B C hB hC A K f hf hKA hK.
have hImage:(f @` E:set Y)=\bigcup_(U in [set` F]) (f @` (E `&` U)).
  apply/seteqP; split=>y.
  - move=>[x hx <-]; have [U hU hxU]:=hCover x (hEK x hx).
    exists U; first exact hU.
    exists x; last reflexivity; by split.
  - move=>[U hU [x [hx _] hxy]]; by exists x.
rewrite hImage; apply:(@measure_null_countable_union R Y [the choiceType of set X]
  nu hNu [set` F] (fun U=>f @` (E `&` U))).
- exact:finite_set_countable (finite_fset F).
- move=>U hU; have hUF:U \in F by exact hU.
  have hNull:mu (E `&` U)=0%E.
    apply:(@measure_null_subset R X mu hMu (E `&` U) E _ hE).
    by move=>x hx; exact hx.1.
  have [L [_ hBound]]:=(hF U hUF).2.2.
  have hEstimate:=@hausdorff_lipschitz_on_bound R X Y U f L m (E `&` U)
    hBound (fun x hx=>hx.2).
  change (@hausdorff_measure R X m (E `&` U)=0%E) in hNull.
  have hZero:((L^+m)%R%:E* @hausdorff_measure R X m (E `&` U)=0)%E.
    exact (eq_trans (congr1 (fun a : \bar R => ((L^+m)%R%:E*a)%E) hNull) (mule0 _)).
  have hEstimateZero:(nu (f @` (E `&` U))<=0)%E.
    exact (eq_ind _ (fun a : \bar R => (nu (f @` (E `&` U))<=a)%E) hEstimate _ hZero).
  clear hEstimate; rename hEstimateZero into hEstimate.
  apply/eqP; by rewrite eq_le hEstimate (measure_nonnegative hNu).
Qed.
