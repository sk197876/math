(** Federer (1969), 3.3.6, p. 293: the original
    narrow-cone-free remainder has zero outer measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeAvoidance StructureConeAvoidanceTheorem
  RectifiableSetUP PureUnrectifiableLaws PureCountablyRectifiableNull MeasureUP MeasureBasic MeasureSplit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_active_cone_points]: the original set C
    in Federer 3.3.6, p. 293: x belongs to B and the original
    infinite-radius narrow cone from x contains an original B point. *)
Definition structure_active_cone_points (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e:R):=
  B `&` [set x | exists y,
    (B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y].

(** Source for [structure_cone_free_remainder_null]: the application
    of 3.3.5 and pure unrectifiability in Federer 3.3.6, p. 293.
    Original B and C need not be measurable; no finite mass is assumed. *)
Theorem structure_cone_free_remainder_null (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e:R):
  is_purely_measure_m_unrectifiable phi m A ->B `<=` A ->0<e<1 ->
  phi (B `\` structure_active_cone_points hmn B p e)= 0%E.
Proof.
move=>hPure hBA he.
pose C:=structure_active_cone_points hmn B p e.
have hAvoid:is_structure_cone_avoiding hmn (B `\` C) p +oo e.
  move=>x [hx hNot]; apply/seteqP; split; last by move=>y [].
  move=>y [[hy _] hCone]; exfalso; apply:hNot.
  split; first exact:hx.
  exists y; by split.
have hRect:=(@federer_3_3_5 R n m hmn (B `\` C) p +oo e (@ltry R 0) he hAvoid).2.
apply:(pure_countably_rectifiable_subset_null hPure _ hRect).
move=>x [hx _]; exact:hBA x hx.
Qed.

(** Source for [structure_active_cone_mass]: the equality phi(B)=phi(C)
    in Federer 3.3.6, p. 293. The outer-measure cover law and monotonicity
    suffice after the actual remainder is null; neither set is replaced
    by a measurable hull. Infinite outer mass is retained. *)
Theorem structure_active_cone_mass (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))-> \bar R)
    (A B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e:R):
  is_purely_measure_m_unrectifiable phi m A ->B `<=` A ->0<e<1 ->
  phi B=phi (structure_active_cone_points hmn B p e).
Proof.
move=>hPure hBA he.
have [hm _]:=(@pure_unrectifiable_iff_rectifiable_subsets_null R _ phi m A).1 hPure.
have hZero:=structure_cone_free_remainder_null hmn p hPure hBA he.
apply/eqP; rewrite eq_le; apply/andP; split.
- have hCover:B `<=` structure_active_cone_points hmn B p e `|`
      (B `\` structure_active_cone_points hmn B p e).
    move=>x hx; case:(pselect (structure_active_cone_points hmn B p e x))=>[hYes|hNo]; first by left.
    right; by split.
  have hBound:=measure_binary_cover hm hCover.
  by rewrite hZero adde0 in hBound.
- apply:(@measure_mono R _ phi hm _ _)=>x [hx _]; exact:hx.
Qed.
