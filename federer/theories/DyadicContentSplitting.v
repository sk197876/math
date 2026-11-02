(** Federer (1969), 2.10.47(1), pp. 204–205: coarse cubes split each finer
    covering content after restriction to a set with null
    coordinate-hyperplane sections. The geometric premises of the abstract
    generator-splitting criterion are proved here from the dyadic coordinate
    laws. Nullity for gamma_i is explicit; the comparison with Hausdorff
    measure is a separate part of the theorem. Source context:
    DyadicCubeGridUP.v and RestrictedCoverSplitting.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  DyadicCubeGridUP DyadicCubeGrid DyadicCubeGridLaws DyadicCubeRefinement DyadicCubeOverlap
  RefiningCoverContent RestrictedCoverSplitting MeasureUP MeasureBasic MeasureRestriction MeasureAlmostBasic FiniteNullOverlapAdditivity NonnegativeSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dyadic_content_cell_measurable]: supporting
    coarse-cell splitting in 2.10.47(1), pp. 204–205.
    Every finer cube has a coarse parent. A different
    coarse cell meets that parent only in a coordinate
    hyperplane, and thus in a null part of D. *)
Theorem dyadic_content_cell_measurable (R : realType) n (a : R_n R n) Q
    (D : set (inner_metric_space (@euclidean_inner_productP R n))) cost i
    (gamma : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) k t :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) cost i gamma ->
  (forall S, refining_cover_tail (dyadic_cube_level Q) i S -> 0<=cost S) ->
  (forall (l : 'I_n) (b : R), gamma (D `&` [set x | x l=b])=0) ->
  (k<=i)%N -> measure_measurable (measure_restrict gamma D) (@Q k t).
Proof.
move=> hQ hg hc hnull hki.
have hm := refining_cover_content_measure hg hc.
apply: (refining_content_cell_measurable_on hg hc)=> T [j [hij [s _ <-]]].
have [u hu] := @dyadic_cube_coarse_parent R n a Q hQ k j (leq_trans hki hij) s.
case: (eqVneq u t)=> [hut|hne].
- rewrite hut in hu; left=> x [_ hx]; exact: hu.
- right; have [l [b hb]] := @dyadic_cube_distinct_overlap_hyperplane R n a Q hQ k u t hne.
  apply: (@measure_null_subset R _ gamma hm _ (D `&` [set x | x l=b])); last exact: hnull.
  move=> x [[hxD hxs] hxt]; split=> //; apply: hb; split=> //; exact: hu.
Qed.

(** Source for [dyadic_content_distinct_overlap_null]: supporting
    null overlaps of distinct coarse cells in 2.10.47(1),
    pp. 204–205, for the restricted content. This
    supplies the finite-additivity hypothesis without
    imposing measurability on the original set D. *)
Theorem dyadic_content_distinct_overlap_null (R : realType) n (a : R_n R n) Q
    (D : set (inner_metric_space (@euclidean_inner_productP R n)))
    (gamma : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) :
  is_dyadic_cube_grid a Q -> is_measure gamma ->
  (forall (l : 'I_n) (b : R), gamma (D `&` [set x | x l=b])=0) ->
  forall k s t, s != t -> measure_restrict gamma D (@Q k s `&` @Q k t)=0.
Proof.
move=> hQ hm hnull k s t hne.
have [l [b hb]] := @dyadic_cube_distinct_overlap_hyperplane R n a Q hQ k s t hne.
apply: (@measure_null_subset R _ gamma hm _ (D `&` [set x | x l=b])); last exact: hnull.
move=> x [hxD hx]; split=> //; exact: hb.
Qed.

(** Source for [dyadic_content_level_additivity]: the finite
    summation of 2.10.47(1), pp. 204–205, once
    the content-nullity of coordinate-hyperplane sections
    has been established. E lies in the initial unit
    cube and k<=i. Compactness of E is not required. *)
Theorem dyadic_content_level_additivity (R : realType) n (a : R_n R n) Q
    (E : set (inner_metric_space (@euclidean_inner_productP R n))) cost i
    (gamma : set (inner_metric_space (@euclidean_inner_productP R n)) -> \bar R) k :
  is_dyadic_cube_grid a Q ->
  is_refining_cover_content (dyadic_cube_level Q) cost i gamma ->
  (forall S, refining_cover_tail (dyadic_cube_level Q) i S -> 0<=cost S) ->
  (forall (l : 'I_n) (b : R), gamma (E `&` [set x | x l=b])=0) ->
  (forall x, E x -> forall l, (a l<=x l<=a l+1)%R) -> (k<=i)%N ->
  gamma E=nonnegative_sum setT (fun s=>gamma (E `&` @Q k s)).
Proof.
move=> hQ hg hc hnull hroot hki.
have hm := refining_cover_content_measure hg hc.
have hmcell s : measure_measurable (measure_restrict gamma E) (@Q k s).
  exact: dyadic_content_cell_measurable hQ hg hc hnull hki.
have hover s t : s != t -> measure_restrict gamma E (@Q k s `&` @Q k t)=0.
  exact: (@dyadic_content_distinct_overlap_null R n a Q E gamma hQ hm hnull k s t).
have hh := @measure_finite_family_null_overlap_additivity R _ (dyadic_cube_indices n k)
  (measure_restrict gamma E) (measure_restrict_is_measure hm E) (@Q k) setT
  (@finite_finset (dyadic_cube_indices n k) setT) (fun s _=>hmcell s) (fun s t _ _=>hover s t).
have he : E `&` (\bigcup_s @Q k s)=E.
  apply/seteqP; split=> [x [hx _]|x hx] //; split=> //.
  have [s hs] := @dyadic_cube_level_covers R n a Q hQ k x (hroot x hx).
  by exists s.
by rewrite /measure_restrict he in hh.
Qed.
