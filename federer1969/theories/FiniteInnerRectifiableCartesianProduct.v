(** Federer (1969), 3.2.23, p. 260, applied
    in the product chart of 3.2.47, p. 283.
    Actual orthonormal coordinates transfer finite Hausdorff
    rectifiability to the original Cartesian inner metric.
    The first factor remains genuinely rectifiable. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerNorm InnerMetric ProductInner FiniteInnerChartUP FiniteInnerCartesianGeometry
  FiniteInnerRectifiableCoordinates FiniteMeasureRectifiableImages
  RectifiableSetUP LipschitzUP LipschitzBasic LipschitzRectifiableImages
  RectifiableCartesianProduct RectifiableCartesianProductUP HausdorffMeasure TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_inner_rectifiable_cartesian_product]:
    finite-mass product rectifiability of 3.2.23, p. 260,
    in the original finite inner ambient spaces, supporting
    the product charts of 3.2.47, p. 283. All
    natural dimensions and both original Borel factors remain. *)
Theorem finite_inner_rectifiable_cartesian_product (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  @is_m_rectifiable R (inner_metric_space hB) r E ->@borel_set (inner_metric_space hB) E ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hC) mu) mu Z ->
  @borel_set (inner_metric_space hC) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)%N)
    (r+mu)%N [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hV hW hE hEB hZ hZB.
have hEC:=rectifiable_lipschitz_image
  (@finite_inner_chart_inverse_lipschitz R V B hB n e p E hV) hE.
have hZC:=@finite_inner_chart_measure_rectifiable_coordinates R W C hC v f q mu Z hW hZ.
have hECB:=@finite_inner_chart_coordinates_borel R V B hB n e p E hV hEB.
have hZCB:=@finite_inner_chart_coordinates_borel R W C hC v f q Z hW hZB.
have hProduct:=rectifiable_cartesian_rectifiability_law
  (federer_3_2_23 hEC hECB hZC hZCB).
have [L [hL hBound]]:=@finite_inner_cartesian_parametrization_lipschitz R V W B C hB hC n v e p f q hV hW.
have hLip:@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R (n+v)))
    (inner_metric_space (product_inner_productP hB hC))
    (EuclideanCartesianMap.euclidean_cartesian_set (p @` E) (q @` Z))
    (finite_inner_cartesian_parametrization e f).
  exists L; split; first exact hL.
  exact (metric_lipschitz_bound_restrict (fun x _=>I) hBound).
have hImage:=hausdorff_measure_rectifiable_lipschitz_image hLip hProduct.
by rewrite (@finite_inner_cartesian_parametrization_image R V W B C n v e p f q E Z hV hW) in hImage.
Qed.

(** Source for [product_inner_swap_norm]: the actual
    Cartesian norm is symmetric under exchanging its factors,
    by 1.7.11, p. 36; supporting the product
    finiteness argument of 3.2.47, p. 283. *)
Lemma product_inner_swap_norm (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) (z:V*W):
  inner_norm (product_inner_productP hC hB) (z.2,z.1)=
    inner_norm (product_inner_productP hB hC) z.
Proof.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
by rewrite inner_norm_sqr !product_innerE addrC -inner_norm_sqr.
Qed.

(** Source for [finite_inner_rectifiable_cartesian_product_right]:
    the same finite product theorem with its genuine
    factor second, 3.2.23, p. 260, supporting
    the whole isotropy product in 3.2.47, p. 283.
    The interchange is an actual isometry, with every
    natural degree and the original Cartesian metric retained. *)
Theorem finite_inner_rectifiable_cartesian_product_right (R:realType) (V W:lmodType R)
    B C (hB:@is_inner_product R V B) (hC:@is_inner_product R W C) n v
    (e:Hom (R_n R n) V) (p:Hom V (R_n R n))
    (f:Hom (R_n R v) W) (q:Hom W (R_n R v)) r mu (E:set V) (Z:set W):
  is_finite_inner_chart B e p ->is_finite_inner_chart C f q ->
  is_measure_m_rectifiable (@hausdorff_measure R (inner_metric_space hB) r) r E ->
  @borel_set (inner_metric_space hB) E ->
  @is_m_rectifiable R (inner_metric_space hC) mu Z ->@borel_set (inner_metric_space hC) Z ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP hB hC)) (r+mu)%N)
    (r+mu)%N [set z:V*W|E z.1 /\Z z.2].
Proof.
move=>hV hW hE hEB hZ hZB.
have hReverse:=@finite_inner_rectifiable_cartesian_product R W V C B hC hB v n
  f q e p mu r Z E hW hV hZ hZB hE hEB.
pose P:=inner_metric_space (product_inner_productP hC hB).
pose Q:=inner_metric_space (product_inner_productP hB hC).
pose swap:=fun z:W*V=>(z.2,z.1).
have hLip:@is_metric_lipschitz R P Q [set z:W*V|Z z.1 /\E z.2] swap.
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  move=>x y _ _; rewrite mul1r !inner_metric_distanceE.
  change (is_true (inner_norm (product_inner_productP hB hC) (x.2-y.2,x.1-y.1)<=
    inner_norm (product_inner_productP hC hB) (x-y))).
  by rewrite (product_inner_swap_norm hC hB (x-y)).
have hImage:=hausdorff_measure_rectifiable_lipschitz_image hLip hReverse.
have hSet:swap @` [set z:W*V|Z z.1 /\E z.2]=[set z:V*W|E z.1 /\Z z.2].
  apply/seteqP; split=>z.
  - by move=>[w [hwZ hwE] <-]; split.
  - move=>[hzE hzZ]; exists (z.2,z.1); first by split.
    exact (esym (surjective_pairing z)).
by rewrite hSet (addnC mu r) in hImage.
Qed.
