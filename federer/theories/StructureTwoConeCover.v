(** Federer (1969), 3.3.6, pp. 293–294: the actual two-cone
    inclusion for each selected projected ball. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  StructureCone StructureProjectionKernel StructureConeMetric StructureConeHeight.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_height_projected_slice_distance]: the first
    assertion on Federer p. 294 in the proof of 3.3.6: every original
    z in B whose projected distance is at most e h(x) has distance at
    most h(x) from x. Both the inside and outside narrow-cone cases
    are proved from the actual height and cone laws. *)
Theorem structure_height_projected_slice_distance (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) e x h z:
  0<e ->is_structure_cone_height hmn B p e x h ->B z ->
  mdist (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p z)<=e*h ->mdist x z<=h.
Proof.
move=>he hHeight hz hProjected.
case:(pselect (structure_cone (structure_projection_kernel hmn p) x +oo e z))=>[hIn|hOut].
- apply:(structure_cone_height_upper hHeight); by split.
- rewrite leNgt; apply/negP=>hFar; apply:hOut.
  apply/(structure_projection_cone_metricE hmn p x z +oo he); split; first exact:ltey.
  have hStrict:e*h<e*mdist x z by rewrite ltr_pM2l.
  exact:le_lt_trans hProjected hStrict.
Qed.

(** Source for [structure_height_two_cone_cover]: the displayed
    inclusion at the end of Federer 3.3.6, p. 293, proved on p. 294.
    A near-maximizing ORIGINAL y and the actual original projection
    yield the two actual wider cones of radius 3h(x). There is no
    supplied incidence inequality or covering hypothesis. *)
Theorem structure_height_two_cone_cover (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) e x h y:
  0<e ->is_structure_cone_height hmn B p e x h ->
  (B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y ->
  3*h<4*mdist x y ->
  (B `&` [set z | mdist
    (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p z)<=e*h]) `<=`
    structure_cone (structure_projection_kernel hmn p) x (3*h)%:E (4*e) `|`
    structure_cone (structure_projection_kernel hmn p) y (3*h)%:E (4*e).
Proof.
move=>he hHeight hy hFar z [hz hProjected].
change (is_true (mdist (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
  (euclidean_projection_linear p z)<=e*h)) in hProjected.
have hPositive:=structure_cone_height_positive hHeight.
have hXY:mdist x y<=h:=structure_cone_height_upper hHeight hy.
have hXZ:mdist x z<=h:=structure_height_projected_slice_distance he hHeight hz hProjected.
have hYZ:mdist y z<= 2*h.
  have hTriangle:=metric_triangle y x z.
  rewrite (metric_sym y x) in hTriangle; lra.
have hNarrow:= (structure_projection_cone_metricE hmn p x y +oo he).1 hy.2.
have hPXY:mdist
    (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p y)<=e*h.
  apply:le_trans (ltW hNarrow.2) _; by rewrite ler_pM2l.
have hPSum:mdist
      (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p z)+
    mdist (euclidean_projection_linear p y:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p z)<= 3*e*h.
  have hTriangle:=metric_triangle
    (euclidean_projection_linear p y:inner_metric_space (@euclidean_inner_productP R m))
    (euclidean_projection_linear p x) (euclidean_projection_linear p z).
  rewrite (@metric_sym R (inner_metric_space (@euclidean_inner_productP R m)) (euclidean_projection_linear p y) (euclidean_projection_linear p x)) in hTriangle.
  nra.
have hWide:0<4*e by nra.
have hSeparation:3*e*h<4*e*(mdist x z+mdist y z).
  have hTriangle:=metric_triangle x z y.
  rewrite (metric_sym z y) in hTriangle.
  have hStrict:3*e*h<4*e*mdist x y by nra.
  nra.
case:(ltP (mdist
      (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p z)) (4*e*mdist x z))=>[hFirst|hNotFirst].
- left; apply/(structure_projection_cone_metricE hmn p x z (3*h)%:E hWide).
  split; last exact:hFirst.
  rewrite lte_fin; lra.
- right; apply/(structure_projection_cone_metricE hmn p y z (3*h)%:E hWide).
  split; first by rewrite lte_fin; lra.
  nra.
Qed.
