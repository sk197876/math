(** Federer (1969), 3.3.6, p. 293: the positive finite
    supremum h(x) of distances to original points in the narrow cone. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import EuclideanInnerProduct InnerMetric
  EuclideanProjectionSpace StructureCone StructureProjectionKernel StructureConeMetric.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_structure_cone_height]: the exact least-upper-bound
    laws for h(x) in Federer 3.3.6, p. 293. This independent
    specification retains the original B and cone; no height is selected
    globally and no near-maximizing source point is assumed. *)
Record is_structure_cone_height (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) (e:R)
    (x:inner_metric_space (@euclidean_inner_productP R n)) (h:R):Prop:={
  (** Source for [structure_cone_height_positive]: 0<h(x),
      Federer 3.3.6, p. 293. *)
  structure_cone_height_positive:0<h;
  (** Source for [structure_cone_height_upper]: all original distances
      in the displayed supremum are at most h(x), Federer 3.3.6, p. 293. *)
  structure_cone_height_upper:forall y,
    (B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y ->mdist x y<=h;
  (** Source for [structure_cone_height_least]: h(x) is below every
      upper bound of those distances, Federer 3.3.6, p. 293. *)
  structure_cone_height_least:forall t,
    (forall y,(B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y ->mdist x y<=t) ->h<=t
}.

(** Source for [structure_cone_height_exists]: existence of the original
    finite h(x), Federer 3.3.6, p. 293. Nonemptiness and a proved
    finite distance bound suffice. Only scalar completeness is used. *)
Theorem structure_cone_height_exists (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) e x M:
  0<e ->
  (exists y,(B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y) ->
  (forall y,B y ->mdist x y<=M) ->
  exists h,is_structure_cone_height hmn B p e x h.
Proof.
move=>he [y [hy hCone]] hM.
pose H: set R:=mdist x @` (B `&` structure_cone (structure_projection_kernel hmn p) x +oo e).
have hHy:H (mdist x y) by exists y; first by split.
have hNonempty:H!=set0 by exists (mdist x y).
have hBound:exists t,ubound H t.
  exists M=>t [z [hz _] <-]; exact:hM z hz.
have hUpper z:(B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) z ->mdist x z<=sup H.
  move=>hz; have hHz:H (mdist x z) by exists z.
  exact:(@ub_le_sup R H hBound (mdist x z) hHz).
have hConeMetric:((mdist x y)%:E < +oo)%E /\
    mdist (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
      (euclidean_projection_linear p y)<e*mdist x y.
  exact:(structure_projection_cone_metricE hmn p x y +oo he).1 hCone.
have hNonnegative:=mdist_ge0
  (euclidean_projection_linear p x:inner_metric_space (@euclidean_inner_productP R m))
  (euclidean_projection_linear p y).
have hPositive:0<mdist x y by nra.
exists (sup H); constructor.
- exact:lt_le_trans hPositive (hUpper y (conj hy hCone)).
- exact:hUpper.
- move=>t ht; apply:(@ge_sup R H t hNonempty)=>v [z hz <-]; exact:ht z hz.
Qed.

(** Source for [structure_cone_height_near_maximizer]: choose y in
    the original narrow cone with 4|y-x|>3h(x), Federer 3.3.6,
    p. 293. The point is derived from the exact supremum laws. *)
Theorem structure_cone_height_near_maximizer (R:realType) n m (hmn:(m<=n)%N)
    (B:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m) e x h:
  is_structure_cone_height hmn B p e x h ->
  exists y,(B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y /\
    3*h<4*mdist x y.
Proof.
move=>hHeight.
case:(pselect (exists y,(B `&` structure_cone (structure_projection_kernel hmn p) x +oo e) y /\
    3*h<4*mdist x y))=>[hYes|hNo]; first exact:hYes.
exfalso.
have hSmall:h<= 3*h/4.
  apply:(structure_cone_height_least hHeight)=>y hy.
  have hNot:~3*h<4*mdist x y by move=>hFar; apply:hNo; exists y.
  have hBound:4*mdist x y<= 3*h by rewrite leNgt; apply/negP.
  lra.
have hPositive:=structure_cone_height_positive hHeight; lra.
Qed.
