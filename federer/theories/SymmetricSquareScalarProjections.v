(** Federer (1969), 3.3.20, p. 307: actual scalar projection symmetries of a symmetric square factor. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology ring.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  MetricCartesianProductUP EuclideanCantorProduct LebesgueScalarMeasure ScalarAffineLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [square_scalar_projection_swap]: exchanging the actual
    coordinates of an equal-factor square exchanges the direction
    coefficients, supporting the symmetries in 3.3.20, p. 307. *)
Theorem square_scalar_projection_swap (R:realType) (B:set (real_line_metric R)) (u v:R):
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    v * euclidean_real_plane_first p+u * euclidean_real_plane_second p) @` euclidean_cantor_product B B.
Proof.
apply/seteqP;split=>z [p [hp0 hp1] <-].
- exists (euclidean_real_plane_pair (euclidean_real_plane_second p) (euclidean_real_plane_first p)).
  + split;by rewrite
      ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  + rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R));ring.
- exists (euclidean_real_plane_pair (euclidean_real_plane_second p) (euclidean_real_plane_first p)).
  + split;by rewrite
      ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R)).
  + rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R));ring.
Qed.

(** Source for [symmetric_square_projection_flip_image]: reflecting
    the actual first coordinate of a factor invariant under x maps to
    1-x translates the corresponding projected set, 3.3.20, p. 307.
    This is an exact original-set identity with no measure premise. *)
Theorem symmetric_square_projection_flip_image (R:realType) (B:set (real_line_metric R)) (u v:R):
  (forall x,B x <->B (1-x)) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    (-u) * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun t:R=>t-u) @`
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
Proof.
move=>hReflection;apply/seteqP;split=>z.
- move=>[p [hp0 hp1] <-].
  pose q:=euclidean_real_plane_pair (1-euclidean_real_plane_first p) (euclidean_real_plane_second p).
  exists (u * euclidean_real_plane_first q+v * euclidean_real_plane_second q).
  + exists q;last by [].
    split;rewrite /q
      ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R))=>//.
    exact:(hReflection _).1 hp0.
  + rewrite /q
      (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R));ring.
- move=>[t [p [hp0 hp1] hValue] <-].
  exists (euclidean_real_plane_pair (1-euclidean_real_plane_first p) (euclidean_real_plane_second p)).
  + split;rewrite
      ?(metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      ?(metric_product_second_pair (@euclidean_real_plane_is_metric_product R))=>//.
    exact:(hReflection _).1 hp0.
  + rewrite
      (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
      (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)) -hValue;ring.
Qed.

(** Source for [symmetric_square_projection_flip_length]: the actual
    first-coordinate reflection preserves projection length, by exact
    translated image and scalar Lebesgue invariance, 3.3.20, p. 307. *)
Theorem symmetric_square_projection_flip_length (R:realType) (B:set (real_line_metric R)) (u v:R):
  (forall x,B x <->B (1-x)) ->
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      (-u) * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B)=
  lebesgue_scalar_measure
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
Proof.
move=>hB;rewrite symmetric_square_projection_flip_image //.
have hFunction:(fun t:R=>t-u)=(fun t:R=>1 * t+(-u)) by apply:funext=>t;ring.
by rewrite hFunction scalar_affine_lebesgue_image ?oner_eq0 // normr1 mul1e.
Qed.
