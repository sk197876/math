(** Federer (1969), 3.3.20, p. 307: exact images under all coordinate signs. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology lra ring.
From Federer Require Import RealMetricBackground EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct SymmetricSquareScalarProjections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [symmetric_square_projection_flip_second_image]: actual
    second-coordinate reflection translates the projected original set,
    supporting all directions in 3.3.20, p. 307. *)
Lemma symmetric_square_projection_flip_second_image (R:realType)
    (B:set (real_line_metric R)) (u v:R):
  (forall x,B x <->B (1-x)) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+(-v) * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun t:R=>t-v) @`
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
Proof.
move=>hB;rewrite (@square_scalar_projection_swap R B u (-v))
  (@symmetric_square_projection_flip_image R B v u hB).
by rewrite (square_scalar_projection_swap B v u).
Qed.

(** Source for [symmetric_square_absolute_projection_image]: both
    coefficient signs are removed by an exact original-set translation,
    3.3.20, p. 307. The signed shift is explicit, and the same
    identity applies to the root square. No nullity assertion is used. *)
Theorem symmetric_square_absolute_projection_image (R:realType)
    (B:set (real_line_metric R)) (u v:R):
  (forall x,B x <->B (1-x)) ->
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    u * euclidean_real_plane_first p+v * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun t:R=>t+(u-`|u|+v-`|v|)/2) @`
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      `|u| * euclidean_real_plane_first p+`|v| * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
Proof.
move=>hB.
have hFirst a b:
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    a * euclidean_real_plane_first p+b * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun t:R=>t+(a-`|a|)/2) @`
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      `|a| * euclidean_real_plane_first p+b * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
  case:(leP 0 a)=>ha.
  - rewrite (ger0_norm ha) subrr mul0r.
    have hId:(fun t:R=>t+0)=id by apply:funext=>t;field.
    by rewrite hId image_id.
  - have h:=@symmetric_square_projection_flip_image R B (-a) b hB.
    rewrite opprK in h;rewrite h (ltr0_norm ha).
    have hShift:(fun t:R=>t+a)=(fun t:R=>t+(a-(-a))/2)
      by apply:funext=>t;field.
    by rewrite hShift.
have hSecond a b:
  (fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
    a * euclidean_real_plane_first p+b * euclidean_real_plane_second p) @` euclidean_cantor_product B B=
  (fun t:R=>t+(b-`|b|)/2) @`
    ((fun p:inner_metric_space (@euclidean_inner_productP R 2)=>
      a * euclidean_real_plane_first p+`|b| * euclidean_real_plane_second p) @` euclidean_cantor_product B B).
  rewrite (@square_scalar_projection_swap R B a b) (hFirst b a).
  by rewrite (square_scalar_projection_swap B `|b| a).
rewrite (hFirst u v) (hSecond `|u| v) !image_comp.
congr (_ @` euclidean_cantor_product B B);apply:funext=>p;rewrite /comp;field;by rewrite ?pnatr_eq0.
Qed.
