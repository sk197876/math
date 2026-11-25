(** Federer (1969), 3.2.46, p. 282: a
    local coordinate representative retains every point
    of each original fibre on its agreeing source.
    These are exact set identities, before integration
    or a rank decomposition is used. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RiemannianTensorUP RiemannianMetricCarrier MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_map_coordinate_fibre_image]:
    the coordinate image of the whole original fibre
    is exactly the fibre of any agreeing coordinate
    representative on the actual coordinate source,
    supporting 3.2.46, p. 282. Neither set
    measurability nor injectivity of f is assumed. *)
Lemma riemannian_map_coordinate_fibre_image (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (F : R_n R m -> R_n R n) (S : set (riemannian_metric_space hg)) :
  (forall x, S x -> F (val x)=val (f x)) -> forall y,
  (fun x : riemannian_metric_space hg=>val x) @` mapping_fibre f S y=
    mapping_fibre F ((fun x : riemannian_metric_space hg=>val x) @` S) (val y).
Proof.
move=> hAgree y; apply/seteqP; split=> z.
- move=> [x [hx hxy] <-]; split; first by exists x.
  by rewrite (hAgree x hx) hxy.
- move=> [[x hx <-] hxy]; exists x; last by []; split; first exact hx.
  apply:val_inj; rewrite -(hAgree x hx); exact hxy.
Qed.

(** Source for [riemannian_coordinate_fibre_outside_chart]:
    a coordinate target point outside the original
    chart has an empty original-source fibre, supporting
    3.2.46, p. 282. The coordinate extension
    need agree only on S; no statement about its
    values outside that source is imposed. *)
Lemma riemannian_coordinate_fibre_outside_chart (R : realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (F : R_n R m -> R_n R n) (S : set (riemannian_metric_space hg)) :
  (forall x, S x -> F (val x)=val (f x)) -> forall z, ~B z ->
    mapping_fibre F ((fun x : riemannian_metric_space hg=>val x) @` S) z=set0.
Proof.
move=> hAgree z hz; apply/seteqP; split; last by move=> x [].
move=> x [[a ha <-] hValue]; exfalso; apply:hz.
have hValueActual : val (f a)=z by rewrite -(hAgree a ha).
by rewrite -hValueActual; exact:set_valP (f a).
Qed.
