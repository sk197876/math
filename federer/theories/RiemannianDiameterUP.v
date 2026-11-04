(** Federer (1969), 3.2.46, p. 281: Hausdorff coverings
    use the diameter for the original curve distance rho.
    The independent supremum laws allow infinite distances
    between components; the empty-set diameter is zero. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RiemannianTensorUP RiemannianMetricCarrier RiemannianDistance.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_riemannian_diameter]: the least nonnegative
    upper bound of original rho distances, supporting the
    Hausdorff measures in Federer 3.2.46, p. 281. *)
Record is_riemannian_diameter (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (S : set (riemannian_metric_space hg)) (d : \bar R) : Prop := {
  (** Source for [riemannian_diameter_nonnegative]: the
      nonnegative diameter convention in 2.10.1, p. 170,
      applied to rho in 3.2.46, p. 281. *)
  riemannian_diameter_nonnegative : 0 <= d;
  (** Source for [riemannian_diameter_upper]: every original
      pair distance is at most the diameter, supporting
      3.2.46, p. 281. *)
  riemannian_diameter_upper : forall x y, S x -> S y ->
    @riemannian_distance R n A g (val x) (val y) <= d;
  (** Source for [riemannian_diameter_least]: least upper
      bound law of the actual rho diameter, supporting
      3.2.46, p. 281. *)
  riemannian_diameter_least : forall b, 0 <= b ->
    (forall x y, S x -> S y ->
      @riemannian_distance R n A g (val x) (val y) <= b) -> d <= b
}.

(** Source for [riemannian_diameter_unique]: uniqueness of
    this diameter from its independent order laws, supporting
    the Hausdorff covering definition in 3.2.46, p. 281. *)
Lemma riemannian_diameter_unique (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) S a b :
  @is_riemannian_diameter R n A g hg S a ->
  @is_riemannian_diameter R n A g hg S b -> a=b.
Proof.
move=> ha hb; apply/eqP; rewrite eq_le; apply/andP; split.
- exact: (riemannian_diameter_least ha (riemannian_diameter_nonnegative hb)
    (riemannian_diameter_upper hb)).
- exact: (riemannian_diameter_least hb (riemannian_diameter_nonnegative ha)
    (riemannian_diameter_upper ha)).
Qed.
