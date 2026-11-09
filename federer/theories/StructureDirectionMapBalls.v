(** Federer (1969), 3.3.4, pp. 291–292:
    ball and fibre identities for any actual
    Borel direction map satisfying the independent
    formula on its original nonzero domain. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  InnerUnitNormalization SymmetricGrading InnerSymmetricPositivity SymmetricSquareGeometry
  MetricSubsetBackground StructureProjectiveSpace StructureDirectionMapUP
  StructureProjectiveDirections.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_direction_map_ball]: the
    exact inverse-image ball inequality for f
    and F in Federer 3.3.4, p. 291.
    Original nonzero projection vectors remain
    unnormalized on the right-hand side. *)
Theorem structure_direction_map_ball (R:realType) (X:metricType R) m
    (q:X->inner_metric_space (@euclidean_inner_productP R m.+1))
    (f:X->structure_projective_space R m)
    (z:structure_projective_space R m) (v:R_n R m.+1) x (t:R):
  is_structure_projective_direction_map q f ->
  0<inner_norm (@euclidean_inner_productP R m.+1) (q x) ->
  inner_norm (@euclidean_inner_productP R m.+1) v= 1 ->
  val z=inner_projective_square v ->0<t ->
  (mdist z (f x)<t <->
    (inner_norm (@euclidean_inner_productP R m.+1) (q x))^+2-
      (euclidean_inner_product (q x) v)^+2<
      t^+2*(inner_norm (@euclidean_inner_productP R m.+1) (q x))^+2).
Proof.
move=>[_ hF] hx hv hz ht.
rewrite metric_sym metric_subset_distanceE.
change (inner_norm (@symmetric_inner_productP R (R_n R m.+1)
    (@euclidean_inner_product R m.+1) (@euclidean_inner_productP R m.+1) 2)
    (val (f x)-val z)<t <->
    (inner_norm (@euclidean_inner_productP R m.+1) (q x))^+2-
      (euclidean_inner_product (q x) v)^+2<
      t^+2*(inner_norm (@euclidean_inner_productP R m.+1) (q x))^+2).
rewrite (hF x hx) hz.
exact:structure_projective_direction_ball hx hv ht.
Qed.

(** Source for [structure_direction_map_fibre]: the
    actual two-direction fibre identity used for
    F inverse R contained in D in Federer
    3.3.4, p. 292. Equality is in the
    original projective carrier and retains
    both antipodal unit directions. *)
Theorem structure_direction_map_fibre (R:realType) (X:metricType R) m
    (q:X->inner_metric_space (@euclidean_inner_productP R m.+1))
    (f:X->structure_projective_space R m)
    (z:structure_projective_space R m) (v:R_n R m.+1) x:
  is_structure_projective_direction_map q f ->
  0<inner_norm (@euclidean_inner_productP R m.+1) (q x) ->
  inner_norm (@euclidean_inner_productP R m.+1) v= 1 ->
  val z=inner_projective_square v ->
  (f x=z <->
    inner_unit_normalization (@euclidean_inner_productP R m.+1) (q x)=v \/
    inner_unit_normalization (@euclidean_inner_productP R m.+1) (q x)= -v).
Proof.
move=>[_ hF] hx hv hz.
have hVal:(f x=z <-> val (f x)=val z).
  split; first by move=>->.
  exact:val_inj.
rewrite hVal (hF x hx) hz.
exact:structure_projective_direction_fibre hx hv.
Qed.
