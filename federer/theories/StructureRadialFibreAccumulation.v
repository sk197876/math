(** Federer (1969), 3.3.4, p. 292:
    membership in every original radial
    image forces actual punctured affine
    plane accumulation once the exact fibre
    geometry has been proved. No hull
    or selected source point is used. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerMetric StructurePlaneGrowth StructurePlaneAccumulationScales.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_original_radial_fibre_accumulation]:
    the final original-image implication
    F inverse R contained in D of
    Federer 3.3.4, p. 292. Each
    reciprocal cutoff supplies an actual
    point of the original A and the
    original nonzero direction domain. Exact
    fibre containment gives its original
    affine plane, and the cofinal metric
    criterion proves punctured accumulation. *)
Theorem structure_original_radial_fibre_accumulation (R:realType) n k (Y:Type)
    (A D:set (inner_metric_space (@euclidean_inner_productP R n)))
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (V:G (R_n R n) k) (f:inner_metric_space (@euclidean_inner_productP R n)->Y) (z:Y):
  (forall x,D x ->x!=a) ->
  (forall x,A x ->D x ->f x=z ->grassmann_val V (x-a)) ->
  (\bigcap_i (f @` [set x|A x /\ mdist a x<((i.+1)%:R:R)^-1 /\ D x])) z ->
  structure_plane_accumulation A a V.
Proof.
move=>hPuncture hFibre hImages.
apply:(structure_plane_accumulation_reciprocals A a V).2=>i.
have [x [hA [hNear hD]] hValue]:=hImages i I.
exists x; split=>//; split; first exact:hFibre x hA hD hValue.
apply/andP; split.
- by rewrite inner_norm_gt0 subr_eq0; exact:hPuncture x hD.
- by move:hNear; rewrite inner_metric_distanceE -[a-x]opprB inner_normN.
Qed.
