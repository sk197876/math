(** Federer (1969), 3.4.4, p. 318: class k
    of the original coordinatewise map, using the proved finite calculus. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP EuclideanCoordinateTopology
  NormDifferentialUP NormHigherCurveDerivativeUP NormRegularity NormRegularityOperations
  NormRegularityLinearMaps NormRegularityFiniteSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_assembly_class]: the map
    assembled from the printed scalar coordinates is of class
    k, 3.4.4, p. 318, by the finite
    sum and bounded linear composition laws of 3.1.11,
    p. 220. The empty target family remains valid. *)
Theorem euclidean_scalar_assembly_class (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (A:set X) m
    (F:'I_m->X->R^o) k:
  (forall x,A x ->norm_domain_interior NX A x) ->
  (forall i,norm_class hNX (@scalar_absolute_value_norm R) A (F i) k) ->
  norm_class hNX (inner_norm_real_norm (@euclidean_inner_productP R m)) A
    (fun x=>[ffun i=>F i x]) k.
Proof.
move=>hA hF.
pose Y:=R_n R m.
pose NY:=inner_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose e:=@coordinate_basis R m.
pose L i:=@scalar_coefficient_linear_map R Y (e i).
have hBound i:norm_bounded_linear (fun t:R^o=>`|t|) NY (L i).
  exists (NY (e i));split;first exact:real_seminorm_nonnegative hNY.1 (e i).
  move=>t;change (is_true (NY (t*:e i)<=NY (e i)*`|t|)).
  by rewrite /NY (real_seminorm_scale hNY.1) mulrC.
have hTerm i:norm_class hNX hNY A (fun x=>L i (F i x)) k.
  exact:(@norm_class_postcompose_linear R X R^o Y NX (fun t:R^o=>`|t|) NY
    hNX (@scalar_absolute_value_norm R) hNY A (F i) (L i) k (hBound i) (hF i)).
have hSum:=@norm_class_finite_sum R X Y NX NY hNX hNY A [the finType of 'I_m]
  (fun i x=>L i (F i x)) k hA hTerm.
apply:(@norm_class_domain_agreement R X Y NX NY hNX hNY A
  (fun x=>\sum_i L i (F i x)) (fun x=>[ffun i=>F i x]) k _ hSum).
move=>x hx.
have hExpansion:=@euclidean_coordinate_expansion R m [ffun i=>F i x].
change ((\sum_i F i x*:e i)=[ffun i=>F i x]).
move:hExpansion;have hEqual:(\sum_i [ffun j=>F j x] i*:e i)=\sum_i F i x*:e i.
  by apply:eq_bigr=>i _;rewrite ffunE.
by rewrite hEqual.
Qed.
