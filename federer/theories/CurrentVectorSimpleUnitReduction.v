(** Federer (1969), 4.1.23, p. 379:
    reduce each nonzero simple step value to
    a nonnegative multiple of a simple unit
    vector and rotate that direction to the
    standard coordinate direction. Degree zero retains
    its scalar sign; an orthogonal map cannot
    reverse the empty exterior product. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanLinearMaps FiniteCoordinates FiniteExteriorPowers ExteriorGrading ExteriorPowers ExteriorMaps
  ExteriorNorm AssociatedSubspace SimpleElementary SimpleZeroDegree
  CurrentCoefficientNorms CurrentZeroDegreeExteriorLaws Mass Comass MassEquality
  OrthonormalFamilies OrthogonalGroupHaarMeasure EuclideanOrthogonalInvariantMeasures
  SimpleUnitTransitivity.
From Federer Require Import EuclideanStiefelInnerSplitting.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [current_positive_simple_unit_factor]: the
    nonzero simple-vector normalization used in
    Federer 4.1.23, p. 379. Its coefficient
    is exactly the original mass. The original
    positive-degree condition is explicit; zero values
    are handled before this normalization. *)
Theorem current_positive_simple_unit_factor (R : realType)
    (h2 : (1+1:R)!=0) n j
    (v : exterior_power (R_n R n) j.+1) :
  simple v -> v!=0 ->
  exists a : R, exists u : exterior_power (R_n R n) j.+1,
    0<a /\ simple u /\
    @exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
      (@euclidean_inner_productP R n) j.+1 u= 1 /\
    v=a*:u /\ @current_vector_mass R h2 n j.+1 v=a.
Proof.
move=> hSimple hNonzero.
pose X := R_n R n.
pose B := @euclidean_inner_product R n.
pose hB := @euclidean_inner_productP R n.
pose N := @exterior_norm R h2 X B hB j.+1.
pose a := N v.
have hA : 0<a.
  rewrite /a lt0r exterior_norm_eq0 hNonzero.
  exact: exterior_norm_nonnegative.
have hA0 : a!=0 := lt0r_neq0 hA.
pose u := a^-1*:v.
have hInverse : 0<=a^-1 by rewrite invr_ge0; exact: ltW hA.
have hUnit : N u= 1.
  have hNormV : @exterior_norm R h2 X B hB j.+1 v=a := erefl.
  change (@exterior_norm R h2 X B hB j.+1 (a^-1*:v)= 1).
  by rewrite exterior_norm_scale (ger0_norm hInverse) hNormV (mulVf hA0).
have hMass : @current_vector_mass R h2 n j.+1 v=a.
  exact: (@simple_mass_euclidean R h2 X B hB n (@coordinate_basis R n)
    (@coordinate_basisP R n) j.+1 (ltn0Sn j)
    (@comass R h2 X B hB n (@coordinate_basis R n) (@coordinate_basisP R n)
      j.+1 (ltn0Sn j))
    (@comassP R h2 X B hB n (@coordinate_basis R n) (@coordinate_basisP R n)
      j.+1 (ltn0Sn j))
    v (@current_vector_mass R h2 n j.+1 v) hSimple
    (@massP R h2 X B hB n (@coordinate_basis R n) (@coordinate_basisP R n)
      j.+1 (ltn0Sn j) v)).
exists a,u; split; first exact: hA.
split; first exact: simple_scale (ltn0Sn j) hSimple.
split; first exact: hUnit.
split; last exact: hMass.
by rewrite /u scalerA mulfV // scale1r.
Qed.

(** Source for [current_zero_vector_signed_unit_factor]:
    the scalar-sign endpoint of the simple-value
    reduction in Federer 4.1.23, p. 379.
    The original zero-degree mass is the absolute
    scalar value. Both signs and the zero
    coefficient are covered without a false scalar
    simplicity or rotation assertion. *)
Theorem current_zero_vector_signed_unit_factor (R : realType)
    (h2 : (1+1:R)!=0) n (v : exterior_power (R_n R n) 0%N) :
  exists a s : R, 0<=a /\ (s= 1 \/ s= -1) /\
    v=a*:exterior_zeroth_inclusion (R_n R n) s /\
    @current_vector_mass R h2 n 0%N v=a.
Proof.
pose c := exterior_zeroth_inverse (R_n R n) v.
have hValue : exterior_zeroth_inclusion (R_n R n) c=v.
  exact: exterior_zeroth_inverseK.
have hMass : @current_vector_mass R h2 n 0%N v=`|c|.
  exact: current_vector_mass_zeroth_value.
case: (lerP 0 c)=> hC.
- exists c,1; split; first exact: hC.
  split; first by left.
  split; last by rewrite hMass (ger0_norm hC).
  rewrite -linearZ; change (v=exterior_zeroth_inclusion (R_n R n) (c*1)).
  by rewrite mulr1 hValue.
- exists (-c),(-1); split; first by rewrite oppr_ge0; exact: ltW hC.
  split; first by right.
  split; last by rewrite hMass (ltr0_norm hC).
  rewrite -linearZ; change (v=exterior_zeroth_inclusion (R_n R n) ((-c)*(-1))).
  by rewrite mulrNN mulr1 hValue.
Qed.

(** Source for [current_simple_unit_coordinate_rotation]:
    the rotation of a positive-degree simple
    unit step value to the standard coordinate
    direction in Federer 4.1.23, p. 379,
    by the proved orthogonal transitivity of
    2.7.16. The above-dimensional zero case is
    handled before invoking this supporting law. *)
Theorem current_simple_unit_coordinate_rotation (R : realType)
    (h2 : (1+1:R)!=0) n m (hPositive : (0<m)%N) (hMN : (m<=n)%N)
    (u : exterior_power (R_n R n) m) :
  simple u -> @exterior_norm R h2 (R_n R n) (@euclidean_inner_product R n)
    (@euclidean_inner_productP R n) m u= 1 ->
  exists g : euclidean_orthogonal_group R n,
    exterior_power_map (hom_as_linear
      (@orthogonal_element_map R (R_n R n) (@euclidean_inner_product R n)
        (@euclidean_inner_productP R n) n (@coordinate_basis R n)
        (@coordinate_basisP R n) g)) m u=
      e_lambda (fun i : 'I_m => @coordinate_basis R n (widen_ord hMN i)) (ord_tuple m).
Proof.
move=> hSimple hUnit.
pose e := fun i : 'I_m => @coordinate_basis R n (widen_ord hMN i).
have hWiden : injective (@widen_ord m n hMN).
  move=> i j hEqual; apply: val_inj.
  exact: (congr1 (fun k : 'I_n => val k) hEqual).
have hFrame : orthonormal_family (@euclidean_inner_product R n) e.
  move=> i j; rewrite /e (@euclidean_coordinate_orthonormal_family R n).
  by rewrite (inj_eq hWiden).
have hStandardSimple := @product_simple R (R_n R n) m e.
have hStandardUnit := @orthonormal_product_unit_norm R h2 (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n) m e hFrame.
exact: (@simple_unit_transitive R h2 n m u (e_lambda e (ord_tuple m))
  hPositive hSimple hStandardSimple hUnit hStandardUnit).
Qed.
