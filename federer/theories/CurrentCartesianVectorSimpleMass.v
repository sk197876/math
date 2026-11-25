(** Federer (1969), 4.1.8, p. 361: equality of
    the original product mass when either factor is
    simple. Apply the original orthogonally supported
    factor theorem of 1.8.4, pp. 40–41, to the actual
    block ranges, and retain both scalar endpoints. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear ModuleQuotient SubspaceSums SubspaceCarrier
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates EuclideanBlockLinearMaps EuclideanBlockLinear
  InnerProductUP ExteriorGrading ExteriorMaps ExteriorMapScaling ExteriorNormNaturality
  ExteriorHomogeneousProducts SimpleVectors CurrentCoefficientNorms
  CurrentPositiveCoefficientNorms CurrentExteriorProductMass CurrentCartesianVectorProduct
  CurrentCartesianBlockMass MassUP OrthogonalMass.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianVectorSimpleMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Local Notation P := (hom_as_linear (@euclidean_first_injection_map R m n)).
Local Notation Q := (hom_as_linear (@euclidean_last_injection_map R m n)).
Local Notation N := (fun d=>@current_vector_mass R h2 (m+n) d).
Local Notation K := (fun d=>@current_form_comass R h2 (m+n) d).

(** Source for [current_cartesian_vector_simple_mass_positive]:
    the original included factors have orthogonal supports;
    either simple factor suffices for exact mass, supporting
    Federer 4.1.8, p. 361, by 1.8.4, pp. 40–41. *)
Theorem current_cartesian_vector_simple_mass_positive i j
    (hi:(0<i)%N) (hj:(0<j)%N)
    (xi:exterior_power X i) (eta:exterior_power Y j):
  simple xi \/simple eta ->
  N (i+j) (@current_cartesian_vector_product R m n i j xi eta)=
    @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta.
Proof.
move=>hSimple.
pose SP:=range_subspace P.
pose SQ:=range_subspace Q.
pose LP:=linear_comp (subspace_retraction SP) P.
pose LQ:=linear_comp (subspace_retraction SQ) Q.
pose x0:=exterior_power_map LP i xi.
pose y0:=exterior_power_map LQ j eta.
have hX:exterior_power_map (subspace_inclusion SP) i x0= exterior_power_map P i xi.
  rewrite /x0 exterior_power_map_composition.
  apply:exterior_power_map_ext=>u.
  change (subspace_inclusion SP (subspace_retraction SP (P u))= P u).
  apply:subspace_retraction_on;by exists u.
have hY:exterior_power_map (subspace_inclusion SQ) j y0= exterior_power_map Q j eta.
  rewrite /y0 exterior_power_map_composition.
  apply:exterior_power_map_ext=>u.
  change (subspace_inclusion SQ (subspace_retraction SQ (Q u))= Q u).
  apply:subspace_retraction_on;by exists u.
have hOrth:forall u v,SP u->SQ v->@euclidean_inner_product R (m+n) u v= 0.
  move=>u v [a ->] [b ->].
  change (@euclidean_inner_product R (m+n)
    (@euclidean_first_injection R m n a) (@euclidean_last_injection R m n b)= 0).
  rewrite /euclidean_first_injection /euclidean_last_injection euclidean_block_join_inner /=.
  by rewrite (bil0r (inner_bilinear (@euclidean_inner_productP R m)))
    (bil0l (inner_bilinear (@euclidean_inner_productP R n))) add0r.
have hIncludedSimple:simple (exterior_power_map (subspace_inclusion SP) i x0) \/
    simple (exterior_power_map (subspace_inclusion SQ) j y0).
  case:hSimple=>hS.
  - left;rewrite hX;exact:(exterior_power_map_simple P hS).
  - right;rewrite hY;exact:(exterior_power_map_simple Q hS).
have hSum:(0<i+j)%N:=leq_trans hi (leq_addr j i).
have hMassX:is_mass (K i) (exterior_power_map (subspace_inclusion SP) i x0)
    (N i (exterior_power_map P i xi)).
  rewrite hX;exact:(@current_positive_mass_laws R h2 (m+n) i hi _).
have hMassY:is_mass (K j) (exterior_power_map (subspace_inclusion SQ) j y0)
    (N j (exterior_power_map Q j eta)).
  rewrite hY;exact:(@current_positive_mass_laws R h2 (m+n) j hj _).
have hMassProduct:is_mass (K (i+j))
    (exterior_product (exterior_power_map (subspace_inclusion SP) i x0)
      (exterior_power_map (subspace_inclusion SQ) j y0))
    (N (i+j) (@current_cartesian_vector_product R m n i j xi eta)).
  rewrite hX hY;exact:(@current_positive_mass_laws R h2 (m+n) (i+j) hSum _).
have h:=@orthogonal_mass_product R h2 Z (@euclidean_inner_product R (m+n))
  (@euclidean_inner_productP R (m+n)) (m+n) (@coordinate_basis R (m+n))
  (@coordinate_basisP R (m+n)) SP SQ hOrth i j hi hj (K i) (K j) (K (i+j))
  (@current_positive_comass_laws R h2 (m+n) i hi)
  (@current_positive_comass_laws R h2 (m+n) j hj)
  (@current_positive_comass_laws R h2 (m+n) (i+j) hSum)
  x0 y0 _ _ _ hIncludedSimple hMassX hMassY hMassProduct.
by rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass in h.
Qed.

(** Source for [current_cartesian_vector_simple_mass]: the
    original product mass is exact when either factor is
    simple, including both degree-zero endpoints, supporting
    Federer 4.1.8, p. 361. *)
Theorem current_cartesian_vector_simple_mass i j
    (xi:exterior_power X i) (eta:exterior_power Y j):
  simple xi \/simple eta ->
  N (i+j) (@current_cartesian_vector_product R m n i j xi eta)=
    @current_vector_mass R h2 m i xi*@current_vector_mass R h2 n j eta.
Proof.
case:i xi=>[|p] xi.
- move=>_;rewrite /current_cartesian_vector_product current_exterior_product_mass_zero_left.
  by rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass.
- case:j eta=>[|q] eta.
  + move=>_;rewrite /current_cartesian_vector_product current_exterior_product_mass_zero_right.
    by rewrite current_cartesian_first_inclusion_mass current_cartesian_second_inclusion_mass.
  + exact:(@current_cartesian_vector_simple_mass_positive p.+1 q.+1 (ltn0Sn p) (ltn0Sn q) xi eta).
Qed.
End CurrentCartesianVectorSimpleMass.
