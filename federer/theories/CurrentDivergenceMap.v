(** Federer (1969), 4.1.7, p. 356: the
    original divergence on mass-normed multivectors.
    The actual first differential is followed
    by the opaque divergence map of 4.1.6,
    p. 354. Its coordinate formula and
    the earlier finite linear bounds prove
    boundedness, including the empty coordinate family. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates ExteriorGrading AlternatingForms
  CurrentCoefficientNorms CurrentVectorSpaces EuclideanCoordinateForms OneCovectorInterior
  DivergenceUP DivergenceSealed DivergenceCoordinates ContinuousMultilinearUP ContinuousMultilinearSealed
  ContinuousMultilinearOne NormOperatorNormUP NormFiniteLinearBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentDivergenceMap.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n p:nat.
Local Notation X := (R_n R n).
Local Notation Y := (exterior_power X p.+1).
Local Notation Z := (exterior_power X p).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NY := (@current_vector_mass R h2 n p.+1).
Local Notation hNY := (@current_vector_mass_real_norm R h2 n p.+1).
Local Notation NZ := (@current_vector_mass R h2 n p).
Local Notation hNZ := (@current_vector_mass_real_norm R h2 n p).
Local Notation T := (@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY).
Local Notation eT := (@ContinuousMultilinear.evaluation R 1 X Y NX NY hNX hNY).
Local Notation TN := (@ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY).
Local Notation hT := (@ContinuousMultilinear.laws R 1 X Y NX NY hNX hNY).
Local Notation J := (@continuous_multilinear_one_evaluation R X Y T NX NY eT TN hT).
Local Notation e := (@coordinate_basis R n).

(** Source for [current_divergence_map]: the original
    divergence of the actual first multivector
    differential, supporting Federer 4.1.7,
    p. 356. *)
Definition current_divergence_map:Hom T Z:=hom_comp (@Divergence.value R h2 n p) J.

(** Source for [current_divergence_map_values]: the
    original Hom/tensor/interior specification is
    retained, supporting Federer 4.1.7,
    p. 356, through 4.1.6, p. 354. *)
Lemma current_divergence_map_values z:
  is_divergence_value h2 (J z) (current_divergence_map z).
Proof. exact:Divergence.laws. Qed.

(** Source for [current_divergence_map_bounded]: the
    actual original divergence has a finite
    homogeneous norm bound, supporting smooth
    divergence and the eighth identity in
    Federer 4.1.7, p. 356. The
    bound follows from the previously proved
    coordinate formula and finite linear-map bounds. *)
Theorem current_divergence_map_bounded:
  norm_bounded_linear TN NZ current_divergence_map.
Proof.
have[d [b hb]]:=@current_vector_finite_basis R h2 n p.+1.
pose L (j:'I_n):Hom Y Z:=@HomMap R Y Z
  (fun xi=>positive_one_covector_interior h2 xi (euclidean_coordinate_form j))
  (introT (asboolP _) ((@positive_one_covector_interior_bilinear R h2 X p).1
    (euclidean_coordinate_form j))).
have hConstants j:exists c:R,0<=c /\forall xi:Y,NZ (L j xi)<=c*NY xi.
  exact:(@norm_finite_linear_bounded R Y Z NY NZ hNY hNZ d b hb (L j)).
have[C hC]:=choice hConstants.
exists (\sum_(j:'I_n) C j*NX (e j));split.
- apply:sumr_ge0=>j _;exact:mulr_ge0 (hC j).1 (real_seminorm_nonnegative hNX.1 _).
- move=>z.
  rewrite /current_divergence_map hom_compE divergence_coordinate_formula.
  apply:le_trans (real_seminorm_sum hNZ.1 _) _.
  rewrite mulr_suml;apply:ler_sum=>j _.
  have hRow: NZ (positive_one_covector_interior h2 (J z (e j)) (euclidean_coordinate_form j))<=
      C j*NY (J z (e j)):=(@hC j).2 (J z (e j)).
  have hGradient:=norm_operator_bound
    (@continuous_multilinear_one_norm_laws R X Y T NX NY eT TN hT z) (e j).
  have hBound:=le_trans hRow (ler_wpM2l (hC j).1 hGradient).
  have hReorder:C j*(TN z*NX (e j))=(C j*NX (e j))*TN z by ring.
  by rewrite hReorder in hBound.
Qed.
End CurrentDivergenceMap.
