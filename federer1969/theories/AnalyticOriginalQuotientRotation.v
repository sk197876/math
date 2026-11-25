(** Supporting Federer (1969), 3.4.8(5), p. 328:
    put differently rotated original coefficient actions in one
    original quotient. Actual inverse orthogonal pullbacks preserve
    the original constants and centre-vanishing ideal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness LinearBasis
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure AnalyticGermUP AnalyticGermRing AnalyticScalarsSealed AnalyticVanishingIdealSealed
  AnalyticGermValueSealed AnalyticOrthogonalPullback AnalyticOrthogonalPullbackInverse
  AnalyticRotatedGermIdeal PointedAnalyticPullbackRing PointedAnalyticPullbackValue CommutativeQuotientUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Rotation.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation P:=(fun g:O=>@analytic_orthogonal_germ_map R X B hB n e he g).
Local Notation M:=(@AnalyticVanishingIdeal.value R X NX hNX 0).
Local Notation constants:=(@AnalyticScalars.map R X NX hNX 0).
Variable I:set G.
Variable C:comNzRingType.
Variable pi:{rmorphism G->C}.
Hypothesis hPi:is_commutative_ideal_quotient I pi.

(** Source for [analytic_original_quotient_rotation]: supporting
    arbitrary original ideal comparison for Federer 3.4.8(5), p. 328.
    Every rotated quotient maps to the same O/I with its exact
    original kernel, the same scalar constants and the same maximal
    ideal image. The inverse rotation is an internally proved witness. *)
Theorem analytic_original_quotient_rotation (g:O):
  exists rho:{rmorphism G->C},
    is_commutative_ideal_quotient (@analytic_rotated_germ_ideal R X B hB n e he I g) rho /\
    (forall c:R,rho (constants c) = pi (constants c)) /\
    (forall alpha:G,M alpha ->(pi @` M) (rho alpha)).
Proof.
have [h [hLeft hRight]]:=@analytic_orthogonal_germ_inverse_exists R X B hB n e he g.
pose rho:=GRing.RMorphism.clone G C (pi \o P h) _.
exists rho;split.
- constructor.
  + move=>c;have [alpha hAlpha]:=commutative_quotient_surjective hPi c.
    exists (P g alpha);change (pi (P h (P g alpha)) = c);by rewrite hLeft.
  + move=>alpha.
    change (pi (P h alpha) = 0 <->@analytic_rotated_germ_ideal R X B hB n e he I g alpha).
    rewrite (commutative_quotient_kernel hPi).
    exact:iff_sym (@analytic_rotated_germ_ideal_inverse_membership R X B hB n e he I g h
      hLeft hRight alpha).
- split.
  + move=>c;change (pi (P h (constants c)) = pi (constants c));apply:congr1.
    rewrite (@AnalyticScalars.laws R X NX hNX 0 c).
    exact:(@pointed_analytic_pullback_constant R X X NX NX hNX hNX 0 0
      (@orthogonal_element_map R X B hB n e he h) (P h)
      (@analytic_orthogonal_germ_map_specification R X B hB n e he h) c).
  + move=>alpha hAlpha.
    exists (P h alpha);last reflexivity.
    apply/(@AnalyticVanishingIdeal.laws R X NX hNX 0).
    rewrite (@pointed_analytic_pullback_centre_value R X X NX NX hNX hNX 0 0
      (@orthogonal_element_map R X B hB n e he h) (P h)
      (@analytic_orthogonal_germ_map_specification R X B hB n e he h)
      (@orthogonal_germ_coordinate_zero R X B hB n e he h)).
    exact:(@AnalyticVanishingIdeal.laws R X NX hNX 0 alpha).1 hAlpha.
Qed.
End Rotation.
