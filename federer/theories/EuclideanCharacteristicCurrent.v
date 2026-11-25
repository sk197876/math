(** Federer (1969), 4.1.8, p. 362: the
    original coordinate-oriented Euclidean current restricted
    to a measurable set. The existing characteristic
    density current gives its actual subset action;
    agreement with the original measurable restriction
    is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentDensityUP CurrentCoefficientNorms CurrentDensityAction CurrentCharacteristicDensity
  CurrentDensityUniqueness EuclideanFundamentalCurrent EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP
  CharacteristicFunctionUP CharacteristicFunctionSealed RealSubsetCharacteristicIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_characteristic_current]: the
    original Lebesgue density chi_B times e_1
    wedge ... wedge e_n, supporting the final
    ordered-box identity in Federer 4.1.8, p. 362,
    by the measurable-density current of 4.1.7,
    p. 356. Dimension zero is retained. *)
Definition euclidean_characteristic_current (R:realType) (h2:(1+1:R)!=0) n
    (B:set (R_n R n)) (hB:measure_measurable (@euclidean_lebesgue_measure R n) B):
    @full_current_space R h2 n n:=
  @current_characteristic_density R h2 n n (@euclidean_lebesgue_measure R n)
    (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
    (@euclidean_distribution_measure_compact_finite R n) B hB
    (e_lambda (@coordinate_basis R n) (ord_tuple n)).

(** Source for [euclidean_characteristic_current_action]: every
    original compact top-degree test has exactly its
    original coordinate-oriented subset integral, supporting
    Federer 4.1.8, p. 362. *)
Theorem euclidean_characteristic_current_action (R:realType) (h2:(1+1:R)!=0) n
    (B:set (R_n R n)) (hB:measure_measurable (@euclidean_lebesgue_measure R n) B)
    (phi:@current_test_space R h2 n (fun _=>True)
      (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) n):
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) B
    (real_total_integrand (fun x=>pairing (e_lambda (@coordinate_basis R n) (ord_tuple n))
      (@current_test_value R h2 n (fun _=>True)
        (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
          (inner_norm (@euclidean_inner_productP R n)) x) n phi x)))
    (@current_value R h2 n (fun _=>True)
      (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
        (inner_norm (@euclidean_inner_productP R n)) x) n
      (@euclidean_characteristic_current R h2 n B hB) phi)%:E.
Proof.
pose X:=R_n R n.
pose top:=e_lambda (@coordinate_basis R n) (ord_tuple n).
pose value:=@current_test_value R h2 n (fun _=>True)
  (fun x (_:True)=>@norm_full_domain_interior R X (inner_norm (@euclidean_inner_productP R n)) x) n.
pose chi:=@CharacteristicFunction.value R X B.
have hChi:=@CharacteristicFunction.laws R X B.
have hI:=@current_characteristic_density_action R h2 n n (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) B hB top phi.
have hPoint:(fun x=>pairing (chi x*:top) (value phi x))=
    (fun x=>chi x*pairing top (value phi x)).
  apply:funext=>x;by rewrite /pairing linearZ.
rewrite hPoint in hI.
exact:(@real_subset_characteristic_integral R X (@euclidean_lebesgue_measure R n) B chi
  (fun x=>pairing top (value phi x)) _ hChi).2 hI.
Qed.

(** Source for [euclidean_characteristic_current_whole]: restricting
    the original coordinate density to the whole
    Euclidean space recovers E^n, supporting the empty
    box convention in Federer 4.1.8, p. 362. *)
Lemma euclidean_characteristic_current_whole (R:realType) (h2:(1+1:R)!=0) n
    (hWhole:measure_measurable (@euclidean_lebesgue_measure R n) setT):
  @euclidean_characteristic_current R h2 n setT hWhole=@euclidean_fundamental_current R h2 n.
Proof.
pose X:=R_n R n.
pose top:=e_lambda (@coordinate_basis R n) (ord_tuple n).
have hI:=@current_characteristic_density_action R h2 n n (@euclidean_lebesgue_measure R n)
  (euclidean_lebesgue_is_measure R n) (@euclidean_distribution_measure_borel R n)
  (@euclidean_distribution_measure_compact_finite R n) setT hWhole top.
have hPoint:(fun x:X=>@CharacteristicFunction.value R X setT x*:top)=(fun _=>top).
  apply:funext=>x;rewrite (characteristic_on_set (@CharacteristicFunction.laws R X setT) Logic.I).
  exact:scale1r.
rewrite hPoint in hI.
exact:(@current_density_action_unique R h2 n n (@euclidean_lebesgue_measure R n)
  (fun _=>top) (@euclidean_characteristic_current R h2 n setT hWhole)
  (@euclidean_fundamental_current R h2 n) hI (@euclidean_fundamental_current_action R h2 n)).
Qed.
