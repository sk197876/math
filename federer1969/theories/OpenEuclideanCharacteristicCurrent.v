(** Federer (1969), 4.1.8, p. 362: the
    original coordinate-oriented characteristic current
    viewed on an arbitrary original open domain.
    Actual zero extension preserves every normalized
    test value used in its subset action. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentDensityUP CurrentOpenRestriction
  EuclideanCharacteristicCurrent EuclideanCharacteristicRestriction EuclideanLebesgueDimensions
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OpenEuclideanCharacteristicCurrent.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hFull := (fun (x:X) (_:True)=>@norm_full_domain_interior R X N x).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior N U x.
Variable B:set X.
Hypothesis hB:measure_measurable (@euclidean_lebesgue_measure R n) B.
Local Notation top := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Local Notation P := (@current_open_test_extension R h2 n n U (fun _=>True) hU hFull (fun _ _=>Logic.I)).

(** Source for [open_euclidean_characteristic_current]: the
    original E^n contracted B viewed on the
    original open U, supporting the finite Cartesian
    products in Federer 4.1.8, p. 362. *)
Definition open_euclidean_characteristic_current:@current_space R h2 n U hU n:=
  @current_open_restriction R h2 n n U (fun _=>True) hU hFull (fun _ _=>Logic.I)
    (@euclidean_characteristic_current R h2 n B hB).

(** Source for [open_euclidean_characteristic_current_action]: every
    original test on U has the literal
    coordinate-oriented integral over B of its globally
    normalized values, supporting Federer 4.1.8,
    p. 362. No containment or boundedness of
    B is added. *)
Theorem open_euclidean_characteristic_current_action phi:
  is_measure_subset_integral (@euclidean_lebesgue_measure R n) B
    (real_total_integrand (fun x=>pairing top (@current_test_value R h2 n U hU n phi x)))
    (@current_value R h2 n U hU n open_euclidean_characteristic_current phi)%:E.
Proof.
rewrite /open_euclidean_characteristic_current current_open_restriction_evaluation.
have hI:=@euclidean_characteristic_current_action R h2 n B hB (P phi).
have hFunction:(fun x=>pairing top (@current_test_value R h2 n (fun _=>True) hFull n (P phi) x))=
    (fun x=>pairing top (@current_test_value R h2 n U hU n phi x)).
  apply:funext=>x;by rewrite current_open_test_extension_values.
by rewrite hFunction in hI.
Qed.

(** Source for [open_euclidean_characteristic_current_restriction]: the
    derived characteristic current is precisely the
    actual original measurable restriction of E^n,
    then viewed on U, supporting Federer 4.1.8,
    p. 362. *)
Theorem open_euclidean_characteristic_current_restriction:
  open_euclidean_characteristic_current=
    @current_open_restriction R h2 n n U (fun _=>True) hU hFull (fun _ _=>Logic.I)
      (@euclidean_fundamental_restricted_current R h2 n B hB).
Proof.
by rewrite /open_euclidean_characteristic_current euclidean_characteristic_current_restriction.
Qed.
End OpenEuclideanCharacteristicCurrent.
