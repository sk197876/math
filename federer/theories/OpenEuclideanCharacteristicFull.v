(** Federer (1969), 4.1.8, p. 362: viewing
    a Euclidean characteristic current on its whole
    original domain changes no test action. Extensional
    equality of the characteristic sets also changes no current. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentEvaluation EuclideanCharacteristicCurrent
  OpenEuclideanCharacteristicCurrent EuclideanLebesgueDimensions MeasureUP MeasureIntegralUP MeasureSubsetIntegral
  SummableRealFunctionUP MeasureIntegralUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [open_euclidean_characteristic_current_full]: the
    whole-domain copy is the actual original Euclidean
    characteristic current, supporting the finite scalar
    product of Federer 4.1.8, p. 362. *)
Lemma open_euclidean_characteristic_current_full (R:realType) (h2:(1+1:R)!=0) n
    (B:set (R_n R n)) (hB:measure_measurable (@euclidean_lebesgue_measure R n) B):
  @open_euclidean_characteristic_current R h2 n (fun _=>True)
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) B hB=
    @euclidean_characteristic_current R h2 n B hB.
Proof.
apply:current_values_extensional=>phi.
exact:EFin_inj (measure_integral_unique
  (@open_euclidean_characteristic_current_action R h2 n (fun _=>True)
    (fun x (_:True)=>@norm_full_domain_interior R (R_n R n)
      (inner_norm (@euclidean_inner_productP R n)) x) B hB phi)
  (@euclidean_characteristic_current_action R h2 n B hB phi)).
Qed.

(** Source for [open_euclidean_characteristic_set_equal]: equal
    original measurable sets determine the same
    coordinate-oriented current, supporting the original
    coordinate box identity in Federer 4.1.8, p. 362. *)
Lemma open_euclidean_characteristic_set_equal (R:realType) (h2:(1+1:R)!=0) n
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (E F:set (R_n R n))
    (hE:measure_measurable (@euclidean_lebesgue_measure R n) E)
    (hF:measure_measurable (@euclidean_lebesgue_measure R n) F):
  E=F->@open_euclidean_characteristic_current R h2 n U hU E hE=
    @open_euclidean_characteristic_current R h2 n U hU F hF.
Proof.
move=>e;subst F.
have h:hF=hE:=Prop_irrelevance _ _.
by rewrite h.
Qed.
