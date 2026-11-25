(** Federer (1969), 4.1.13, pp. 369–370: put the
    final affine estimate of 4.1.9, p. 364, in the
    original notation rho=max(||Df||,||Dg||). The
    exact integral and every natural degree are retained. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions
  classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanHomOperator OperatorNormUP OperatorNormSealed CurrentDomain CurrentSpaces
  CurrentIntegrationCriterion NormalisedCurrentSealed CurrentMapDifferential
  CurrentHomotopyUP CurrentHomotopyCylinder CurrentDeformationChainSealed
  CurrentAffineHomotopyMass HomotopyAffinePowerFields CurrentMassSealed MeasureIntegralUP
  MeasureIntegralBounds SummableRealFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [nonnegative_maximum_power]: supporting the
    original rho^m in Federer 4.1.13, p. 369.
    Natural powers preserve order on the nonnegative reals,
    so taking the maximum before or after the power agrees.
    The assertion includes exponent zero and both zero inputs. *)
Lemma nonnegative_maximum_power (R:realType) (a b:R) j:
  0<=a->0<=b->Num.max (a^+j) (b^+j)=(Num.max a b)^+j.
Proof.
move=>ha hb;case:(leP a b)=>hab.
- have hp:a^+j<=b^+j by apply:lerXn2r;rewrite ?nnegrE.
  by rewrite (max_idPr hp).
- have hba:b<=a:=ltW hab.
  have hp:b^+j<=a^+j by apply:lerXn2r;rewrite ?nnegrE.
  by rewrite (max_idPl hp).
Qed.

Section CurrentAffineHomotopyMaximumBound.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n nu j:nat.
Local Notation X := (R_n R n).
Local Notation Y := (R_n R nu).
Local Notation NY := (inner_norm (@euclidean_inner_productP R nu)).
Variable A:set R.
Variables (U:set X) (V:set Y).
Variables (f g:X->Y) (h:R_n R (1+n)%N->Y).
Hypothesis hH:@is_smooth_current_homotopy R n nu A U V f g h.
Local Notation hU := (@current_homotopy_source_open R n nu A U V f g h hH.1).
Local Notation hV := (@current_homotopy_target_open R n nu A U V f g h hH.1).
Variable T:@current_space R h2 n U hU j.
Hypothesis hT:@is_integration_representable_current R h2 n j U hU T.
Local Notation UT := (current_domain R n U).
Local Notation beta := (@NormalisedCurrent.measure R h2 n j U hU T hT).
Local Notation Op := (@euclidean_operator_norm R n nu).
Local Notation a := (fun x:UT=>NY (g (set_val x)-f (set_val x))).
Local Notation b := (fun x:UT=>Op (@current_map_differential R n nu U f (set_val x))).
Local Notation c := (fun x:UT=>Op (@current_map_differential R n nu U g (set_val x))).
Local Notation Max := (@homotopy_affine_power_maximum R n j U a b c).
Local Notation Weight := (fun x:UT=>a x*(Num.max (b x) (c x))^+j).
Local Notation Value := (measure_lower_integral beta (real_total_integrand Weight)).
Hypothesis hAffine:forall t x,A t->U x->
  @current_homotopy_slice_map R n nu h t x=(1-t)*:f x+t*:g x.
Hypothesis hProper:@is_current_homotopy_proper R h2 n nu j A U V f g h hH.1 T.
Local Notation chain := (@CurrentDeformationChain.value R h2 n nu j
  A U V f g h hH T hProper).

(** Source for [current_affine_homotopy_maximum_bound]: the
    mass estimates invoked in the proof of Federer 4.1.13,
    p. 370, give M(chain T)<=||T||(|g-f|rho^j).
    This is the already proved last inequality of 4.1.9,
    p. 364, with its exact endpoint maximum rewritten.
    No finite-integral premise or extra separability is used. *)
Theorem current_affine_homotopy_maximum_bound:
  is_measure_integral beta (real_total_integrand Weight) Value /\
    (@CurrentMass.value R h2 nu (1+j)%N V hV chain<=Value)%E.
Proof.
have hMax:Max=Weight.
  apply:funext=>x;rewrite /homotopy_affine_power_maximum.
  congr (_*_);apply:nonnegative_maximum_power.
  - exact:(real_seminorm_nonnegative (@euclidean_operator_norm_is_norm R n nu).1 _).
  - exact:(real_seminorm_nonnegative (@euclidean_operator_norm_is_norm R n nu).1 _).
have hEst:=@current_affine_homotopy_mass_estimates R h2 n nu j
  A U V f g h hH T hT hAffine hProper.
rewrite hMax in hEst;split;first exact:hEst.2.2.1.
exact:(le_trans hEst.2.2.2.1 hEst.2.2.2.2).
Qed.
End CurrentAffineHomotopyMaximumBound.
