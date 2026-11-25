(** Federer (1969), 4.1.19, p. 377:
    almost changes of either representing form
    preserve the two original Omega actions.
    Conversely those actions determine beta on
    the whole original pair space by linearity. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingPairing CurrentDomain CurrentCoefficientNorms CurrentLonePairImageUP
  CompactSummableMultivectors EuclideanOpenDomainMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP
  MeasureIntegralAlmostEquality MeasureIntegralUniqueness PartialFunctionBasic
  SummableRealFunctionUP FlatCochainRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section PairAlmost.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).

(** Source for [lone_pair_form_density_almost_invariant]:
    the almost-everywhere classes of the two
    forms are what their original Omega
    actions determine, supporting Federer 4.1.19,
    p. 377. Both new representatives
    retain the original bounded measurability premise. *)
Theorem lone_pair_form_density_almost_invariant (beta : Hom P R^o)
    (phi phi' : UT -> A_m X R^o m)
    (psi psi' : UT -> A_m X R^o m.+1) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  @is_bounded_measurable_current_form R h2 n U m phi' ->
  @is_bounded_measurable_current_form R h2 n U m.+1 psi' ->
  measure_almost_everywhere mu [set x | phi x=phi' x] ->
  measure_almost_everywhere mu [set x | psi x=psi' x] ->
  @is_lone_pair_form_density R h2 n m U hU beta phi' psi'.
Proof.
move=> [hPhi [hPsi [hLeft hRight]]] hPhi' hPsi' hPhiAlmost hPsiAlmost.
split; first exact: hPhi'.
split; first exact: hPsi'.
split.
- move=> xi; apply: (@measure_integral_almost_equal R UT mu hMu _ _ _
    (@hLeft xi)).
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hPhiAlmost)=> x hx.
  exists (pairing (value m xi x) (phi x))%:E.
  split; apply/real_total_integrand_graph; first exact: erefl.
  by rewrite hx.
- move=> eta; apply: (@measure_integral_almost_equal R UT mu hMu _ _ _
    (@hRight eta)).
  apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hPsiAlmost)=> x hx.
  exists (pairing (value m.+1 eta x) (psi x))%:E.
  split; apply/real_total_integrand_graph; first exact: erefl.
  by rewrite hx.
Qed.

(** Source for [lone_pair_form_functional_unique]:
    the two original form action identities
    determine the whole beta of Federer
    4.1.19, p. 377. Test each
    factor separately and add their actual
    linear values; no norm equality is assumed. *)
Theorem lone_pair_form_functional_unique (beta gamma : Hom P R^o)
    (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1) :
  @is_lone_pair_form_density R h2 n m U hU beta phi psi ->
  @is_lone_pair_form_density R h2 n m U hU gamma phi psi -> beta=gamma.
Proof.
move=> hBeta hGamma; apply: hom_ext=> v.
have hLeft : beta (v.1,0)=gamma (v.1,0).
  exact: (EFin_inj (measure_integral_unique
    (hBeta.2.2.1 v.1) (hGamma.2.2.1 v.1))).
have hRight : beta (0,v.2)=gamma (0,v.2).
  exact: (EFin_inj (measure_integral_unique
    (hBeta.2.2.2 v.2) (hGamma.2.2.2 v.2))).
have hPair : ((v.1,0):P)+(0,v.2)=v.
  apply: injective_projections.
  - change (v.1+0=v.1); exact: addr0.
  - change (0+v.2=v.2); exact: add0r.
have hBetaSplit := eq_trans (congr1 beta (esym hPair))
  (linD (hom_linear beta) (v.1,0) (0,v.2)).
have hGammaSplit := eq_trans (congr1 gamma (esym hPair))
  (linD (hom_linear gamma) (v.1,0) (0,v.2)).
by rewrite hBetaSplit hGammaSplit hLeft hRight.
Qed.
End PairAlmost.
