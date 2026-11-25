(** Federer (1969), 4.1.19, p. 377: the
    printed weak equation says exactly that
    beta vanishes on the original compact
    smooth graph pairs of 4.1.18.
    Derive this equivalence from the two
    actual integral actions and their proven finite values. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Bilinear AlternatingForms Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading AlternatingPairing CurrentDomain CurrentCoefficientNorms
  CurrentVectorSpaces SmoothCompactSet SmoothFunctionSupport
  SmoothCurrentDivergence EuclideanOpenDomainMeasure CurrentLonePairImageUP
  CompactSummableMultivectors CurrentCompactSmoothDivergenceUP
  CurrentCompactSmoothDivergenceExistence MeasureIntegralUP
  MeasureIntegralUniqueness SummableRealFunctionUP SummableRealArithmetic
  FlatCochainRepresentationUP CurrentWeakExteriorPairUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeakGraphAction.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation graph :=
  (@is_current_compact_smooth_divergence_pair R h2 n m U hU).
Variable beta : Hom P R^o.
Variables (phi : UT -> A_m X R^o m) (psi : UT -> A_m X R^o m.+1).
Hypothesis hDensity : @is_lone_pair_form_density R h2 n m U hU beta phi psi.

(** Source for [weak_exterior_pair_graph_action_iff]:
    the original weak equation is equivalent
    to beta[div eta,eta]=0 for every original
    graph pair, supporting both directions in
    Federer 4.1.19, p. 377.
    Compact Omega membership and integral existence
    are derived from the preceding exact laws. *)
Theorem weak_exterior_pair_graph_action_iff :
  @is_weak_current_exterior_pair R h2 n m U hU phi psi <->
  forall v : P, graph v -> beta v=0.
Proof.
have hBeta (v : P) : beta v=beta (v.1,0)+beta (0,v.2).
  have hPair : ((v.1,0):P)+(0,v.2)=v.
    apply: injective_projections.
    - change (v.1+0=v.1); exact: addr0.
    - change (0+v.2=v.2); exact: add0r.
  exact: (eq_trans (congr1 beta (esym hPair))
    (linD (hom_linear beta) (v.1,0) (0,v.2))).
have hActions (v : P) : is_measure_integral mu
    (real_total_integrand (fun x =>
      pairing (value m v.1 x) (phi x)+pairing (value m.+1 v.2 x) (psi x)))
    (beta v)%:E.
  have hSum := @real_total_integral_add R UT mu hMu
    (fun x => pairing (value m v.1 x) (phi x))
    (fun x => pairing (value m.+1 v.2 x) (psi x))
    (beta (v.1,0)) (beta (0,v.2))
    (hDensity.2.2.1 v.1) (hDensity.2.2.2 v.2).
  by rewrite -(hBeta v) in hSum.
split.
- move=> hWeak v [eta [K [hSupport [hLeft hRight]]]].
  have hActual := hActions v.
  rewrite hLeft hRight in hActual.
  exact: (EFin_inj (measure_integral_unique hActual (@hWeak eta K hSupport))).
- move=> hGraph eta K hSupport.
  have [v [hV [hLeft [hRight hOff]]]] :=
    @current_compact_smooth_divergence_pair_exists R h2 n m U hU K eta hSupport.
  have hActual := hActions v.
  by rewrite hLeft hRight (hGraph v hV) in hActual.
Qed.
End WeakGraphAction.
