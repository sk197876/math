(** Federer (1969), 4.1.19, p. 377: the
    weak equation depends on the original almost
    classes of the two measurable forms. In
    particular an almost representative of the actual
    class-one derivative has the same weak action. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom AlternatingForms RealNormUP NormDifferentialUP NormClassOneUP
  NormRegularity InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct AlternatingPairing ExteriorDerivativeUP
  CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothCurrentDivergence EuclideanOpenDomainMeasure
  MeasureUP MeasureAlmostUP MeasureAlmostBasic PartialFunctionBasic
  MeasureIntegralUP MeasureIntegralAlmostEquality SummableRealFunctionUP
  CurrentWeakExteriorPairUP CurrentClassOneWeakExterior.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section WeakAlmostEquality.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Y d := (A_m X R^o d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation mu := (@euclidean_open_domain_measure R n U).
Local Notation hMu := (proj1 (@euclidean_open_domain_measure_laws R n U hU)).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).

(** Source for [weak_current_exterior_pair_almost_invariant]:
    both original null modifications preserve the
    weak equation in Federer 4.1.19,
    p. 377. This uses the original
    integral almost-invariance of 2.4.3(2), p. 81;
    no pointwise derivative assertion is inferred. *)
Theorem weak_current_exterior_pair_almost_invariant
    (phi phi' : UT -> Y m) (psi psi' : UT -> Y m.+1) :
  @is_weak_current_exterior_pair R h2 n m U hU phi psi ->
  measure_almost_everywhere mu [set x | phi x=phi' x] ->
  measure_almost_everywhere mu [set x | psi x=psi' x] ->
  @is_weak_current_exterior_pair R h2 n m U hU phi' psi'.
Proof.
move=> hWeak hPhi hPsi eta K hSupport.
apply: (@measure_integral_almost_equal R UT mu hMu _ _ _
  (@hWeak eta K hSupport)).
apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _
  (measure_almost_everywhere_and hMu hPhi hPsi))=> x [hLeft hRight].
exists (pairing (ev m (div eta) (set_val x)) (phi x)+
  pairing (ev m.+1 eta (set_val x)) (psi x))%:E.
split; apply/real_total_integrand_graph; first exact: erefl.
by rewrite hLeft hRight.
Qed.

(** Source for [weak_current_exterior_pair_almost_iff]:
    the literal original weak relation in
    Federer 4.1.19, p. 377, is
    invariant in both directions under almost
    equality, including a null or empty domain. *)
Theorem weak_current_exterior_pair_almost_iff
    (phi phi' : UT -> Y m) (psi psi' : UT -> Y m.+1) :
  measure_almost_everywhere mu [set x | phi x=phi' x] ->
  measure_almost_everywhere mu [set x | psi x=psi' x] ->
  (@is_weak_current_exterior_pair R h2 n m U hU phi psi <->
    @is_weak_current_exterior_pair R h2 n m U hU phi' psi').
Proof.
move=> hPhi hPsi; split.
- move=> hWeak.
  exact: (@weak_current_exterior_pair_almost_invariant phi phi' psi psi'
    hWeak hPhi hPsi).
- move=> hWeak.
  apply: (@weak_current_exterior_pair_almost_invariant phi' phi psi' psi hWeak).
  + apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hPhi).
    by move=> x hx; exact: esym hx.
  + apply: (@measure_almost_everywhere_mono R UT mu hMu _ _ _ hPsi).
    by move=> x hx; exact: esym hx.
Qed.

(** Source for [current_class_one_almost_derivative_weak]:
    an arbitrary measurable representative of the
    actual class-one exterior derivative gives the
    same weak equation, supporting the class-one
    parenthesis of Federer 4.1.19, p. 377.
    No continuity or global bound on that
    representative is used for this implication. *)
Theorem current_class_one_almost_derivative_weak
    (phi : X -> Y m) (beta : X -> Y m.+1) (psi : UT -> Y m.+1) :
  norm_class hNX (@current_form_comass_real_norm R h2 n m) U phi 1%N ->
  (forall x, U x -> has_exterior_derivative NX
    (@current_form_comass R h2 n m) U phi x (beta x)) ->
  measure_almost_everywhere mu [set x | beta (set_val x)=psi x] ->
  @is_weak_current_exterior_pair R h2 n m U hU
    (fun x : UT => phi (set_val x)) psi.
Proof.
move=> hClass hActual hAlmost.
apply: (@weak_current_exterior_pair_almost_invariant
  (fun x : UT => phi (set_val x)) (fun x : UT => phi (set_val x))
  (fun x : UT => beta (set_val x)) psi
  (@current_class_one_exterior_weak_integral R h2 n m U hU phi beta hClass hActual)).
- apply: (@measure_almost_everywhere_mono R UT mu hMu setT _ _
    (measure_almost_everywhere_true hMu)); by move=> x _.
- exact: hAlmost.
Qed.
End WeakAlmostEquality.
