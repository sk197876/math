(** Federer (1969), 4.1.18, p. 376: existence of
    the original iterative choices by successive use of
    the proved normal approximation and smoothing step.
    The independent sequence laws remain the public statement;
    no particular choice or recursive implementation is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations
  EuclideanInnerProduct ExteriorGrading CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP
  CurrentCompactTubeIndex CurrentFlatSmoothingPeel
  CurrentFlatSmoothingIterationUP SuccessiveSelectionSequence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationExistence.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation UT:=(current_domain R n Full).
Local Notation KType:=(smooth_compact_set hNX Full).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation Next:=(@current_space R h2 n Full hFull m.+1).
Local Notation V:=(@current_vector_smooth_space R h2 n Full hFull m).
Local Notation vv:=(@current_vector_smooth_value R h2 n Full hFull m).
Local Notation W:=(@compact_summable_multivector_space R h2 n m Full hFull).
Local Notation value:=(@compact_summable_multivector_value R h2 n m Full hFull).
Local Notation size:=(@compact_summable_multivector_size R h2 n m Full hFull).
Local Notation image:=(@compact_summable_multivector_current R h2 n m Full hFull).
Local Notation bd:=(@current_boundary R h2 n m Full hFull).
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull).
Local Notation NextM:=(@CurrentMass.value R h2 n m.+1 Full hFull).
Local Notation N:=(@current_normal_mass R h2 n Full hFull m).
Local Notation F K:=(@current_flat_norm R h2 n m Full hFull K).
Local Notation flat K:=(@is_flat_current_supported_in R h2 n m Full hFull K).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).


Variables (K0:KType) (T0:C) (delta:R).
Hypothesis hFlat:flat K0 T0.
Hypothesis hDelta:0<delta.
Local Notation State:={K:KType & {T:C | flat K T}}.
Local Notation Outputs:=(C*(Next*(R*(V*W))))%type.
Local Notation stateK s:=(projT1 s).
Local Notation stateT s:=(sval (projT2 s)).
Local Notation outA d:=d.1.
Local Notation outS d:=d.2.1.
Local Notation outEpsilon d:=d.2.2.1.
Local Notation outF d:=d.2.2.2.1.
Local Notation outXi d:=d.2.2.2.2.

(** Source for [flat_smoothing_successor_laws]: the original
    one-step requirements, before any witness selection,
    Federer 4.1.18, p. 376. *)
Local Definition flat_smoothing_successor_laws k (s t:State) (d:Outputs):Prop:=
  smooth_compact_carrier (stateK t)=
    @euclidean_closed_support_tube R n (smooth_compact_carrier (stateK s))
      (flat_smoothing_radius_budget delta k) /\
  @normal_currents_supported_in R h2 n Full hFull m (stateK s) (outA d) /\
  @normal_currents_supported_in R h2 n Full hFull m.+1 (stateK s) (outS d) /\
  (F (stateK s) (stateT s-outA d-bd (outS d))<
    (flat_smoothing_residual_budget delta k)%:E)%E /\
  (M (outA d)+NextM (outS d)<F (stateK s) (stateT s)+
    (flat_smoothing_price_budget delta k)%:E)%E /\
  0<outEpsilon d /\outEpsilon d<=flat_smoothing_radius_budget delta k /\
  ((outEpsilon d)%:E*N (outA d)<(flat_smoothing_residual_budget delta k)%:E)%E /\
  value (outXi d)=(fun x:UT=>vv (outF d) (set_val x)) /\
  Smooth (outA d) (outEpsilon d)=image (outXi d) /\
  (forall x:UT,~smooth_compact_carrier (stateK t) (set_val x)->
    value (outXi d) x=0) /\((size (outXi d))%:E<=M (outA d))%E /\
  stateT t=stateT s-image (outXi d)-bd (outS d) /\
  (F (stateK t) (stateT t)<(flat_smoothing_price_budget delta k)%:E)%E /\
  ((size (outXi d))%:E+NextM (outS d)<F (stateK s) (stateT s)+
    (flat_smoothing_price_budget delta k)%:E)%E.

(** Source for [flat_smoothing_successor_exists]: every flat
    state admits the original next choice, without any
    finite-mass hypothesis, Federer 4.1.18, p. 376. *)
Local Lemma flat_smoothing_successor_exists k (s:State):
  exists t:State,exists d:Outputs,flat_smoothing_successor_laws k s t d.
Proof.
have[hRadius [hPrice hError]]:=@flat_smoothing_budgets_positive R delta k hDelta.
have[A [S [epsilon [f [xi h]]]]]:=
  @current_flat_smoothing_peel R h2 n m phi family hPhi hFamily
    (stateK s) (stateT s) (flat_smoothing_radius_budget delta k)
    (flat_smoothing_residual_budget delta k)
    (flat_smoothing_price_budget delta k) (svalP (projT2 s)) hRadius hError hPrice.
pose E:=@current_compact_closed_tube_index R n Full (stateK s)
  (flat_smoothing_radius_budget delta k) (fun _ _=>Logic.I).
change (  @normal_currents_supported_in R h2 n Full hFull m (stateK s) A /\
  @normal_currents_supported_in R h2 n Full hFull m.+1 (stateK s) S /\
  (F (stateK s) (stateT s-A-bd S)<(flat_smoothing_residual_budget delta k)%:E)%E /\
  (M A+NextM S<F (stateK s) (stateT s)+(flat_smoothing_price_budget delta k)%:E)%E /\
  0<epsilon /\epsilon<=flat_smoothing_radius_budget delta k /\
  (epsilon%:E*N A<(flat_smoothing_residual_budget delta k)%:E)%E /\
  value xi=(fun x:UT=>vv f (set_val x)) /\Smooth A epsilon=image xi /\
  (forall x:UT,~smooth_compact_carrier E (set_val x)->value xi x=0) /\
  ((size xi)%:E<=M A)%E /\flat E (stateT s-image xi-bd S) /\
  (F E (stateT s-image xi-bd S)<(2*flat_smoothing_residual_budget delta k)%:E)%E /\
  ((size xi)%:E+NextM S<F (stateK s) (stateT s)+(flat_smoothing_price_budget delta k)%:E)%E) in h.
move:h=>[hA [hS [hApprox [hCost [hEpsilon [hScale [hSmall [hValue
  [hImage [hOff [hSize [hNextFlat [hResidual hPriceBound]]]]]]]]]]]]].
pose next:State:=existT (fun K=>{T:C | flat K T}) E
  (exist (fun T=>flat E T) (stateT s-image xi-bd S) hNextFlat).
exists next,(A,(S,(epsilon,(f,xi))));unfold flat_smoothing_successor_laws.
have hRatio:=(@flat_smoothing_budget_ratios R delta k).1.
rewrite hRatio in hResidual.
repeat split=>//.
Qed.

(** Source for [flat_smoothing_iteration_exists]: simultaneous
    existence of every original R_i,S_i,epsilon_i,xi_i,K_i,T_i
    with all displayed quantitative laws, Federer 4.1.18, p. 376. *)
Theorem flat_smoothing_iteration_exists:
  exists K:nat->KType,exists T A:nat->C,exists S:nat->Next,
  exists epsilon:nat->R,exists f:nat->V,exists xi:nat->W,
  @is_flat_smoothing_iteration R h2 n m phi family hPhi hFamily
    K0 T0 delta K T A S epsilon f xi.
Proof.
pose initial:State:=existT (fun K=>{T:C | flat K T}) K0
  (exist (fun T=>flat K0 T) T0 hFlat).
pose P:=fun k (s t:State)=>exists d:Outputs,flat_smoothing_successor_laws k s t d.
have hP:forall k s,exists t,P k s t:=flat_smoothing_successor_exists.
have[states [hInitial hStep]]:=@successive_selection_sequence_exists State initial P hP.
pose data k:=sval (constructive_indefinite_description (hStep k)).
have hData k:=svalP (constructive_indefinite_description (hStep k)).
exists (fun k=>stateK (states k)),(fun k=>stateT (states k)),
  (fun k=>outA (data k)),(fun k=>outS (data k)),
  (fun k=>outEpsilon (data k)),(fun k=>outF (data k)),(fun k=>outXi (data k)).
constructor.
- by rewrite hInitial.
- move=>k;exact:(hData k).1.
- move=>k;exact:svalP (projT2 (states k)).
- move=>k;exact:(conj (hData k).2.1 (hData k).2.2.1).
- move=>k;exact:(conj (hData k).2.2.2.1 (hData k).2.2.2.2.1).
- move=>k;exact:(conj (hData k).2.2.2.2.2.1
    (conj (hData k).2.2.2.2.2.2.1 (hData k).2.2.2.2.2.2.2.1)).
- move=>k;exact:(conj (hData k).2.2.2.2.2.2.2.2.1
    (conj (hData k).2.2.2.2.2.2.2.2.2.1
    (conj (hData k).2.2.2.2.2.2.2.2.2.2.1 (hData k).2.2.2.2.2.2.2.2.2.2.2.1))).
- move=>k;exact:(hData k).2.2.2.2.2.2.2.2.2.2.2.2.1.
- move=>k;exact:(hData k).2.2.2.2.2.2.2.2.2.2.2.2.2.1.
- move=>k;exact:(hData k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.
Qed.
End IterationExistence.
