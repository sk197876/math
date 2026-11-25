(** Federer (1969), 4.1.18, p. 376: an independent
    specification of all original iterative choices. Formal stage
    k=0 gives printed i=1. These laws retain normality,
    literal support tubes, both independent error allowances,
    the actual smooth coefficient and every flat residual. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology functions.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP
  NormOpenDomainLaws InnerNorm HilbertFormCompactness GrassmannAbbreviations ExteriorGrading
  EuclideanInnerProduct CurrentDomain CurrentSpaces CurrentVectorSpaces
  CurrentBoundary NormalCurrentsUP CurrentMassSealed CurrentNormalMass
  CurrentFlatNorm FlatCurrentsUP SmoothCompactSet EuclideanClosedSupportTube
  CurrentFlatSmoothingBudgets CurrentSmoothingOperators
  CompactSummableMultivectors CompactSummableMultivectorDensity
  SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IterationSpecification.
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

(** Source for [is_flat_smoothing_iteration]: the full
    sequence of choices displayed in Federer 4.1.18,
    p. 376, specified without using a recursive witness. *)
Record is_flat_smoothing_iteration (K0:KType) (T0:C) (delta:R)
    (K:nat->KType) (T A:nat->C) (S:nat->Next)
    (epsilon:nat->R) (f:nat->V) (xi:nat->W):Prop:={
  (** Source for [flat_smoothing_iteration_initial]: the original
      K_0=K and T_0=T, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_initial:K 0=K0 /\T 0=T0;
  (** Source for [flat_smoothing_iteration_tubes]: each K_i is
      the printed closed neighbourhood, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_tubes:forall k,
    smooth_compact_carrier (K k.+1)=
    @euclidean_closed_support_tube R n (smooth_compact_carrier (K k))
      (flat_smoothing_radius_budget delta k);
  (** Source for [flat_smoothing_iteration_flat]: every original
      residual belongs to its K_i flat class, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_flat:forall k,flat (K k) (T k);
  (** Source for [flat_smoothing_iteration_normal]: both chosen
      currents are normal in K_(i-1), Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_normal:forall k,
    @normal_currents_supported_in R h2 n Full hFull m (K k) (A k) /\
    @normal_currents_supported_in R h2 n Full hFull m.+1 (K k) (S k);
  (** Source for [flat_smoothing_iteration_approximation]: the
      independent normal decomposition error and price,
      Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_approximation:forall k,
    (F (K k) (T k-A k-bd (S k))<
      (flat_smoothing_residual_budget delta k)%:E)%E /\
    (M (A k)+NextM (S k)<F (K k) (T k)+
      (flat_smoothing_price_budget delta k)%:E)%E;
  (** Source for [flat_smoothing_iteration_scales]: the two
      simultaneous radius bounds, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_scales:forall k,
    0<epsilon k /\epsilon k<=flat_smoothing_radius_budget delta k /\
    ((epsilon k)%:E*N (A k)<(flat_smoothing_residual_budget delta k)%:E)%E;
  (** Source for [flat_smoothing_iteration_coefficients]: the
      actual smooth coefficient, exact Lebesgue current,
      support and mass bound, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_coefficients:forall k,
    value (xi k)=(fun x:UT=>vv (f k) (set_val x)) /\
    Smooth (A k) (epsilon k)=image (xi k) /\
    (forall x:UT,~smooth_compact_carrier (K k.+1) (set_val x)->
      value (xi k) x=0) /\((size (xi k))%:E<=M (A k))%E;
  (** Source for [flat_smoothing_iteration_recurrence]: subtract
      the actual smooth density and boundary, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_recurrence:forall k,
    T k.+1=T k-image (xi k)-bd (S k);
  (** Source for [flat_smoothing_iteration_residuals]: the exact
      printed new residual bound, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_residuals:forall k,
    (F (K k.+1) (T k.+1)<(flat_smoothing_price_budget delta k)%:E)%E;
  (** Source for [flat_smoothing_iteration_prices]: the actual
      field size and filling price, Federer 4.1.18, p. 376. *)
  flat_smoothing_iteration_prices:forall k,
    ((size (xi k))%:E+NextM (S k)<F (K k) (T k)+
      (flat_smoothing_price_budget delta k)%:E)%E
}.
End IterationSpecification.
