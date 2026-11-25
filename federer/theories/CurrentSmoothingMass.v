(** Federer (1969), 4.1.18, p. 375: the
    original current smoothing has mass at most M(T).
    The already proved unit-kernel uniform norm estimate
    preserves the exact coefficient one. Arbitrary currents
    and infinite mass are retained.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  AlternatingForms CurrentSpaces CurrentCoefficientNorms SmoothTestSpaces
  SmoothTestEvaluation CurrentMassUP CurrentMassSealed CurrentMassBasic
  CurrentGlobalComassSealed CurrentGlobalComassBound ExtendedSupremumUP SmoothingKernelUP SmoothingDilationUP
  SmoothingUniformNormBound CurrentSmoothingOperators.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section CurrentSmoothingMass.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation Y:=(A_m X R^o m).
Local Notation NY:=(@current_form_comass R h2 n m).
Local Notation hNY:=(@current_form_comass_real_norm R h2 n m).
Local Notation E:=(@current_smooth_space R h2 n Full hFull m).
Local Notation ev:=(@current_smooth_value R h2 n Full hFull m).
Local Notation hE:=(@current_smooth_space_laws R h2 n Full hFull m).
Local Notation DT:=(@current_test_space R h2 n Full hFull m).
Local Notation value:=(@current_test_value R h2 n Full hFull m).
Local Notation C:=(@current_space R h2 n Full hFull m).
Local Notation M:=(@CurrentMass.value R h2 n m Full hFull).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Q:=(@current_test_smoothing R h2 n m phi family hPhi hFamily epsilon).
Local Notation Smooth:=(@current_smoothing R h2 n m phi family hPhi hFamily).

(** Source for [current_test_smoothing_comass_bound]:
    M(Phi_epsilon*omega)<=M(omega) for the original
    compact tests, supporting the first mass estimate
    in Federer 4.1.18, p. 375. *)
Theorem current_test_smoothing_comass_bound (omega:DT) b:
  (@CurrentGlobalComass.value R h2 n m Full (value omega)<=b%:E)%E ->
  (@CurrentGlobalComass.value R h2 n m Full (value (Q omega))<=b%:E)%E.
Proof.
move=>hBound.
have hPoint:=(@current_global_comass_bound R h2 n m Full (value omega) b).1 hBound.
apply:(@current_global_comass_bound R h2 n m Full (value (Q omega)) b).2=>x _.
change (NY (ev (smooth_test_inclusion hE (Q omega)) x)<=b).
rewrite (@current_test_smoothing_inclusion R h2 n m phi family hPhi hFamily
  epsilon hEpsilon omega).
apply:(@smoothing_uniform_norm_bound R n Y NY hNY phi hPhi family hFamily
  epsilon (value omega)
  (ev (@current_smooth_smoothing R h2 n m phi family hPhi hFamily epsilon
    (smooth_test_inclusion hE omega))) b hEpsilon).
- exact:(@current_smooth_smoothing_convolution R h2 n m phi family hPhi hFamily
    epsilon hEpsilon (smooth_test_inclusion hE omega)).
- by move=>z;exact:hPoint z Logic.I.
Qed.

(** Source for [current_smoothing_mass_bound]: the literal
    M(T_epsilon)<=M(T) in Federer 4.1.18,
    p. 375. No finite mass, representation,
    compact support or normality hypothesis is added. *)
Theorem current_smoothing_mass_bound (T:C):
  (M (Smooth T epsilon)<=M T)%E.
Proof.
apply:(extended_supremum_least (@CurrentMass.laws R h2 n m Full hFull
  (Smooth T epsilon)))=>a [omega [hOmega <-]].
rewrite (@current_smoothing_action R h2 n m phi family hPhi hFamily
  T epsilon hEpsilon omega).
apply:current_mass_unit_test_upper.
exact:current_test_smoothing_comass_bound hOmega.
Qed.
End CurrentSmoothingMass.
