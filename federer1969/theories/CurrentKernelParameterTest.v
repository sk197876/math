(** Federer (1969), 4.1.18, p. 374: the
    parameter-product input acts on the same genuine
    compact test in each equal-domain presentation.
    These are equality adapters only; the original
    Cartesian product stays opaque. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentDomainTransport
  CurrentEqualDomainTests CurrentCartesianDomain CurrentCartesianProductSealed
  CurrentAmbientCartesianProduct CurrentHomotopyUP CurrentHomotopyDomain
  CurrentTranslationParameterHomotopy CurrentKernelParameterInput
  CurrentKernelAverageSealed SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentKernelParameterTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Full:=(fun d:nat=>fun _:R_n R d=>True).
Local Notation N d:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hFull:=(fun (d:nat) (x:R_n R d) (_:True)=>norm_full_domain_interior (N d) x).
Local Notation AB:=(@euclidean_cartesian_set R n n (Full n) (Full n)).
Local Notation hAB:=(@current_cartesian_domain_open R n n (Full n) (Full n) (hFull n) (hFull n)).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH.1).
Local Notation D:=(@current_test_space R h2 (n+n)%N (Full (n+n)%N) hSource m).
Local Notation DAB:=(@current_test_space R h2 (n+n)%N AB hAB m).

(** Source for [current_kernel_parameter_test]: exact
    identification of the same original compact
    test with its Cartesian-domain presentation,
    supporting 4.1.18, p. 374. *)
Definition current_kernel_parameter_test:Hom D DAB:=
  hom_comp
    (@current_test_equal_domain R h2 (n+n)%N m (Full (n+n)%N) AB
      (hFull (n+n)%N) hAB (esym (@current_cartesian_full_domain R n n)))
    (@current_test_equal_domain R h2 (n+n)%N m (Full (n+n)%N) (Full (n+n)%N)
      hSource (hFull (n+n)%N) (erefl _)).

(** Source for [current_kernel_parameter_test_values]:
    the original actual coefficients are unchanged,
    supporting the averaged action in 4.1.18,
    p. 374. *)
Theorem current_kernel_parameter_test_values (beta:D) a:
  @current_test_value R h2 (n+n)%N AB hAB m (current_kernel_parameter_test beta) a=
  @current_test_value R h2 (n+n)%N (Full (n+n)%N) hSource m beta a.
Proof.
by rewrite /current_kernel_parameter_test hom_compE !current_test_equal_domain_values.
Qed.

Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).

(** Source for [current_kernel_parameter_input_action]:
    the actual product's original compact-test action
    is invariant under the equality adapters used
    in the smoothing witness, 4.1.18, p. 374. *)
Theorem current_kernel_parameter_input_action
    (T:@current_space R h2 n (Full n) (hFull n) m) (beta:D):
  @current_value R h2 (n+n)%N (Full (n+n)%N) hSource m
    (@current_kernel_parameter_input R h2 n m phi family hPhi hFamily epsilon hEpsilon T) beta=
  @current_value R h2 (n+n)%N AB hAB m
    (@CartesianCurrentProduct.value R h2 n n 0%N m
      (Full n) (Full n) (hFull n) (hFull n) S T)
    (current_kernel_parameter_test beta).
Proof.
rewrite /current_kernel_parameter_input current_equal_domain_test_action_reverse
  /current_ambient_cartesian_product current_equal_domain_test_action_reverse.
reflexivity.
Qed.
End CurrentKernelParameterTest.
