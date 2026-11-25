(** Federer (1969), 4.1.18, p. 374: an actual
    continuous current witnesses existence of the averaged
    smoothing deformation. Only the preceding opaque
    Cartesian current and smooth deformation chain are
    used; this construction is not a consumer definition. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps CurrentSpaces CurrentDomainTransport
  CurrentHomotopyUP CurrentHomotopyDomain CurrentTranslationParameterHomotopy CurrentKernelParameterInput
  CurrentDeformationChainSealed SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentKernelSmoothingChainWitness.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X:=(R_n R n).
Local Notation Full:=(fun d:nat=>fun _:R_n R d=>True).
Local Notation N d:=(inner_norm (@euclidean_inner_productP R d)).
Local Notation hFull:=(fun (d:nat) (x:R_n R d) (_:True)=>norm_full_domain_interior (N d) x).
Local Notation H:=(@current_translation_parameter_homotopy R n).
Local Notation q:=(@euclidean_last_block_map R n n).
Local Notation End:=(@current_translation_parameter_end R n).
Local Notation hH:=(@current_translation_parameter_homotopy_laws R n).
Local Notation hTarget:=(@current_homotopy_target_open R (n+n)%N n
  (fun _=>True) (Full (n+n)%N) (Full n) q End H hH.1).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation C:=(@current_space R h2 n (Full n) (hFull n) m).
Local Notation Input:=(@current_kernel_parameter_input R h2 n m
  phi family hPhi hFamily epsilon hEpsilon).
Local Notation Proper:=(@current_kernel_parameter_homotopy_proper R h2 n m
  phi family hPhi hFamily epsilon hEpsilon).

(** Source for [current_kernel_smoothing_chain_witness]:
    an actual continuous (m+1)-current realises the
    original compact-kernel homotopy construction in
    4.1.18, p. 374. Current and form action
    laws must subsequently identify its independent
    averaged-transgression specification. *)
Definition current_kernel_smoothing_chain_witness (T:C):
    @current_space R h2 n (Full n) (hFull n) (1+m)%N:=
  @current_domain_transport R h2 n (Full n) hTarget (Full n) (erefl _)
    (hFull n) (1+m)%N
    (@CurrentDeformationChain.value R h2 (n+n)%N n m (fun _=>True)
      (Full (n+n)%N) (Full n) q End H hH (Input T)
      (@current_kernel_parameter_homotopy_proper R h2 n m phi family hPhi hFamily
        epsilon hEpsilon T)).
End CurrentKernelSmoothingChainWitness.
