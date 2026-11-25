(** Federer (1969), 4.1.18, p. 374: inside
    the existence proof, the compact kernel zero-current
    times an arbitrary T supplies the spatial input
    for h(t,z,x)=x+t z. Equality transport aligns
    the original open-domain proofs internally.  *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import ProperMapUP Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap CurrentSpaces CurrentDomainTransport
  CurrentCartesianDomain CurrentCartesianProductSealed CurrentCartesianSupportEquality
  CurrentAmbientCartesianProduct FunctionalSupportRelativeClosed
  CurrentWholeSupportClosed CurrentHomotopyUP CurrentHomotopyDomain
  CurrentHomotopyCylinder CurrentCompactTimeCylinder CurrentProperOnContainingSet
  CurrentTranslationParameterHomotopy EuclideanTranslationCylinderProper
  SmoothingKernelUP SmoothingDilationUP CurrentKernelAverageSealed CurrentKernelAverageBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentKernelParameterInput.
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
Local Notation geometry:=hH.1.
Local Notation hSource:=(@current_homotopy_source_open R (n+n)%N n
  (fun _=>True) (Full (n+n)%N) (Full n) q End H geometry).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation S:=(@CurrentKernelAverage.value R h2 n phi family hPhi hFamily epsilon hEpsilon).
Local Notation C:=(@current_space R h2 n (Full n) (hFull n) m).

(** Source for [current_kernel_parameter_input]: a witness
    current used only to prove existence of the original
    smoothing deformation in 4.1.18, p. 374. The
    current T remains arbitrary; no private proof object
    or analytic hypothesis is introduced. *)
Definition current_kernel_parameter_input (T:C):
    @current_space R h2 (n+n)%N (Full (n+n)%N) hSource m:=
  @current_domain_transport R h2 (n+n)%N (Full (n+n)%N) (hFull (n+n)%N)
    (Full (n+n)%N) (erefl _) hSource m
    (@current_ambient_cartesian_product R h2 n n 0%N m S T).
Local Notation Input:=current_kernel_parameter_input.

(** Source for [current_kernel_parameter_input_support]:
    the actual witness support is exactly the kernel
    support times the original support, from 4.1.8,
    p. 360, supporting 4.1.18, p. 374. *)
Theorem current_kernel_parameter_input_support (T:C):
  @current_support R h2 (n+n)%N (Full (n+n)%N) hSource m (Input T)=
    @euclidean_cartesian_set R n n
      (@current_support R h2 n (Full n) (hFull n) 0%N S)
      (@current_support R h2 n (Full n) (hFull n) m T).
Proof.
rewrite /current_kernel_parameter_input current_domain_transport_support
  /current_ambient_cartesian_product current_domain_transport_support.
exact:(@current_cartesian_support R h2 n n 0%N m
  (Full n) (Full n) (hFull n) (hFull n) S T).
Qed.

(** Source for [current_kernel_parameter_input_bound]:
    the kernel parameter stays in the literal closed
    epsilon ball, supporting the original properness
    and support bounds in 4.1.18, pp. 374–375. *)
Theorem current_kernel_parameter_input_bound (T:C) a:
  @current_support R h2 (n+n)%N (Full (n+n)%N) hSource m (Input T) a ->
    N n (@euclidean_first_block_map R n n a)<=epsilon.
Proof.
rewrite current_kernel_parameter_input_support=>ha.
have hKernel:=@current_kernel_average_support R h2 n phi family hPhi hFamily
  epsilon hEpsilon (@euclidean_first_block_map R n n a) ha.1.
by rewrite current_kernel_average_index_carrier in hKernel.
Qed.

(** Source for [current_kernel_parameter_homotopy_proper]:
    uniform compact-kernel control proves exactly the
    printed closed-cylinder properness for the actual
    witness current, supporting 4.1.18, p. 374.
    Noncompact original supports are retained. *)
Theorem current_kernel_parameter_homotopy_proper (T:C):
  @is_current_homotopy_proper R h2 (n+n)%N n m (fun _=>True)
    (Full (n+n)%N) (Full n) q End H geometry (Input T).
Proof.
pose Support:=@current_support R h2 (n+n)%N (Full (n+n)%N) hSource m (Input T).
have hClosed:=@current_whole_support_closed R h2 (n+n)%N m hSource (Input T).
have hBound:=fun a ha=>@current_kernel_parameter_input_bound T a ha.
have hProper:=@euclidean_translation_parameter_cylinder_proper R n Support
  hClosed epsilon hBound.
pose Cylinder:=@current_compact_time_cylinder_carrier R (n+n)%N Support.
pose AU:=@current_homotopy_product_domain R (n+n)%N (fun _=>True) (Full (n+n)%N).
pose Actual:=@current_map_on_containing_set R (1+(n+n))%N n AU (Full n) Cylinder
  (@current_homotopy_cylinder_in_domain R h2 (n+n)%N n m (fun _=>True)
    (Full (n+n)%N) (Full n) q End H geometry (Input T)) H
  (@current_homotopy_image R (n+n)%N n (fun _=>True)
    (Full (n+n)%N) (Full n) q End H geometry).
have hMap:Actual=@current_map_on_containing_set R (1+(n+n))%N n
    (Full (1+(n+n))%N) (Full n) Cylinder (fun _ _=>Logic.I) H (fun _ _=>Logic.I).
  apply:funext=>x;apply:val_inj;reflexivity.
change (is_proper_map Actual).
by rewrite hMap.
Qed.
End CurrentKernelParameterInput.
