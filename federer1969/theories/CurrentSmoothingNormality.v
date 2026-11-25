(** Federer (1969), 4.1.18, pp. 375–376:
    original smoothings are locally normal and,
    for compact input, normal. Their actual normal
    masses do not exceed those of the input.
    These are the original normal approximants used
    in the printed representation argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentSpaces CurrentBoundary CurrentIntegrationCriterion CurrentMassSealed CurrentNormalMass NormalCurrentsUP CurrentSmoothingOperators
  CurrentSmoothingRepresentable CurrentSmoothingExteriorDerivative
  CurrentSmoothingMass CurrentSmoothingSupportTube SmoothingKernelUP SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentSmoothingNormality.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Full:=(fun _:X=>True).
Local Notation hFull:=(fun (x:X) (_:True)=>norm_full_domain_interior NX x).
Local Notation C:=(fun d=>@current_space R h2 n Full hFull d).
Variables (phi:X->R) (family:R->X->R).
Hypothesis hPhi:is_smoothing_kernel phi.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable epsilon:R.
Hypothesis hEpsilon:0<epsilon.
Local Notation Smooth:=(fun d (T:C d)=>
  @current_smoothing R h2 n d phi family hPhi hFamily T epsilon).

(** Source for [current_smoothing_locally_normal]: the
    original smooth density and its boundary
    are representable for every input current,
    supporting 4.1.18, pp. 375–376. *)
Theorem current_smoothing_locally_normal m (T:C m):
  @is_locally_normal_current R h2 n Full hFull m (Smooth m T).
Proof.
case:m T=>[|j] T;split.
- exact:(@current_smoothing_representable R h2 n 0%N phi family hPhi hFamily T epsilon hEpsilon).
- exact:Logic.I.
- exact:(@current_smoothing_representable R h2 n j.+1 phi family hPhi hFamily T epsilon hEpsilon).
- change (@is_integration_representable_current R h2 n j Full hFull
    (@current_boundary R h2 n j Full hFull (Smooth j.+1 T))).
  rewrite current_smoothing_boundary_commutation //.
  exact:(@current_smoothing_representable R h2 n j phi family hPhi hFamily
    (@current_boundary R h2 n j Full hFull T) epsilon hEpsilon).
Qed.

(** Source for [current_smoothing_normal]: compact input
    gives original compact normal smoothing,
    supporting the printed approximation in
    Federer 4.1.18, pp. 375–376. *)
Theorem current_smoothing_normal m (T:C m):
  @compact (real_norm_metric_space hNX)
    (@current_support R h2 n Full hFull m T) ->
  @is_normal_current R h2 n Full hFull m (Smooth m T).
Proof.
move=>hCompact;split;first exact:current_smoothing_locally_normal.
exact:(@current_smoothing_compact R h2 n m phi family hPhi hFamily epsilon hEpsilon T hCompact).
Qed.

(** Source for [current_smoothing_normal_mass_bound]: the
    two original sharp mass contractions give
    N(T_epsilon)<=N(T), supporting the normal
    approximation and homotopy bounds of
    Federer 4.1.18, pp. 375–376. *)
Theorem current_smoothing_normal_mass_bound m (T:C m):
  (@current_normal_mass R h2 n Full hFull m (Smooth m T)<=
    @current_normal_mass R h2 n Full hFull m T)%E.
Proof.
case:m T=>[|j] T.
- exact:(@current_smoothing_mass_bound R h2 n 0%N phi family hPhi hFamily epsilon hEpsilon T).
- change ((@CurrentMass.value R h2 n j.+1 Full hFull (Smooth j.+1 T)+
    @CurrentMass.value R h2 n j Full hFull
      (@current_boundary R h2 n j Full hFull (Smooth j.+1 T)))<=
    (@CurrentMass.value R h2 n j.+1 Full hFull T+
      @CurrentMass.value R h2 n j Full hFull
        (@current_boundary R h2 n j Full hFull T)))%E.
  rewrite current_smoothing_boundary_commutation //.
  exact:leeD
    (@current_smoothing_mass_bound R h2 n j.+1 phi family hPhi hFamily epsilon hEpsilon T)
    (@current_smoothing_mass_bound R h2 n j phi family hPhi hFamily epsilon hEpsilon
      (@current_boundary R h2 n j Full hFull T)).
Qed.
End CurrentSmoothingNormality.
