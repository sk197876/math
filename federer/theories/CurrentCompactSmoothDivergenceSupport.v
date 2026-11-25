(** Federer (1969), 4.1.18, p. 377: compact
    smooth divergence pairs retain their original
    support K in U. The old first-order
    support and compact zero-extension theorems give
    the required whole-space representatives internally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormOpenDomainLaws NormDifferentialLocal NormDifferentialDirectional
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothCompactDomainInclusion SmoothFunctionSpaceUP
  SmoothFunctionSupport SmoothFirstOrderUP SmoothFirstOrderSealed
  SmoothFirstOrderSupport SmoothCompactZeroExtension CurrentDivergenceMap
  SmoothCurrentDivergence DivergenceUP DivergenceDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section CompactDivergenceSupport.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Z d := (exterior_power X d).
Local Notation N d := (@current_vector_mass R h2 n d).
Local Notation hN d := (@current_vector_mass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU m.+1).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).

(** Source for [current_compact_smooth_divergence_support]:
    div eta is supported in the same
    original K as eta, supporting the
    graph pairs in Federer 4.1.18,
    p. 377. This is the earlier
    general first-order support theorem. *)
Theorem current_compact_smooth_divergence_support
    (K : smooth_compact_set hNX U) (eta : E m.+1) :
  @smooth_function_support R X (Z m.+1) NX hNX U (E m.+1)
    (ev m.+1) eta `<=` smooth_compact_carrier K ->
  @smooth_function_support R X (Z m) NX hNX U (E m)
    (ev m) (div eta) `<=` smooth_compact_carrier K.
Proof.
exact: (@smooth_first_order_preserves_support R X (Z m.+1) (Z m)
  NX (N m.+1) (N m) hNX (hN m.+1) (hN m) U hU
  (E m.+1) (E m) (ev m.+1) (ev m) (hE m.+1) (hE m)
  D hD (@current_divergence_map R h2 n m) div
  (@SmoothFirstOrder.laws R X (Z m.+1) (Z m)
    NX (N m.+1) (N m) hNX (hN m.+1) (hN m) U
    (E m.+1) (E m) (ev m.+1) (ev m) (hE m.+1) (hE m)
    D hD (@current_divergence_map R h2 n m)
    (@current_divergence_map_bounded R h2 n m)) K eta).
Qed.

(** Source for [current_smooth_divergence_restriction_values]:
    an original smooth field and a whole-space
    representative agreeing on U have the same
    actual divergence on U, supporting the
    original graph argument in Federer 4.1.18,
    p. 377. Differential uniqueness proves this
    locality; no derivative agreement is assumed. *)
Theorem current_smooth_divergence_restriction_values
    (eta : E m.+1) (zeta : F m.+1) :
  (forall x, U x -> fv m.+1 zeta x=ev m.+1 eta x) ->
  forall x, U x -> fv m (divF zeta) x=ev m (div eta) x.
Proof.
move=> hValue x hx.
have [L [hL hDivL]] := @smooth_current_divergence_actual R h2 n m
  U hU eta x hx.
have [M [hM hDivM]] := @smooth_current_divergence_actual R h2 n m
  Full hFull zeta x Logic.I.
have hRestricted := @norm_differential_restrict R X (Z m.+1) NX (N m.+1)
  Full U (fv m.+1 zeta) x M (fun _ _ => Logic.I) (@hU x hx) hM.
have hOriginal : has_norm_differential NX (N m.+1) U (ev m.+1 eta) x M.
  apply: (@norm_differential_domain_agreement R X (Z m.+1) NX (N m.+1)
    hNX U (fv m.+1 zeta) (ev m.+1 eta) x M _ hRestricted).
  exact: hValue.
have hSame := norm_differential_unique hNX (hN m.+1) hL hOriginal.
rewrite hSame in hDivL.
exact: (divergence_value_unique hDivM hDivL).
Qed.

End CompactDivergenceSupport.

Section CompactDivergenceZeroExtension.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Z d := (exterior_power X d).
Local Notation N d := (@current_vector_mass R h2 n d).
Local Notation hN d := (@current_vector_mass_real_norm R h2 n d).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation D := (@current_vector_smooth_derivatives R h2 n U hU m.+1).
Local Notation hD := (@current_vector_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).


(** Source for [current_compact_smooth_divergence_zero_extension]:
    both fields in the graph pair extend
    by zero with every original point value
    retained, supporting Federer 4.1.18,
    p. 377. The same K lies
    inside U; no uniform source enlargement
    or global support hypothesis is added. *)
Theorem current_compact_smooth_divergence_zero_extension
    (K : smooth_compact_set hNX U) (eta : E m.+1) :
  @smooth_function_support R X (Z m.+1) NX hNX U (E m.+1)
    (ev m.+1) eta `<=` smooth_compact_carrier K ->
  exists zeta : F m.+1,
    fv m.+1 zeta=ev m.+1 eta /\ fv m (divF zeta)=ev m (div eta).
Proof.
move=> hSupport.
have hGlobal := @smooth_compact_zero_extension_regular R X (Z m.+1)
  NX (N m.+1) hNX (hN m.+1) U (E m.+1) (ev m.+1) (hE m.+1)
  K eta hSupport.
have [zeta hZeta] := @smooth_function_evaluation_surjective R X (Z m.+1)
  NX (N m.+1) hNX (hN m.+1) Full (F m.+1) (fv m.+1) (hF m.+1)
  (ev m.+1 eta) hGlobal.
have hValue : fv m.+1 zeta=ev m.+1 eta.
  apply: funext=> x; exact: (@hZeta x Logic.I).
pose KF := @smooth_compact_domain_inclusion R X NX hNX U Full
  (fun _ _ => Logic.I) K.
have hZetaSupport : @smooth_function_support R X (Z m.+1) NX hNX
    Full (F m.+1) (fv m.+1) zeta `<=` smooth_compact_carrier KF.
  apply: (smooth_function_compact_support_iff (hF m.+1) KF zeta).2=> x hx.
  rewrite hValue.
  exact: ((smooth_function_compact_support_iff (hE m.+1) K eta).1
    hSupport x hx).
have hDivSupport := @current_compact_smooth_divergence_support R h2 n m
  Full hFull KF zeta hZetaSupport.
exists zeta; split; first exact: hValue.
apply: funext=> x; case: (pselect (U x))=> hx.
- apply: current_smooth_divergence_restriction_values=> // y hy.
  by rewrite hValue.
- rewrite (@smooth_function_evaluation_outside R X (Z m) NX (N m)
    hNX (hN m) U (E m) (ev m) (hE m) (div eta) x hx).
  apply: ((smooth_function_compact_support_iff (hF m) KF (divF zeta)).1
    hDivSupport x).
  move=> hxK; exact: (hx (smooth_compact_in_domain K x hxK)).
Qed.
End CompactDivergenceZeroExtension.
