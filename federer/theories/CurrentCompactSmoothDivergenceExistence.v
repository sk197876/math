(** Federer (1969), 4.1.18, p. 377: every
    original compact smooth eta gives the
    literal Omega pair (div eta,eta).
    The earlier first-order support law and
    compact smooth L1 membership retain the same K. *)
From mathcomp Require Import all_boot all_order all_algebra
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothCurrentDivergence CompactSummableMultivectors
  CompactSummableMultivectorSmoothField CurrentLonePairImageUP
  CurrentCompactSmoothDivergenceUP CurrentCompactSmoothDivergenceSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section GraphExistence.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).

(** Source for [current_compact_smooth_divergence_pair_exists]:
    the graph set in Federer 4.1.18,
    p. 377, contains the actual pair
    associated with every original compact smooth
    eta. Both fields vanish outside its
    same original K, and all values are exact. *)
Theorem current_compact_smooth_divergence_pair_exists
    (K : smooth_compact_set hNX U) (eta : E m.+1) :
  @smooth_function_support R X (exterior_power X m.+1) NX hNX U
    (E m.+1) (ev m.+1) eta `<=` smooth_compact_carrier K ->
  exists v : P,
    @is_current_compact_smooth_divergence_pair R h2 n m U hU v /\
    value m v.1=(fun x : UT => ev m (div eta) (set_val x)) /\
    value m.+1 v.2=(fun x : UT => ev m.+1 eta (set_val x)) /\
    forall x : UT, ~smooth_compact_carrier K (set_val x) ->
      value m v.1 x=0 /\ value m.+1 v.2 x=0.
Proof.
move=> hSupport.
have hDivSupport := @current_compact_smooth_divergence_support R h2 n m
  U hU K eta hSupport.
have hOff x (hx : U x) (hK : ~smooth_compact_carrier K x) :
    ev m.+1 eta x=0.
  exact: ((smooth_function_compact_support_iff (hE m.+1) K eta).1 hSupport x hK).
have hDivOff x (hx : U x) (hK : ~smooth_compact_carrier K x) :
    ev m (div eta) x=0.
  exact: ((smooth_function_compact_support_iff (hE m) K (div eta)).1
    hDivSupport x hK).
have [xi hXi] := @compact_summable_multivector_smooth_field R h2 n m
  U hU (div eta) K hDivOff.
have [zeta hZeta] := @compact_summable_multivector_smooth_field R h2 n m.+1
  U hU eta K hOff.
exists (xi,zeta); split.
- exists eta,K; split; first exact: hSupport.
  by split.
split; first exact: hXi.
split; first exact: hZeta.
move=> x hx; rewrite hXi hZeta; split.
- exact: (@hDivOff (set_val x) (set_valP x) hx).
- exact: (@hOff (set_val x) (set_valP x) hx).
Qed.
End GraphExistence.
