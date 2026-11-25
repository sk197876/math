(** Federer (1969), 4.1.18, p. 377:
    a compact smooth whole-space divergence
    graph with carrier inside U is
    an actual graph pair on the
    original U. Restriction and original differential
    locality retain every pointwise field value. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormOpenDomainLaws
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  ExteriorGrading CurrentDomain CurrentCoefficientNorms CurrentVectorSpaces
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport
  SmoothRestrictionUP SmoothRestrictionSealed SmoothCurrentDivergence
  CurrentLonePairImageUP CompactSummableMultivectors
  CurrentCompactSmoothDivergenceUP CurrentCompactSmoothDivergenceSupport
  CurrentCompactSmoothDivergenceExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section RestrictSmoothGraph.
Variable R : realType.
Hypothesis h2 : (1+1:R)!=0.
Variables n m : nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Z d := (exterior_power X d).
Local Notation N d := (@current_vector_mass R h2 n d).
Local Notation hN d := (@current_vector_mass_real_norm R h2 n d).
Local Notation Full := (fun _ : X => True).
Local Notation hFull := (fun (x : X) (_ : True) =>
  @norm_full_domain_interior R X NX x).
Local Notation F d := (@current_vector_smooth_space R h2 n Full hFull d).
Local Notation fv d := (@current_vector_smooth_value R h2 n Full hFull d).
Local Notation hF d := (@current_vector_smooth_space_laws R h2 n Full hFull d).
Local Notation divF := (@smooth_current_divergence R h2 n m Full hFull).
Variable U : set X.
Hypothesis hU : forall x, U x -> norm_domain_interior NX U x.
Local Notation UT := (current_domain R n U).
Local Notation E d := (@current_vector_smooth_space R h2 n U hU d).
Local Notation ev d := (@current_vector_smooth_value R h2 n U hU d).
Local Notation hE d := (@current_vector_smooth_space_laws R h2 n U hU d).
Local Notation div := (@smooth_current_divergence R h2 n m U hU).
Local Notation P := (@current_lone_pair_space R h2 n m U hU).
Local Notation value d := (@compact_summable_multivector_value R h2 n d U hU).

(** Source for [current_full_smooth_graph_open_restriction]:
    the actual ordinary smoothing graph on
    R^n gives the original compact smooth
    graph pair on U in Federer
    4.1.18, p. 377. The same
    original K bounds the restricted smooth
    field; no agreement is weakened to almost equality. *)
Theorem current_full_smooth_graph_open_restriction
    (f : F m) (g : F m.+1) (K : smooth_compact_set hNX U) :
  f=divF g -> (forall x, ~smooth_compact_carrier K x -> fv m.+1 g x=0) ->
  exists w : P,
    @is_current_compact_smooth_divergence_pair R h2 n m U hU w /\
    value m w.1=(fun x : UT => fv m f (set_val x)) /\
    value m.+1 w.2=(fun x : UT => fv m.+1 g (set_val x)).
Proof.
move=> hGraph hOff.
pose restriction := @SmoothRestriction.operator R X (Z m.+1) NX (N m.+1)
  hNX (hN m.+1) U Full hU (fun _ _ => Logic.I)
  (E m.+1) (F m.+1) (ev m.+1) (fv m.+1) (hE m.+1) (hF m.+1).
have hRestriction := @SmoothRestriction.laws R X (Z m.+1) NX (N m.+1)
  hNX (hN m.+1) U Full hU (fun _ _ => Logic.I)
  (E m.+1) (F m.+1) (ev m.+1) (fv m.+1) (hE m.+1) (hF m.+1).
pose eta := restriction g.
have hSupport : @smooth_function_support R X (Z m.+1) NX hNX U
    (E m.+1) (ev m.+1) eta `<=` smooth_compact_carrier K.
  apply: (smooth_function_compact_support_iff (hE m.+1) K eta).2=> x hx.
  case: (pselect (U x))=> hUx.
  - rewrite (@hRestriction g x hUx); exact: (@hOff x hx).
  - exact: (smooth_function_evaluation_outside (hE m.+1) eta hUx).
have hDivValue := @current_smooth_divergence_restriction_values R h2 n m U hU
  eta g (fun x hx => esym (@hRestriction g x hx)).
have [w [hW [hLeft [hRight hWOff]]]] :=
  @current_compact_smooth_divergence_pair_exists R h2 n m U hU K eta hSupport.
exists w; split; first exact: hW.
split.
- apply: funext=> x; rewrite hLeft hGraph.
  exact: esym (@hDivValue (set_val x) (set_valP x)).
- apply: funext=> x; rewrite hRight.
  exact: (@hRestriction g (set_val x) (set_valP x)).
Qed.
End RestrictSmoothGraph.
