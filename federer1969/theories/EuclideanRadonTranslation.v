(** Federer (1969), 4.1.18, p. 375: literal
    translated images of the original full-domain
    Radon measure remain Radon and integrate a
    compact scalar test by its translated pullback.
    This is 2.4.18 together with proper translation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct CurrentDomain
  FiniteNormCompactHull FiniteNormEquivalence IsotropyGroupTopology ProperMapUP
  EuclideanTranslatedCompactFunctions MeasureUP MeasurePushforward RadonMeasureUP
  RadonProperPushforward RadonWeightedPushforwardIntegral MeasureIntegralUP MeasureIntegralUniqueness
  RadonCompactScalarIntegral FunctionLatticeUP CompactSupportFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanRadonTranslation.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation XT:=(real_norm_metric_space hNX).
Local Notation Full:=(fun _:X=>True).
Local Notation FT:=(current_domain R n Full).
Variable beta:set FT->\bar R.
Hypotheses (hBeta:is_measure beta) (hBetaRadon:is_radon_measure beta).
Variable z:X.
Local Notation tau:=(fun x:FT=>(set_val x+z:XT)).

(** Source for [euclidean_radon_translation]: the
    literal tau_z#beta after the canonical inclusion
    of the full current domain, supporting the
    translated variation average in 4.1.18, p. 375. *)
Definition euclidean_radon_translation:set XT->\bar R:=measure_pushforward tau beta.

(** Source for [euclidean_radon_translation_laws]:
    proper translation preserves the original Radon
    measure, supporting 4.1.18, p. 375. Infinite
    total measure and dimension zero are allowed. *)
Theorem euclidean_radon_translation_laws:
  is_measure euclidean_radon_translation /\is_radon_measure euclidean_radon_translation.
Proof.
have hContinuous:continuous tau.
  move=>x;exact:(continuous_comp (@set_type_val_continuous XT Full x)
    (@norm_translation_continuous R X NX hNX z (set_val x))).
have hProper:is_proper_map tau.
  move=>K hK.
  pose L:set XT:=(fun x:XT=>x-z) @` K.
  have hL:compact L.
    apply:continuous_compact hK.
    exact:continuous_subspaceT (@norm_translation_continuous R X NX hNX (-z)).
  have hIn:L `<=` Full by move=>x _.
  have hCopy:=@set_type_compact_preimage XT Full L hL hIn.
  have hEqual:tau @^-1` K=(set_val @^-1` L:set FT).
    apply:funext=>x;apply:propext;split.
    - move=>hx;exists (set_val x+z);first exact:hx.
      by rewrite addrK.
    - move=>[y hy hValue].
      have hBack:set_val x+z= y by rewrite -hValue subrK.
      change (K (set_val x+z)).
      by rewrite hBack.
  by rewrite hEqual.
split;first exact:measure_pushforward_is_measure hBeta.
exact:(@proper_continuous_radon_pushforward R FT XT beta hBeta hBetaRadon tau
  (@metric_hausdorff R XT)
  (@finite_norm_locally_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) NX hNX)
  hContinuous hProper).
Qed.

(** Source for [euclidean_radon_translation_compact_value]:
    the compact test integral of the original
    translated image equals its literal source
    pullback integral, by 2.4.18, supporting
    Federer 4.1.18, p. 375. *)
Theorem euclidean_radon_translation_compact_value (f:XT->R):
  positive_function_lattice (@compactly_supported_continuous_functions R XT) f ->
  @radon_positive_compact_integral R XT euclidean_radon_translation
    euclidean_radon_translation_laws.1 euclidean_radon_translation_laws.2 f=
    @radon_positive_compact_integral R FT beta hBeta hBetaRadon
      (fun x:FT=>f (set_val x+z)).
Proof.
move=>hF.
have hSource:=@radon_positive_compact_integral_laws R FT beta hBeta hBetaRadon
  (fun x:FT=>f (set_val x+z))
  (@euclidean_full_translated_positive_compact R n f z hF).
have hImage:=(@real_total_pushforward_integral_iff R FT XT beta hBeta tau f hSource.1 _).1 hSource.
exact:(EFin_inj (measure_integral_unique
  (@radon_positive_compact_integral_laws R XT euclidean_radon_translation
    euclidean_radon_translation_laws.1 euclidean_radon_translation_laws.2 f hF) hImage)).
Qed.
End EuclideanRadonTranslation.
Arguments euclidean_radon_translation : clear implicits.
