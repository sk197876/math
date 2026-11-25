(** Federer (1969), 4.1.25, p. 383: the smooth
    images used in the first displayed action converge to
    the actual Lipschitz image of the L1 density current.
    Apply the original universal law of 4.1.14, p. 370;
    no finite boundary mass or normality is required. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  LipschitzUP SmoothCompactSet CurrentSpaces FlatCurrentsUP
  CompactSummableMultivectors CompactSummableMultivectorDensity
  CurrentLipschitzCompactImage CurrentCompactPushforwardAlgebra
  CurrentSmoothApproximationUP CurrentFlatLipschitzPushforwardUP
  CurrentFlatLipschitzPushforwardSealed CurrentLipschitzImageOriginalApproximation
  CurrentWeakSequenceLimit CurrentLipschitzLebesgueActionDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

Section LebesgueActionApproximation.
Variable R : realType.
Hypothesis h2 : (1+1:R) != 0.
Variables m n k : nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R m)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation FullX := (fun _ : X => True).
Local Notation FullY := (fun _ : Y => True).
Local Notation hFullX := (fun (x:X) (_:True) => norm_full_domain_interior NX x).
Local Notation hFullY := (fun (y:Y) (_:True) => norm_full_domain_interior NY y).
Variable xi : @compact_summable_multivector_space R h2 m k FullX hFullX.
Local Notation T := (@compact_summable_multivector_current R h2 m k FullX hFullX xi).
Local Notation hFlat := (@current_lipschitz_lebesgue_action_density_flat
  R h2 m k FullX hFullX xi).
Variable f : X -> Y.
Hypothesis hLocal : @is_locally_metric_lipschitz R
  (real_norm_metric_space hNX) (real_norm_metric_space hNY) FullX f.
Local Notation hImage := (fun (x:X) (_:True) => Logic.I).
Local Notation Q := (@CurrentFlatLipschitzPushforward.value R h2 m n k
  FullX FullY hFullX hFullY f hImage hLocal T hFlat).
Variable K : smooth_compact_set hNX FullX.
Hypothesis hK : @is_flat_current_supported_in R h2 m k FullX hFullX K T.
Variable g : nat -> X -> Y.
Hypothesis hG : @is_current_smooth_approximation R m n FullX FullY K f g.
Local Notation hCompact := (@flat_supported_current_compact R h2 m k FullX hFullX K T hK).

(** Source for [current_lipschitz_lebesgue_action_image_approximation]:
    every original smooth family converges to the actual
    opaque Lipschitz pushforward on every compact target test,
    supporting the smoothing proof of 4.1.25, p. 383.
    K is an internal supporting index in this adapter;
    the density field itself is the only current input. *)
Theorem current_lipschitz_lebesgue_action_image_approximation :
  @is_current_weak_sequence_limit R h2 n k FullY hFullY
    (fun i => @current_compact_map_pushforward R h2 m n FullX FullY hFullX hFullY
      (g i) (current_smooth_approximation_image hG i)
      (current_smooth_approximation_class hG i) k T hCompact) Q.
Proof.
exact: (@current_lipschitz_image_original_approximation_weak R h2 m n k
  FullX FullY hFullX hFullY f hImage hLocal K T hK Q
  ((@CurrentFlatLipschitzPushforward.laws R h2 m n k
    FullX FullY hFullX hFullY f hImage hLocal T hFlat).2 K hK) g hG).
Qed.
End LebesgueActionApproximation.
