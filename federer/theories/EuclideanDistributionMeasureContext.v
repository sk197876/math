(** Federer (1969), 4.1.1, p. 346: the
    actual Euclidean Lebesgue measure satisfies
    every measure premise used by the integral
    distribution and integration-by-parts proofs.
    Its topology remains the original Euclidean one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness FiniteNormEquivalence InnerNormTopologyAdapters
  TopologicalBorel BorelFunctionBasic RadonMeasureUP BorelRegularMeasureUP MeasureUP MeasurePushforward
  EuclideanOpenPositiveMass EuclideanAdditiveGroup EuclideanLebesgueDimensions EuclideanLebesgueCompactInner EuclideanLebesgueTranslation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section EuclideanDistributionMeasureContext.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation hInner := (@euclidean_inner_productP R n).
Local Notation N := (inner_norm hInner).
Local Notation hN := (inner_norm_real_norm hInner).
Local Notation NT := (real_norm_metric_space hN).
Local Notation IT := (inner_metric_space hInner).
Local Notation mu := (@euclidean_lebesgue_measure R n).

(** Source for [euclidean_distribution_inner_to_norm]:
    the two presentations of the actual Euclidean
    topology agree, supporting the original
    Lebesgue integral in Federer 4.1.1, p. 346. *)
Lemma euclidean_distribution_inner_to_norm:continuous (fun x:IT=>(x:NT)).
Proof. move=>x A hA; exact:(inner_real_norm_same_nbhs hInner x A).2 hA. Qed.

(** Source for [euclidean_distribution_norm_to_inner]:
    the reverse topology identification for the
    same Euclidean source, supporting Federer
    4.1.1, p. 346. *)
Lemma euclidean_distribution_norm_to_inner:continuous (fun x:NT=>(x:IT)).
Proof. move=>x A hA; exact:(inner_real_norm_same_nbhs hInner x A).1 hA. Qed.

(** Source for [euclidean_distribution_measure_borel]:
    the original Lebesgue measure contains the
    source Borel sets, supporting Federer
    4.1.1, p. 346. *)
Theorem euclidean_distribution_measure_borel (A:set X):
  @borel_set NT A ->measure_measurable mu A.
Proof.
move=>hA.
have hBorel:@borel_set IT A:=borel_function_preimage (continuous_borel_function euclidean_distribution_inner_to_norm) hA.
exact:(borel_regular_borel_measurable (euclidean_lebesgue_is_measure R n)
  (euclidean_lebesgue_borel_regular R n) hBorel).
Qed.

(** Source for [euclidean_distribution_measure_open]:
    open subsets of the original Euclidean source
    are Lebesgue measurable, supporting Federer
    4.1.1, p. 346. *)
Theorem euclidean_distribution_measure_open (A:set X):
  @open NT A ->measure_measurable mu A.
Proof. move=>hA; exact:euclidean_distribution_measure_borel (open_borel_set hA). Qed.

(** Source for [euclidean_distribution_measure_compact_finite]:
    the original Euclidean measure is finite on
    compact supports, including dimension zero,
    supporting Federer 4.1.1, p. 346. *)
Theorem euclidean_distribution_measure_compact_finite (C:set X):
  @compact NT C ->(mu C< +oo)%E.
Proof.
move=>hC.
have hImage:@compact IT ((fun x:NT=>(x:IT)) @` C).
  apply:continuous_compact hC; exact:continuous_subspaceT euclidean_distribution_norm_to_inner.
have hEq:((fun x:NT=>(x:IT)) @` C)=C.
  apply:funext=>x; apply:propext; split; [by move=>[y hy <-]|by move=>hx; exists x].
rewrite hEq in hImage.
exact:(radon_compact_finite (euclidean_lebesgue_radon R n) hImage).
Qed.

(** Source for [euclidean_distribution_measure_translation]:
    the original Lebesgue measure is invariant
    under x |-> x+c, supporting the derivative
    integral in Federer 4.1.1, p. 346. *)
Theorem euclidean_distribution_measure_translation c:
  measure_pushforward (fun x:X=>x+c) mu=mu.
Proof.
have hEq:(fun x:X=>x+c)=(@euclidean_translation R n c) by apply:funext=>x; exact:addrC.
rewrite hEq; exact:euclidean_lebesgue_translation_pushforward.
Qed.
(** Source for [euclidean_distribution_measure_open_positive]:
    every nonempty source-open set has positive
    Lebesgue measure, supporting the noncompact
    distribution support in Federer 4.1.1, p. 345. *)
Theorem euclidean_distribution_measure_open_positive (A:set X) x:
  @open NT A ->A x ->(0<mu A)%E.
Proof.
move=>hA hx.
apply:(@euclidean_open_positive_mass R n A x _ hx).
exact:(inner_norm_openP hInner A).2 hA.
Qed.
End EuclideanDistributionMeasureContext.
