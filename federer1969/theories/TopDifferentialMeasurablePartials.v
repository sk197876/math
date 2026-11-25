(** Federer (1969), 3.1.15, p. 227:
    "by 3.1.4 D D^k f is L^m-measurable on dmn D D^k f": the
    coordinate functions D^alpha f of the top differential are
    continuous on the open domain, their zero extensions are
    measurable, and 3.1.4 gives measurable domains and measurable
    approximate partial derivatives; at a point of ordinary
    differentiability the approximate partials are the ordinary
    ones. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  EuclideanLebesgueDimensions NormDifferentialUP NormDifferentialLocal NormDifferentialFiniteCalculus
  NormClassOneUP NormClassZeroPostcompose NormPartialDerivative
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne NormHigherDifferentialUP
  SymmetricMultiIndices NormHigherMultiPartialUP
  PartialFunctionUP PartialFunctionBasic MeasurableFunctionUP MeasureUP MeasureRestriction
  MeasureCountableClosure ApproximatePartialDerivativeUP ApproximatePartialDerivative
  OrdinaryApproximatePartial EuclideanApproximateDifferentiability
  TopDifferentialStepanoff OpenRestrictionZeroExtensionMeasurable.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section MeasurablePartials.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation Yn := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R m.+1).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable B : set X.
Variable Dk : X->Z k.
Hypothesis hDk : norm_class_zero N (@ZN k) B Dk.

(** Source for [top_coordinate_class_zero]:
    the coordinates D^alpha f of the continuous top differential
    are continuous on the domain, Federer 3.1.11, p. 223. *)
Lemma top_coordinate_class_zero (alpha : symmetric_indices m.+1 k) :
  norm_class_zero N NY B (top_coordinate ev Dk alpha).
Proof.
have hb : norm_bounded_linear (@ZN k) NY (@ev k (norm_multi_partial_arguments R alpha)).
  exists (\prod_(i<k) N (norm_multi_partial_arguments R alpha i)); split.
  - apply: prodr_ge0=>i _; exact: (real_seminorm_nonnegative hN.1).
  - move=>z; rewrite mulrC.
    exact: (multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ k) z)
      (norm_multi_partial_arguments R alpha)).
exact: (norm_class_zero_postcompose (continuous_multilinear_norm_is_norm hNY (@hZ k)) hDk hb).
Qed.

(** Source for [top_extension]:
    the zero extension of D^alpha f to R^m, to which 3.1.4 applies,
    Federer 3.1.15, p. 227. *)
Definition top_extension (alpha : symmetric_indices m.+1 k) : X->Yn :=
  zero_extension B (top_coordinate ev Dk alpha).

(** Source for [top_extension_on]:
    the extension agrees with D^alpha f on the domain. *)
Lemma top_extension_on (alpha : symmetric_indices m.+1 k) x : B x ->
  top_extension alpha x=top_coordinate ev Dk alpha x.
Proof. by move=>hx; rewrite /top_extension /zero_extension; case: pselect. Qed.

(** Source for [top_partial]:
    the approximate partial derivative ap D_i D^alpha f of
    Federer 3.1.2, p. 212, of the extended coordinate,
    as used in 3.1.15, p. 227. *)
Definition top_partial (alpha : symmetric_indices m.+1 k) (i : 'I_m.+1) :
    partial_function X Yn :=
  approximate_partial_derivative hNY setT (top_extension alpha) i.

(** Source for [top_partial_domain]:
    the domain of ap D_i D^alpha f. *)
Definition top_partial_domain (alpha : symmetric_indices m.+1 k) (i : 'I_m.+1) : set X :=
  partial_function_domain (top_partial alpha i).

(** Source for [top_partial_measurable]:
    3.1.4 for the extended coordinate: the domain of each
    approximate partial is measurable and the partial is
    measurable with respect to the restricted measure,
    Federer 3.1.4, p. 214, as used in 3.1.15, p. 227. *)
Theorem top_partial_measurable (alpha : symmetric_indices m.+1 k) (i : 'I_m.+1) :
  measure_measurable Leb (top_partial_domain alpha i) /\
  is_measure_measurable_function (measure_restrict Leb (top_partial_domain alpha i))
    (top_partial alpha i).
Proof.
have hmeas := zero_extension_measurable (top_coordinate_class_zero alpha).
have [hdom [hfun _]] := federer_3_1_4 hmeas.
by split; [exact: (hdom i)|exact: (hfun i)].
Qed.

(** Source for [top_partial_all_domains]:
    the common domain of all approximate partials of all
    coordinates, a measurable set, Federer 3.1.15, p. 227. *)
Definition top_partial_all_domains : set X :=
  \bigcap_(p in [set: symmetric_indices m.+1 k*'I_m.+1]) top_partial_domain p.1 p.2.

(** Source for [top_partial_all_domains_measurable]:
    a finite intersection of measurable sets is measurable,
    Federer 2.1.3, p. 54. *)
Lemma top_partial_all_domains_measurable : measure_measurable Leb top_partial_all_domains.
Proof.
apply: (measure_measurable_countable_intersection (euclidean_lebesgue_is_measure R m.+1)).
- exact: countableP.
- move=>p _; exact: (top_partial_measurable p.1 p.2).1.
Qed.

(** Source for [top_partial_at_differentiability_point]:
    where D^alpha f is differentiable on the open domain, its
    approximate partial derivatives exist and equal the values of
    the differential on the standard vectors, Federer 3.1.2, p. 212,
    and 3.1.1, p. 211, as used in 3.1.15, p. 227. *)
Lemma top_partial_at_differentiability_point (alpha : symmetric_indices m.+1 k)
    (a : X) (L : Hom (R_n R m.+1) (R_n R n)) :
  has_norm_differential N NY B (top_coordinate ev Dk alpha) a L ->
  forall i, partial_function_graph (top_partial alpha i) a (L (@coordinate_basis R m.+1 i)).
Proof.
move=>hL i.
have hL' : has_norm_differential N NY B (top_extension alpha) a L.
  apply: (norm_differential_domain_agreement hN _ hL)=>x hx.
  by rewrite top_extension_on.
have hpartial := norm_differential_partial hN hNY hL' i.
have happ := ordinary_partial_is_approximate hNY hpartial.
exact: (approximate_partial_derivative_graph hNY setT (top_extension alpha) i a _).2 happ.
Qed.

(** Source for [top_partial_all_domains_at_differentiability_point]:
    a point where every coordinate is differentiable lies in the
    common domain, Federer 3.1.15, p. 227. *)
Lemma top_partial_all_domains_at_differentiability_point (a : X) :
  (forall alpha, norm_differentiable_at N NY B (top_coordinate ev Dk alpha) a) ->
  top_partial_all_domains a.
Proof.
move=>hdiff p _.
have [L hL] := hdiff p.1.
exists (L (@coordinate_basis R m.+1 p.2)).
exact: (top_partial_at_differentiability_point hL p.2).
Qed.
End MeasurablePartials.
