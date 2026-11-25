(** Federer (1969), 4.1.19, p. 377: expand
    an original L1 multivector field in
    its finite coefficient basis. Bounded coordinate
    maps retain L1 membership, and the
    original basis expansion gives an exact identity
    of raw fields, before any almost-equality quotient. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis
  FiniteDualDimension NormDifferentialUP NormFiniteLinearBound
  VectorDaniellHypotheses FiniteNormMetricPolish LocalUniquenessExample
  MeasureUP SummableFieldSealed SummableFieldLaws SummableFieldLinearImage.
From Federer Require Import Annihilator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [summable_field_value_sum]: the
    finite field expansion in Federer 4.1.19,
    p. 377, preserves literal values by
    the pointwise operations of 2.3.8, pp. 78–79. *)
Lemma summable_field_value_sum (R : realType) (X : topologicalType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (I : finType) (f : I -> @SummableField.space R X V N hN mu hm) :
  @summable_field_value R X V N hN mu hm (\sum_i f i) =
    (fun x => \sum_i @summable_field_value R X V N hN mu hm (f i) x).
Proof.
apply: funext=> x.
have hSeq (s : seq I) :
    @summable_field_value R X V N hN mu hm (\sum_(i <- s) f i) x =
      \sum_(i <- s) @summable_field_value R X V N hN mu hm (f i) x.
  elim: s=> [|i s ih].
  - by rewrite !big_nil /summable_field_value !linear0.
  - by rewrite !big_cons summable_field_value_add /= ih.
exact: (hSeq (index_enum I)).
Qed.

(** Source for [summable_finite_basis_decomposition]:
    the exact finite-coordinate decomposition used for
    the bounded-form representation in Federer 4.1.19,
    p. 377. Scalar coordinate maps and
    scalar vector products are actual linear maps
    on the full raw L1 spaces. No
    coordinate maximum norm replaces the original N. *)
Theorem summable_finite_basis_decomposition
    (R : realType) (X : topologicalType) (V : lmodType R)
    (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu)
    d (e : 'I_d -> V) (he : is_basis e) :
  exists C : 'I_d -> Hom (@SummableField.space R X V N hN mu hm)
      (@SummableField.space R X R^o (fun t : R => `|t|%R)
        (scalar_absolute_value_norm R) mu hm),
  exists J : 'I_d -> Hom
      (@SummableField.space R X R^o (fun t : R => `|t|%R)
        (scalar_absolute_value_norm R) mu hm)
      (@SummableField.space R X V N hN mu hm),
    (forall i w x, @summable_field_value R X R^o (fun t : R => `|t|%R)
      (scalar_absolute_value_norm R) mu hm (C i w) x =
      dual_basis he i (@summable_field_value R X V N hN mu hm w x)) /\
    (forall i f x, @summable_field_value R X V N hN mu hm (J i f) x =
      @summable_field_value R X R^o (fun t : R => `|t|%R)
        (scalar_absolute_value_norm R) mu hm f x*:e i) /\
    forall w, w = \sum_i J i (C i w).
Proof.
pose W := @SummableField.space R X V N hN mu hm.
pose S := @SummableField.space R X R^o (fun t : R => `|t|%R)
  (scalar_absolute_value_norm R) mu hm.
pose value := @summable_field_value R X V N hN mu hm.
pose scalarValue := @summable_field_value R X R^o (fun t : R => `|t|%R)
  (scalar_absolute_value_norm R) mu hm.
have hSep : is_separable_normed_space hN.
  exact: (@finite_norm_metric_separable R V N hN d e he).
have hCoordinates (i : 'I_d) : exists C : Hom W S,
    forall w x, scalarValue (C w) x = dual_basis he i (value w x).
  have [c [hC hBound]] := @norm_finite_linear_bounded R V R^o N
    (fun t : R => `|t|%R) hN (scalar_absolute_value_norm R) d e he
    (dual_basis he i).
  have [C [hValues hSize]] := @summable_field_linear_image_exists R X V R^o
    N (fun t : R => `|t|%R) hN (scalar_absolute_value_norm R)
    (@scalar_norm_separable R) mu hm (dual_basis he i) c hC hBound.
  by exists C.
have hProducts (i : 'I_d) : exists J : Hom S W,
    forall f x, value (J f) x = scalarValue f x*:e i.
  have [J [hValues hSize]] := @summable_scalar_orbit_map_exists R X V N hN
    hSep mu hm (e i).
  by exists J.
have [C hC] := choice hCoordinates.
have [J hJ] := choice hProducts.
exists C,J; split; first exact: hC.
split; first exact: hJ.
move=> w; apply: (@summable_field_value_injective R X V N hN mu hm).
rewrite summable_field_value_sum; apply: funext=> x.
have hValues : (\sum_i value (J i (C i w)) x) =
    \sum_i (dual_basis he i (value w x):R)*:e i.
  apply: eq_bigr=> i _; by rewrite (hJ i (C i w) x) (hC i w x).
rewrite hValues; exact: (@basis_vector_expansion R V d e he (value w x)).
Qed.
