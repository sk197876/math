(** Federer (1969), 2.5.10, p. 100: the question "whether there always
    exists a phi measurable function k such that mu(f)=integral f k d phi
    whenever f is phi summable" allows k to take values in the extended real
    numbers. By 2.1.1, p. 51, the product 0 . infinity is undefined unless
    the special convention assigning the value 0 is indicated. Both readings
    are specified below: [is_extended_lattice_density] uses the partial
    product of 2.3.2, p. 74, and [is_zero_product_lattice_density] the
    convention 0 . infinity = 0. In either reading the integral of f k is
    finite, so f k is finite almost everywhere by 2.4.4, p. 82; there f(x)
    k(x) = f(x) fine(k(x)), where fine replaces the infinite values by 0.
    Hence the real function fine o k, which is measurable by 2.3.2, p. 73,
    represents the same functional. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric RealMetricBackground ExtendedRealOrderTopology ExtendedRealPartial
  PartialFunctionUP PartialFunctionBasic PartialExtendedArithmetic MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableTotalBasic BorelFunctionUP ExtendedFiniteProjectionBorel
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureSummableFiniteValues
  SummableRealFunctionUP TotalScalarLpUP TotalScalarMeasurability RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_extended_lattice_density]: the representation
    mu(f)=integral f k d phi for f in L in Federer 2.5.10, p. 100,
    with a phi measurable extended real valued k; the product f k is
    the partial product of 2.3.2, p. 74, undefined where
    0 . infinity occurs (2.1.1, p. 51). *)
Definition is_extended_lattice_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A : (X -> R) -> R) (k : X -> \bar R) :=
  is_measure_measurable_function mu (partial_function_total (k : X -> extended_real_line R)) /\
  forall f, L f -> is_measure_integral mu
    (partial_extended_function_multiply (real_total_integrand f) (partial_function_total k)) (A f)%:E.

(** Source for [is_zero_product_lattice_density]: the same
    representation in Federer 2.5.10, p. 100, read with the special
    convention 0 . infinity = 0 of 2.1.1, p. 51, which is the
    convention of the extended real multiplication of MathComp. *)
Definition is_zero_product_lattice_density (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (L : set (X -> R)) (A : (X -> R) -> R) (k : X -> \bar R) :=
  is_measure_measurable_function mu (partial_function_total (k : X -> extended_real_line R)) /\
  forall f, L f -> is_measure_integral mu
    (partial_function_total (fun x => ((f x)%:E * k x : extended_real_line R))) (A f)%:E.

(** Source for [extended_product_finite_fine]: supporting scalar
    identity for the reduction in Federer 2.5.10, p. 100: if
    r z is finite then r z = r fine(z); for infinite z this forces
    r=0, and both sides vanish under the convention of 2.1.1, p. 51. *)
Lemma extended_product_finite_fine (R : realType) (r : R) (z : \bar R) :
  (r%:E * z) \is a fin_num -> (r * fine z)%:E = r%:E * z.
Proof.
case: z=> [s| |] /= hf.
- by rewrite EFinM.
- case: (ltrgt0P r) hf=> [hr|hr|->].
  + by rewrite mulry gtr0_sg // mul1e.
  + by rewrite mulry ltr0_sg // mulN1e.
  + by rewrite mul0r mul0e.
- case: (ltrgt0P r) hf=> [hr|hr|->].
  + by rewrite mulrNy gtr0_sg // mul1e.
  + by rewrite mulrNy ltr0_sg // mulN1e.
  + by rewrite mul0r mul0e.
Qed.

(** Source for [fine_density_measurable]: supporting measurability
    of fine o k for a measurable extended real k, Federer 2.3.2,
    p. 73, since fine is a Borel function; used for the reduction
    in 2.5.10, p. 100. *)
Lemma fine_density_measurable (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (k : X -> \bar R) :
  is_measure_measurable_function mu (partial_function_total (k : X -> extended_real_line R)) ->
  is_measure_measurable_function mu (total_scalar_function (fun x => fine (k x))).
Proof.
move=> hk; apply: (@real_total_scalar_measurable R X mu hm).
exact: (@measurable_total_borel_postcomposition R X (extended_real_line R)
  [the topologicalType of real_line_metric R] mu hm k (fun y => (fine y : real_line_metric R)) hk
  (@extended_finite_projection_borel R)).
Qed.

(** Source for [extended_lattice_density_real]: in Federer 2.5.10,
    p. 100, an extended real representing function may be replaced
    by a real one: if k represents A on L with the partial product,
    then so does fine o k. *)
Theorem extended_lattice_density_real (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A : (X -> R) -> R)
    (k : X -> \bar R) :
  is_extended_lattice_density mu L A k -> is_real_lattice_density mu L A (fun x => fine (k x)).
Proof.
move=> [hk hrep]; split; first exact: (fine_density_measurable hm hk).
move=> f hf; have hi := hrep f hf.
have hfin := @measure_summable_finite_almost R X mu hm _ (ex_intro _ (A f) hi).
apply: (@measure_integral_almost_equal R X mu hm _ _ _ hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfin)=> x [y [hy hyf]].
exists y; split=> //; apply/real_total_integrand_graph.
have [a [b [ha [hb he]]]] := (partial_extended_function_multiply_graph _ _ x y).1 hy.
have hax : (f x)%:E = a := (real_total_integrand_graph f x a).1 ha.
have hbx : k x = b := hb.
rewrite /extended_multiply in he.
case hd : (mule_def a b) in he=> //; have hab : a * b = y by case: he.
have hy' : (f x)%:E * k x = y by rewrite hax hbx.
have hfy : (f x)%:E * k x \is a fin_num by rewrite hy'.
by rewrite (extended_product_finite_fine hfy) hy'.
Qed.

(** Source for [zero_product_lattice_density_real]: the same
    reduction in Federer 2.5.10, p. 100, under the convention
    0 . infinity = 0 of 2.1.1, p. 51. *)
Theorem zero_product_lattice_density_real (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (L : set (X -> R)) (A : (X -> R) -> R)
    (k : X -> \bar R) :
  is_zero_product_lattice_density mu L A k -> is_real_lattice_density mu L A (fun x => fine (k x)).
Proof.
move=> [hk hrep]; split; first exact: (fine_density_measurable hm hk).
move=> f hf; have hi := hrep f hf.
have hfin := @measure_summable_finite_almost R X mu hm _ (ex_intro _ (A f) hi).
apply: (@measure_integral_almost_equal R X mu hm _ _ _ hi).
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hfin)=> x [y [hy hyf]].
exists y; split=> //; apply/real_total_integrand_graph.
have hy' : (f x)%:E * k x = y := hy.
have hfy : (f x)%:E * k x \is a fin_num by rewrite hy'.
by rewrite (extended_product_finite_fine hfy) hy'.
Qed.
