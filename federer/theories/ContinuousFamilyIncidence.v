(** Supporting the affine double-slicing argument of Federer (1969),
    2.10.16, p. 178. A continuous family of maps has a Suslin incidence set
    on every Suslin source, when source and parameter spaces are complete
    separable metric spaces. This extends the direct incidence argument in
    2.10.5, p. 172; it does not restrict the family to orthogonal
    projections. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  cardinality reals topology.
From Federer Require Import CompleteMetricUP MetricProductBackground MetricProductCompleteness
  MetricProductSeparability SuslinSetUP SuslinPreimages BorelImageMeasurability
  TopologicalProductMaps HausdorffBinaryProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [family_incidence]: supporting incidence set
    for 2.10.16, p. 178. Its point (y,p) records an
    x in A with y equal to the value of the p-th map. *)
Definition family_incidence (X Y P : Type) (e : P*X -> Y) (A : set X) : set (Y*P) :=
  [set z | exists x, A x /\ z.1=e (z.2,x)].

(** Source for [continuous_family_incidence_suslin]: supporting
    joint incidence measurability for 2.10.16, p. 178,
    by the continuous-image theorem of 2.2.10, p. 65.
    The continuous family is used as an abstract function;
    no rank or injectivity assumption is imposed. *)
Theorem continuous_family_incidence_suslin (R : realType)
    (X P : metricType R) (Y : topologicalType) (e : P*X -> Y) (A : set X) :
  is_complete_metric_space X -> is_complete_metric_space P ->
  (exists D : set X, countable D /\ dense D) ->
  (exists D : set P, countable D /\ dense D) ->
  hausdorff_space Y -> continuous e -> is_suslin_set R A ->
  is_suslin_set R (family_incidence e A).
Proof.
move=> hX hP hsX hsP hY he hA.
pose T := [the metricType R of metric_product X P].
pose F (z : T) : Y*P := (e (z.2,z.1),z.2).
have hF : continuous F.
  apply: topological_pair_continuous; last exact: second_projection_continuous.
  have hs : continuous (fun z : T => (z.2,z.1)).
    apply: topological_pair_continuous; [exact: second_projection_continuous|exact: first_projection_continuous].
  move=> z; exact (continuous_comp (hs z) (he (z.2,z.1))).
have hsrc : is_suslin_set R ((@fst X P) @^-1` A).
  exact: continuous_preimage_suslin (@first_projection_continuous X P) hA.
have himg : F @` ((@fst X P) @^-1` A)=family_incidence e A.
  apply/seteqP; split.
  - move=> [y p] [[x q] hx <-]; by exists x.
  - move=> [y p] [x [hx hy]]; exists (x,p)=> //.
    have hy' : y=e (p,x) := hy.
    change ((e (p,x),p)=(y,p)); by rewrite hy'.
rewrite -himg.
apply: (@continuous_suslin_image R T (Y*P)%type F _
  (@complete_metric_product R X P hX hP) (@separable_metric_product R X P hsX hsP) _ hF hsrc).
exact: hausdorff_binary_product hY (@metric_hausdorff R P).
Qed.
