(** Federer (1969), 2.2.15, pp. 70–71: supporting pair closure for the
    real-valued Baire algebra. Two applications of the smallest-class
    principle give the result: first fix a continuous first coordinate, then
    allow any Baire first coordinate. *)
From mathcomp Require Import all_boot classical_sets reals topology.
From Federer Require Import PointwiseLimit BaireFunctionUP BaireFunctions
  MetricProductBackground TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [baire_pair_functions]: supporting product
    closure for the algebra assertion in Federer 2.2.15,
    pp. 70–71. The proof follows sequential closure and
    minimality rather than presupposing a closure theorem for
    Baire ranks. Both target factors carry their given metrics. *)
Theorem baire_pair_functions (R : realType) (X : topologicalType) (Y Z : metricType R)
    (f : X -> Y) (g : X -> Z) :
  is_baire_function f -> is_baire_function g ->
  @is_baire_function R X [the metricType R of metric_product Y Z] (fun x => (f x,g x)).
Proof.
pose P := [the metricType R of metric_product Y Z].
have hcont (a : X -> Y) : continuous a -> forall b : X -> Z,
    is_baire_function b -> @is_baire_function R X P (fun x => (a x,b x)).
  move=> ha; apply: (@baire_function_induction R X Z
    [set b | @is_baire_function R X P (fun x => (a x,b x))]).
  - move=> b c hb hlim.
    apply: (@baire_function_pointwise_limit R X P
      (fun n x => (a x,b n x)) (fun x => (a x,c x)))=> //.
    exact: (@pointwise_limit_pair X Y Z (fun _ => a) b a c
      (@pointwise_limit_constant X Y a) hlim).
  - move=> b hb; apply: continuous_baire_function.
    exact: topological_pair_continuous ha hb.
have hall : forall a : X -> Y, is_baire_function a ->
    forall b : X -> Z, is_baire_function b -> @is_baire_function R X P (fun x => (a x,b x)).
  apply: (@baire_function_induction R X Y [set a | forall b : X -> Z,
    is_baire_function b -> @is_baire_function R X P (fun x => (a x,b x))]).
  - move=> a c ha hlim b hb.
    apply: (@baire_function_pointwise_limit R X P
      (fun n x => (a n x,b x)) (fun x => (c x,b x))).
    + move=> n; exact: ha n b hb.
    + exact: (@pointwise_limit_pair X Y Z a (fun _ => b) c b hlim
        (@pointwise_limit_constant X Z b)).
  - exact hcont.
move=> hf hg; exact: hall f hf g hg.
Qed.
