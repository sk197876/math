(** Federer (1969), 2.4.16, pp. 89–90: identifying the exact partial-graph
    sign convention with the printed pointwise condition for total
    functions. Source context: MeasureDualTestUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  ScalarSignTest MeasureDualTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [total_sign_matching_iff]: the total-domain form
    of sign(u)=sign(f) in Federer 2.4.16, pp. 89–90. *)
Lemma total_sign_matching_iff (R : realType) (X : Type)
    (f u : X -> real_norm_metric_space (scalar_absolute_value_norm R)) :
  is_sign_matching_test (partial_function_total f) (partial_function_total u) <->
    forall x, Num.sg (u x)=Num.sg (f x).
Proof.
split.
- move=> hs x.
  have hf : partial_function_graph (partial_scalar_sign (partial_function_total f)) x (Num.sg (f x)).
    exists (f x); by split.
  have [y [<- hy]] := (hs x _).1 hf; exact hy.
- move=> hs x z; split.
  + move=> [y [<- hy]]; exists (u x); split=> //; by rewrite hs.
  + move=> [y [<- hy]]; exists (f x); split=> //; by rewrite hs in hy.
Qed.
