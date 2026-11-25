(** Federer (1969), 3.2.26(3), p. 262: a
    uniform additive error contributes at most that error
    to a probability L^t norm. This is the two-term
    Minkowski estimate of 2.4.12, pp. 86–87, and
    retains infinite inputs and the infinity exponent. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureUP
  MeasurableFunctionUP MeasurableTotalBasic ProbabilityExtendedNormCover
  NonnegativeExtendedExponentNorm NonnegativeExtendedProbabilityConstant
  NonnegativeSum NonnegativeSumBoolean.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [probability_extended_norm_uniform_error]: the
    triangle estimate used after the first integral inequality
    of 3.2.26(3), p. 262. Norms use the actual
    nonnegative extended-input formulas. No finiteness of
    either function or either norm is assumed. *)
Theorem probability_extended_norm_uniform_error (R:realType) (X:choiceType)
    (mu:set X->\bar R) (t: \bar R) (f g:X->extended_real_line R) (e:R):
  is_measure mu ->mu setT= 1 ->1<=t ->(0<=e)%R ->
  (forall x,0<=f x) ->(forall x,0<=g x) ->
  is_measure_measurable_function mu (partial_function_total f) ->
  is_measure_measurable_function mu (partial_function_total g) ->
  (forall x,f x<=g x+e%:E) ->
  nonnegative_extended_exponent_norm mu f t<=
    nonnegative_extended_exponent_norm mu g t+e%:E.
Proof.
move=>hMu hProbability ht he hf0 hg0 hf hg hError.
pose F (b:bool):X->extended_real_line R:=if b then g else fun _=>e%:E.
have hF0 b x:0<=F b x by case:b=>//=; rewrite lee_fin.
have hF b:is_measure_measurable_function mu (partial_function_total (F b)).
  case:b; first exact hg.
  exact:(@measurable_total_constant R X (extended_real_line R) mu hMu e%:E).
have hCover x:f x<=nonnegative_sum setT (fun b:bool=>F b x).
  rewrite nonnegative_sum_bool; last by move=>b; exact:hF0 b x.
  exact:hError x.
have hBound:=@probability_nonnegative_extended_norm_cover R X bool mu hMu t setT f F
  hProbability (countableP setT) ht hf0 hF0 hf (fun b _=>hF b) hCover.
rewrite nonnegative_sum_bool in hBound; last first.
- move=>b; exact:(@nonnegative_extended_exponent_norm_ge0 R X mu (F b) t hMu
    (hF0 b) ht (hF b)).
change (is_true (nonnegative_extended_exponent_norm mu f t<=
  nonnegative_extended_exponent_norm mu g t+
    nonnegative_extended_exponent_norm mu (fun _:X=>e%:E) t)) in hBound.
by rewrite (@probability_nonnegative_extended_constant_norm R X mu hMu e%:E t
  hProbability (lee_tofin he) ht) in hBound.
Qed.
