(** Federer (1969), 4.1.5, pp. 349–350: the
    continuous extension is independent of the chosen
    compact uniform approximation. Subtraction reduces
    the comparison to the proved uniform zero estimate. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP FunctionLatticeUP CompactSupportFunctionUP
  CompactUniformApproximationUP CompactUniformApproximationAlgebra DistributionVariationUP
  DistributionCompactUniformLimits PositiveNormLimitUP PositiveRealLinearLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [distribution_compact_uniform_limit_unique]:
    uniqueness of the convolution extension T(w) in
    Federer 4.1.5, p. 349. Every actual common-support
    uniform approximation has the same scalar limit,
    so no choice of smoothing kernel changes T. *)
Theorem distribution_compact_uniform_limit_unique (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (E:lmodType R) (value:Hom E (GRing.Lmodule.clone R (X->Y) _)) (S:Hom E R^o)
    (hh:hausdorff_space X) (hl:locally_compact (@setT X)) (hU:open U)
    (hFinite:forall f:X->R,
      @positive_function_lattice R X (@compactly_supported_continuous_functions R X) f ->
      @real_function_support R X f `<=` U ->
      exists b:R,is_distribution_variation_value NY value S f b%:E)
    (w:X->Y) (P Q:R->E) t u:
  is_compact_uniform_test_approximation U NY value w P ->
  is_compact_uniform_test_approximation U NY value w Q ->
  positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (P e)) t ->
  positive_norm_limit (fun a:R^o=>`|a|) (fun e=>S (Q e)) u ->t=u.
Proof.
move=>hP hQ hPLimit hQLimit.
have hNeg:=@compact_uniform_test_approximation_scale R X U Y NY hNY E value w Q (-1) hQ.
have hDifference:=@compact_uniform_test_approximation_add R X U Y NY hNY E value
  w (fun x=>(-1)*:w x) P (fun e=>(-1)*:Q e) hP hNeg.
have hZeroFunction:(fun x=>w x+(-1)*:w x)=(fun _:X=>(0:Y)).
  apply:funext=>x; by rewrite scaleN1r addrN.
rewrite hZeroFunction in hDifference.
have hZero:=@distribution_compact_uniform_zero_limit R X U hh hl hU Y NY hNY E value S hFinite
  (fun e=>P e+(-1)*:Q e) hDifference.
have hLinear:=@positive_real_limit_add R (fun e=>S (P e)) (fun e=>(-1)*S (Q e)) t ((-1)*u)
  hPLimit (@positive_real_limit_scale R (fun e=>S (Q e)) u (-1) hQLimit).
have hEvaluation:(fun e=>S (P e+(-1)*:Q e))=(fun e=>S (P e)+(-1)*S (Q e)).
  apply:funext=>e; by rewrite linearD linearZ.
rewrite hEvaluation in hZero.
have hEq:=@positive_norm_limit_unique R R^o (fun a:R^o=>`|a|) (@scalar_absolute_value_norm R)
  (fun e=>S (P e)+(-1)*S (Q e)) 0 (t+(-1)*u) hZero hLinear.
lra.
Qed.
