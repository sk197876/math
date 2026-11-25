(** Federer (1969), 4.1.14, p. 371: continuity of
    the original scalar weight |g-f|sigma^m and its smooth
    approximation weights. The norm and product continuity
    laws were proved before the measure theory. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import RealNormUP NormMetric RealMetricBackground
  MetricProductBackground TopologicalProductMaps NormMetricContinuity
  NormMetricSubtractContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory
  numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.

(** Source for [current_affine_weight_continuous]: the original
    affine weight in Federer 4.1.14, p. 371, is
    continuous wherever its two endpoints and sigma are
    continuous. Natural degree zero requires no positive
    lower bound for the majorant. *)
Theorem current_affine_weight_continuous (R : realType)
    (X : topologicalType) (Y : lmodType R) (NY : Y -> R)
    (hNY : is_real_norm NY)
    (f g : X -> real_norm_metric_space hNY) (sigma : X -> R^o) m :
  continuous f -> continuous g -> continuous sigma ->
  continuous (fun x:X => (NY (g x-f x)*(sigma x)^+m:R^o)).
Proof.
move=> hF hG hSigma.
pose YT := real_norm_metric_space hNY.
pose P := metric_product YT YT.
pose pair (x:X) : P := (g x,f x).
have hPair : continuous pair := topological_pair_continuous hG hF.
have hDifference : continuous (fun x:X => (g x-f x:YT)).
  move=> x.
  exact: (@continuous_comp X P YT pair (fun p:P => p.1-p.2) x
    (hPair x) (@real_norm_metric_subtract_continuous R Y NY hNY (pair x))).
have hNorm : continuous (fun x:X => (NY (g x-f x):R^o)).
  move=> x.
  exact: (@continuous_comp X YT (real_line_metric R)
    (fun x:X => g x-f x) (fun y:YT => NY y) x (hDifference x)
    (@real_norm_metric_norm_continuous R Y NY hNY (g x-f x))).
have hPower : forall k:nat, continuous (fun x:X => ((sigma x)^+k:R^o)).
  elim=> [|k ih] x.
  - exact: cvg_cst.
  - have hExp : (fun y:X => (sigma y)^+k.+1)=
      (fun y:X => sigma y*(sigma y)^+k).
      by apply: funext=> y; rewrite exprS.
    rewrite hExp.
    exact: (@cvgM R X (nbhs x) (@nbhs_filter X x)
      sigma (fun y:X => (sigma y)^+k) (sigma x) ((sigma x)^+k)
      (hSigma x) (ih x)).
move=> x.
exact: (@cvgM R X (nbhs x) (@nbhs_filter X x)
  (fun y:X => NY (g y-f y)) (fun y:X => (sigma y)^+m)
  (NY (g x-f x)) ((sigma x)^+m) (hNorm x) (hPower m x)).
Qed.
