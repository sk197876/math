(** Federer (1969), 3.2.33, p. 270: the actual
    analytic differential field in the exterior rank tests. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormDifferentialUP NormHigherDifferentialUP NormHigherDifferentialFirst
  ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearOne ContinuousMultilinearSealed
  ContinuousOperatorUP NormOperatorNormUP NormAnalyticUP NormAnalyticLinear NormAnalyticOperations
  NormAnalyticFirstJet EuclideanHomOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_analytic_differential_field_exists]:
    the analytic Df used in h_i in Federer 3.2.33,
    p. 270. The proved analytic first jet is identified
    isometrically with the actual bounded linear operator.
    Composition with that bounded linear identification proves
    analyticity in the original Hom operator norm. Existence,
    all actual differential laws and analyticity are proved
    together, without assuming a selected derivative field. *)
Theorem euclidean_analytic_differential_field_exists (R:realType) m n
    (A:set (R_n R m)) (f:R_n R m->R_n R n):
  @norm_analytic R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f ->
  exists D:R_n R m->Hom (R_n R m) (R_n R n),
    (forall x,A x ->has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) A f x (D x)) /\
    @norm_analytic R (R_n R m) (Hom (R_n R m) (R_n R n))
      (inner_norm (@euclidean_inner_productP R m)) (@euclidean_operator_norm R m n)
      (inner_norm_real_norm (@euclidean_inner_productP R m)) (@euclidean_operator_norm_is_norm R m n) A D.
Proof.
move=>hf.
pose X:=R_n R m; pose Y:=R_n R n.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ev i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
have hZ i:is_continuous_multilinear_space NX NY (ev i) (ZN i).
  exact:ContinuousMultilinear.laws.
pose hN1:=continuous_multilinear_norm_is_norm hNY (@ContinuousMultilinear.laws R 1%N X Y NX NY hNX hNY).
pose J:=@continuous_multilinear_one_evaluation R X Y (Z 1%N) NX NY (ev 1%N) (ZN 1%N) (hZ 1%N).
have hJBound:norm_bounded_linear (ZN 1%N) (@euclidean_operator_norm R m n) J.
  exists 1; split; first exact:ler01.
  move=>z; rewrite mul1r.
  have hOne:=@continuous_multilinear_one_norm_laws R X Y (Z 1%N) NX NY
    (ev 1%N) (ZN 1%N) (hZ 1%N) z.
  have hOp:=continuous_operator_norm_laws (@euclidean_hom_operator_space R m n) (J z).
  have hEqual:=norm_operator_unique hOp hOne.
  by rewrite hEqual.
have hFull z (_:True):norm_domain_interior (ZN 1%N) (fun _=>True) z.
  exists 1; split; first exact:ltr01; by move=>v hv.
have hJAnalytic:=@norm_bounded_linear_analytic R (Z 1%N) (Hom X Y) (ZN 1%N)
  (@euclidean_operator_norm R m n) hN1 (@euclidean_operator_norm_is_norm R m n)
  (fun _=>True) hFull J hJBound.
have [G [hG hAnalytic]]:=@norm_analytic_first_jet_exists R X Y NX NY hNX hNY A f hf.
exists (fun x=>J (G x)); split.
- move=>x hx.
  exact:((@norm_higher_differential_first R X Y NX NY hNX hNY Z ev ZN hZ A f x (G x)).1 (hG x hx)).
- exact:(@norm_analytic_compose_on R X (Z 1%N) (Hom X Y) NX (ZN 1%N)
    (@euclidean_operator_norm R m n) hNX hN1 (@euclidean_operator_norm_is_norm R m n)
    A (fun _=>True) G J (fun x hx=>Logic.I) hAnalytic hJAnalytic).
Qed.
