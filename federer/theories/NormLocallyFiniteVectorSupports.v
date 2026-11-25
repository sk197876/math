(** Federer (1969), 4.1.1, p. 344: locally
    finite vector-valued smooth sums support the common-
    support sequence argument. The existing scalar
    support theorem applies to the vector norms,
    whose nonzero loci are exactly the original ones. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormLocallyFiniteFamilyUP LocallyFiniteFamilyUP
  CompactSupportFunctionUP NormLocallyFiniteFunctionSupports.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_locally_finite_vector_supports]: local
    finiteness of vector functions implies local finiteness
    of their actual closed supports, supporting Federer
    4.1.1, p. 344. The scalar support proof
    is reused through the given vector norm. *)
Theorem norm_locally_finite_vector_supports (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (J:choiceType) (U:set X) (I:set J) (f:J->X->Y):
  is_norm_locally_finite_function_family NX U I f ->
  @is_locally_finite_family_on (real_norm_metric_space hNX) J U I
    (fun j=>closure [set x:real_norm_metric_space hNX|f j x<>0]).
Proof.
move=>hF.
have hNorm:is_norm_locally_finite_function_family NX U I (fun j x=>NY (f j x)).
  move=>a ha; have [O [hOa [hOU [hOpen [F [hFI hZero]]]]]]:=hF a ha.
  exists O; split=>//; split=>//; split=>//; exists F; split=>//.
  move=>x hx j hj hn; by rewrite (hZero x hx j hj hn) (real_seminorm_zero hNY.1).
have hLocal:=@norm_locally_finite_function_supports R X NX hNX J U I (fun j x=>NY (f j x)) hNorm.
have hSupports (j:J):@real_function_support R (real_norm_metric_space hNX) (fun x=>NY (f j x))=
    closure [set x:real_norm_metric_space hNX|f j x<>0].
  congr closure; apply:funext=>x; apply:propext; split.
  - move=>hn hz; apply:hn; by rewrite hz (real_seminorm_zero hNY.1).
  - move=>hn hz; exact:hn (hNY.2 _ hz).
have hFamily:(fun j=>@real_function_support R (real_norm_metric_space hNX) (fun x=>NY (f j x)))=
    (fun j=>closure [set x:real_norm_metric_space hNX|f j x<>0]).
  apply:funext=>j; exact:hSupports.
by rewrite hFamily in hLocal.
Qed.
