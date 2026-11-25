(** Federer (1969), 4.1.1, p. 345: compact test supports
    meet only finitely many partition functions. This supporting
    connection turns the already proved local finite expression
    for functions into local finiteness of their actual supports. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric NormBoundedLinearTopology CompactSupportFunctionUP
  NormLocallyFiniteFamilyUP LocallyFiniteFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_locally_finite_function_supports]: local
    finiteness of functions implies local finiteness of their
    closed supports, supporting the partition decomposition of
    Federer 4.1.1, p. 345, from 3.1.13, p. 225. *)
Theorem norm_locally_finite_function_supports (R:realType)
    (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    (J:choiceType) (U:set X) (I:set J) (v:J->X->R):
  is_norm_locally_finite_function_family NX U I v ->
  @is_locally_finite_family_on (real_norm_metric_space hNX) J U I
    (fun j=>@real_function_support R (real_norm_metric_space hNX) (v j)).
Proof.
move=>hv x hx.
have [O [hOx [hOU [hInterior [F [hFI hF]]]]]]:=hv x hx.
have hOpen:@open (real_norm_metric_space hNX) O.
  rewrite openE=>y hy.
  exact:(norm_domain_interior_neighbourhood hNX O y).1 (hInterior y hy).
exists O; split=>//; split=>//.
apply:(sub_finite_set _ (@finite_fset J F))=>j [hIj [y [hy hs]]].
case:(boolP (j \in F))=>hj; first exact hj.
have hNb:=@open_nbhs_nbhs (real_norm_metric_space hNX) y O (conj hOpen hy).
have [z [hz hOz]]:=hs O hNb.
exact:False_ind _ (hz (hF z hOz j hIj hj)).
Qed.
