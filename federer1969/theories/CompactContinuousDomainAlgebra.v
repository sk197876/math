(** Federer (1969), 4.1.5, p. 350: the
    decomposition w=h w+(w-h w) stays inside the
    original compact continuous vector space D. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP VectorDaniellHypotheses CompactContinuousDomainFields.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_continuous_domain_subtract]:
    subtraction in the original D of Federer 4.1.5,
    p. 350, derived from its already proved vector
    space laws. *)
Theorem compact_continuous_domain_subtract (R:realType) (X:topologicalType)
    (U:set X) (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (w v:X->Y):
  compact_continuous_domain_fields U hNY w ->
  compact_continuous_domain_fields U hNY v ->
  compact_continuous_domain_fields U hNY (fun x=>w x-v x).
Proof.
move=>hw hv.
pose Q:=@compact_continuous_domain_fields R X U Y NY hNY.
have hQ:=@compact_continuous_domain_vector_space R X U Y NY hNY.
have hNeg:=@vector_function_space_scale R X Y Q hQ (-1) v hv.
have hSum:=@vector_function_space_add R X Y Q hQ w (fun x=>(-1)*:v x) hw hNeg.
have hEq:(fun x=>w x+(-1)*:v x)=(fun x=>w x-v x).
  apply:funext=>x; by rewrite scaleN1r.
by rewrite hEq in hSum.
Qed.
