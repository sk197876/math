(** Federer (1969), 4.1.5, p. 350:
    differences of compact continuous fields remain
    in the original extension domain. This adapter
    uses its already proved vector-space laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import RealNormUP VectorDaniellHypotheses CompactContinuousVectorFields CompactContinuousVectorSpace.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [compact_continuous_vector_subtract]:
    the compact continuous norm errors used for
    actual test density in Federer 4.1.5,
    p. 350. *)
Theorem compact_continuous_vector_subtract (R:realType) (X:topologicalType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (w v:X->Y):
  compact_continuous_vector_fields hNY w ->
  compact_continuous_vector_fields hNY v ->
  compact_continuous_vector_fields hNY (fun x=>w x-v x).
Proof.
move=>hw hv.
pose Q:=@compact_continuous_vector_fields R X Y NY hNY.
have hQ:=@compact_continuous_vector_space R X Y NY hNY.
have hNeg:=@vector_function_space_scale R X Y Q hQ (-1) v hv.
have hSum:=@vector_function_space_add R X Y Q hQ w (fun x=>(-1)*:v x) hw hNeg.
have hEq:(fun x=>w x+(-1)*:v x)=(fun x=>w x-v x).
  apply:funext=>x; by rewrite scaleN1r.
by rewrite hEq in hSum.
Qed.
