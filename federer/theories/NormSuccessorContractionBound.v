(** Federer (1969), 3.1.24, pp. 238–239:
    contracting a higher differential with its final argument,
    in the successor-arity notation of 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra reals ring.
From Federer Require Import Hom RealNormUP ContinuousMultilinearUP ContinuousMultilinearSuccessorContraction
  NormBoundedBilinearUP MultilinearArguments MultilinearArgumentTransport MultilinearSuccessorArguments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [continuous_multilinear_successor_contraction_unit_bound]:
    the contraction used in termwise differentiation of the
    series in Federer 3.1.24, pp. 238–239. The
    operation is bilinear, satisfies the actual successor
    evaluation law from 3.1.11, p. 219, and
    has norm at most the product of the form norm
    and the vector norm. Its existence and bound are proved
    solely from the abstract multilinear-space laws. *)
Theorem continuous_multilinear_successor_contraction_unit_bound (R:realType) k
    (X Y:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX)
    (Z:nat->lmodType R) (ev:forall i,{ffun 'I_i->X}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space NX NY (@ev i) (@ZN i)) :
  exists C:Z k.+1->X->Z k,
    norm_bounded_bilinear (@ZN k.+1) NX (@ZN k) C /\
    (forall z v,@ZN k (C z v)<=@ZN k.+1 z*NX v) /\
    forall z v u,@ev k u (C z v)= @ev k.+1 (multilinear_successor_arguments u v) z.
Proof.
have [C [hC he]]:=@continuous_multilinear_successor_contraction_exists R k X Y (Z k) (Z k.+1)
  NX NY hNX (@ev k) (@ZN k) (@ev k.+1) (@ZN k.+1) (hZ k) (hZ k.+1).
have hsucc z v u:@ev k u (C z v)= @ev k.+1 (multilinear_successor_arguments u v) z.
  exact (he z v u).
exists C; split; first exact hC.
split; last exact hsucc.
move=>z v.
have hz:0<=@ZN k.+1 z:=multilinear_operator_nonnegative (continuous_multilinear_norm_laws (hZ k.+1) z).
have hv:0<=NX v:=real_seminorm_nonnegative hNX.1 v.
apply: (multilinear_operator_least (continuous_multilinear_norm_laws (hZ k) (C z v))
  (mulr_ge0 hz hv))=>u.
rewrite hsucc.
have hh:=multilinear_operator_bound (continuous_multilinear_norm_laws (hZ k.+1) z)
  (multilinear_successor_arguments u v).
have hp:(\prod_(i<k.+1) NX (multilinear_successor_arguments u v i))=
    (\prod_(i<k) NX (u i))*NX v.
  by rewrite /multilinear_successor_arguments multilinear_arguments_cast_product
    multilinear_arguments_product big_ord1 ffunE.
rewrite hp in hh.
have heq:@ZN k.+1 z*((\prod_(i<k) NX (u i))*NX v)=
    (@ZN k.+1 z*NX v)*(\prod_(i<k) NX (u i)) by ring.
by rewrite heq in hh.
Qed.
