(** Federer (1969), 3.4.12, p. 339:
    an original complex m-dimensional holomorphic submanifold
    is an actual real 2m-dimensional analytic submanifold.
    Reuse the original coordinate maps and paired plane bases. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP GrassmannSubspaces
  ComplexGrassmannReal HolomorphicDiffeomorphismUP HolomorphicDiffeomorphismReal
  HolomorphicSubmanifoldUP NormAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [holomorphic_submanifold_real]: the original
    real dimension is twice the complex dimension,
    3.4.12, p. 339, first paragraph.
    All actual plane-section and inverse equations remain;
    the assertion includes m=0 and the empty set. *)
Theorem holomorphic_submanifold_real (R:realType)
    (X:lmodType (ComplexScalars.C R)) (NX:X->R)
    (hNX:is_real_norm (fun x:restricted_space (ComplexScalars.embed R) X=>NX x))
    m (S:set X):
  is_holomorphic_submanifold hNX m S ->
  is_norm_analytic_submanifold hNX (m+m)%N S.
Proof.
move=>h b hb;have [T [C [s [t [Z [hT [hD hImage]]]]]]]:=h b hb.
have [W hW]:=complex_grassmann_real Z.
exists T,C,s,t,W;split;first exact:hT.
split;first exact:holomorphic_diffeomorphism_real hD.
split;first exact:(holomorphic_diffeomorphism_forward hD).1.
split;first exact:(holomorphic_diffeomorphism_inverse hD).1.
rewrite hImage;apply/seteqP;split=>x [hx hC];split=>//.
- exact:(hW x).2 hx.
- exact:(hW x).1 hx.
Qed.
