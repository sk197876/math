(** Federer (1969), 4.1.1, p. 344:
    the support of a functional
    is relatively closed in its
    original open domain. This supporting
    consequence of the union-of-annihilation-sets
    definition is reused for proper
    restrictions in 4.1.7, p. 359. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric FunctionalSupportUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [functional_support_relative_closed]:
    the original support is U
    intersected with an ambient closed
    set, supporting Federer 4.1.1,
    p. 344, and the proper
    support restrictions of 4.1.7, p. 359. *)
Theorem functional_support_relative_closed (R:realType) (X Y:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U:set X) (E:lmodType R)
    (ev:E->X->Y) (T:Hom E R^o):
  exists C:set X,@closed (real_norm_metric_space hNX) C /\
    @smooth_functional_support R X Y NX hNX U E ev T=U `&` C.
Proof.
pose W:=\bigcup_(O in (@smooth_functional_annihilation_open R X Y NX hNX U E ev T)) O.
have hW:@open (real_norm_metric_space hNX) W.
  apply:bigcup_open=>O hO;exact:hO.1.
exists (~` W);split;first exact:open_closedC hW.
apply:funext=>x;apply:propext;split.
- move=>[hx hNo];split=>//;move=>[O hO hxO];apply:hNo;by exists O.
- move=>[hx hNo];split=>//;move=>[O [hO hxO]];apply:hNo;by exists O.
Qed.
