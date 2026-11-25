(** Federer (1969), 4.1.1, p. 344: opaque
    auxiliary compact neighbourhood exhaustion. Only
    its independently stated increasing and neighbourhood
    cofinal laws are exposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP LinearBasis SmoothCompactSet
  SmoothCompactExhaustionUP SmoothCompactExhaustionExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothCompactExhaustionSignature.
(** Source for [value]: auxiliary compact bounds for
    the common-support argument in Federer 4.1.1,
    p. 344. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X),is_basis b ->forall U:set X,
      (forall x,U x ->norm_domain_interior NX U x) ->nat->smooth_compact_set hNX U.
(** Source for [laws]: independent compact exhaustion
    laws supporting Federer 4.1.1, p. 344. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X) (hb:is_basis b) (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x),
    is_smooth_compact_exhaustion (@value R X NX hNX n b hb U hU).
End SmoothCompactExhaustionSignature.
Module SmoothCompactExhaustion:SmoothCompactExhaustionSignature.
(** Source for [value]: choose the already proved
    compact exhaustion witness, supporting Federer
    4.1.1, p. 344. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X) (hb:is_basis b) (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x):
    nat->smooth_compact_set hNX U:=projT1 (cid (@smooth_compact_exhaustion_exists R X NX hNX n b hb U hU)).
(** Source for [laws]: the hidden witness satisfies
    the original independent compact neighbourhood laws,
    supporting Federer 4.1.1, p. 344. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
    n (b:'I_n->X) (hb:is_basis b) (U:set X) (hU:forall x,U x ->norm_domain_interior NX U x):
    is_smooth_compact_exhaustion (@value R X NX hNX n b hb U hU).
Proof. exact:(projT2 (cid (@smooth_compact_exhaustion_exists R X NX hNX n b hb U hU))). Qed.
End SmoothCompactExhaustion.
