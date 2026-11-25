(** Federer (1969), 4.1.1, pp. 344–345: opaque smooth
    compact cutoff, specified by smoothness, support and an
    exact neighbourhood plateau. Its finite partition witness
    is private to the existence theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP LinearBasis SmoothCompactSet
  SmoothCompactCutoffUP SmoothCompactCutoffExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type SmoothCompactCutoffSignature.
(** Source for [value]: a smooth compactly supported cutoff
    equal to one near K, supporting Federer 4.1.1, pp. 344–345. *)
Parameter value:forall (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X),is_basis b ->
    forall (U:set X) (K:smooth_compact_set hNX U),
      (forall x,U x ->norm_domain_interior NX U x)->X->R.
(** Source for [laws]: independent support, smoothness and
    neighbourhood-plateau laws for the cutoff, supporting
    Federer 4.1.1, pp. 344–345. *)
Parameter laws:forall (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (K:smooth_compact_set hNX U)
    (hU:forall x,U x ->norm_domain_interior NX U x),
    is_smooth_compact_cutoff hNX U (smooth_compact_carrier K)
      (@value R X NX hNX n b hb U K hU).
End SmoothCompactCutoffSignature.
Module SmoothCompactCutoff:SmoothCompactCutoffSignature.
(** Source for [value]: select the already proved smooth
    cutoff witness, supporting Federer 4.1.1, pp. 344–345. *)
Definition value (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (K:smooth_compact_set hNX U)
    (hU:forall x,U x ->norm_domain_interior NX U x):X->R:=
  projT1 (cid (smooth_compact_cutoff_exists hb K hU)).
(** Source for [laws]: the hidden witness satisfies the
    independently stated cutoff properties, supporting Federer
    4.1.1, pp. 344–345. *)
Lemma laws (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (b:'I_n->X) (hb:is_basis b)
    (U:set X) (K:smooth_compact_set hNX U)
    (hU:forall x,U x ->norm_domain_interior NX U x):
    is_smooth_compact_cutoff hNX U (smooth_compact_carrier K)
      (@value R X NX hNX n b hb U K hU).
Proof. exact:(projT2 (cid (smooth_compact_cutoff_exists hb K hU))). Qed.
End SmoothCompactCutoff.
