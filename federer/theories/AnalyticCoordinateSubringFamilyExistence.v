(** Federer (1969), 3.4.8(1), p. 326:
    existence and uniqueness of the original family
    of coordinate germ images, using only each
    image's public opaque interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis AnalyticGermRing AnalyticPrefixGermSubring
  AnalyticCoordinateSubringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_coordinate_subring_family_exists]:
    the original finite-prefix images supply an
    actual family, as in 3.4.8(1), p. 326.
    Only unused indices receive an auxiliary extension. *)
Theorem analytic_coordinate_subring_family_exists (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o):
  exists Q:nat->set (@analytic_germ_ring R X NX hNX 0),
    is_analytic_coordinate_subring_family he omega Q.
Proof.
pose Q:=fun j=>if pselect ((j<=n)%N) is left h then
  @analytic_prefix_germ_subring R X NX hNX n e he omega j h else set0.
exists Q;constructor.
- move=>j hj;rewrite /Q;case:pselect=>[h|h].
  + by rewrite (bool_irrelevance h hj).
  + exfalso;exact:h hj.
- move=>j hj;rewrite /Q;case:pselect=>[h|h]=>//.
  have hFalse:=leq_ltn_trans h hj;by rewrite ltnn in hFalse.
Qed.

(** Source for [analytic_coordinate_subring_family_unique]:
    the exact independent image laws determine the
    family uniquely, supporting 3.4.8(1), p. 326. *)
Lemma analytic_coordinate_subring_family_unique (R:realType) (X:lmodType R)
  (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
  (omega:'I_n->Hom X R^o) (Q P:nat->set (@analytic_germ_ring R X NX hNX 0)):
  is_analytic_coordinate_subring_family he omega Q ->
  is_analytic_coordinate_subring_family he omega P ->Q = P.
Proof.
move=>hQ hP;apply:funext=>j;case:(leqP j n)=>[hj|hj].
- by rewrite (analytic_coordinate_subring_family_member hQ hj)
    (analytic_coordinate_subring_family_member hP hj).
- by rewrite (analytic_coordinate_subring_family_outside hQ hj)
    (analytic_coordinate_subring_family_outside hP hj).
Qed.
