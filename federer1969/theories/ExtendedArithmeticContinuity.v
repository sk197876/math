(** Federer (1969), 2.3.2, p. 74: continuity of scalar arithmetic on its
    defined domain. The narrow ereal_normedtype and normed_module imports
    supply scalar-topology background, as for real arithmetic in
    BaireRealAlgebra; no external measurability theorem is used. The
    explicit adapter preserves the public order topology. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology ereal ereal_normedtype normed_module.
From Federer Require Import ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(** Source for [extended_real_native_neighborhoods]: scalar-topology
    adapter supporting Federer 2.3.2, p. 74. Both structures
    have exactly the order-interval neighborhood basis. *)
Lemma extended_real_native_neighborhoods (R : realType) (x : \bar R) :
  @nbhs _ (extended_real_line R) x = @nbhs _ [the topologicalType of (\bar R : Type)] x.
Proof. by rewrite !itv_nbhsE. Qed.

(** Source for [extended_add_continuous_at_defined]: scalar-topology
    background for addition in Federer 2.3.2, p. 74 Opposite infinities are
    excluded exactly by the operation domain. *)
Lemma extended_add_continuous_at_defined (R : realType) (p : extended_real_line R * extended_real_line R) :
  adde_def p.1 p.2 -> {for p, continuous (fun q : extended_real_line R * extended_real_line R => ((q.1 + q.2)%E : extended_real_line R))}.
Proof.
move=> hp; rewrite /continuous_at.
change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => (q.1 + q.2)%E) (nbhs p)) (@nbhs _ (extended_real_line R) (p.1 + p.2)%E)).
rewrite extended_real_native_neighborhoods.
apply (@cvgeD _ (nbhs p) _ R (fun q : extended_real_line R * extended_real_line R => q.1) (fun q : extended_real_line R * extended_real_line R => q.2) p.1 p.2 hp).
- change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => q.1) (nbhs p)) (@nbhs _ [the topologicalType of (\bar R : Type)] p.1)).
  rewrite -extended_real_native_neighborhoods; exact: cvg_fst.
- change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => q.2) (nbhs p)) (@nbhs _ [the topologicalType of (\bar R : Type)] p.2)).
  rewrite -extended_real_native_neighborhoods; exact: cvg_snd.
Qed.

(** Source for [extended_multiply_continuous_at_defined]: scalar-topology
    background for multiplication in Federer 2.3.2, p. 74 Zero times either
    infinity is excluded, with no total-product convention. *)
Lemma extended_multiply_continuous_at_defined (R : realType) (p : extended_real_line R * extended_real_line R) :
  mule_def p.1 p.2 -> {for p, continuous (fun q : extended_real_line R * extended_real_line R => ((q.1 * q.2)%E : extended_real_line R))}.
Proof.
move=> hp; rewrite /continuous_at.
change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => (q.1 * q.2)%E) (nbhs p)) (@nbhs _ (extended_real_line R) (p.1 * p.2)%E)).
rewrite extended_real_native_neighborhoods.
apply (@cvgeM _ (nbhs p) _ R (fun q : extended_real_line R * extended_real_line R => q.1) (fun q : extended_real_line R * extended_real_line R => q.2) p.1 p.2 hp).
- change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => q.1) (nbhs p)) (@nbhs _ [the topologicalType of (\bar R : Type)] p.1)).
  rewrite -extended_real_native_neighborhoods; exact: cvg_fst.
- change (@cvg_to _ (fmap (fun q : extended_real_line R * extended_real_line R => q.2) (nbhs p)) (@nbhs _ [the topologicalType of (\bar R : Type)] p.2)).
  rewrite -extended_real_native_neighborhoods; exact: cvg_snd.
Qed.
