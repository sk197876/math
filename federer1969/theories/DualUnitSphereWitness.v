(** Federer (1969), 2.5.14, p. 108: a fixed unit dual functional supplies a
    normalized representative on a locally exceptional set. This supporting
    choice uses the norming-functional corollary of 2.4.12, p. 86, also used
    in 2.5.12, p. 104. The nonzero-space hypothesis is explicit; zero
    dimension is treated separately. These support the Hahn–Banach
    ingredient, not this representative convention. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP VectorDaniellHypotheses VectorDaniellDualExtension
  VectorDaniellPairingMeasurability DualNormEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [nontrivial_dual_unit_sphere_inhabited]: supporting
    unit-dual representative for Federer 2.5.14, p. 108,
    from the norming-functional corollary in 2.4.12, p. 86.
    This paraphrases the corollary, specialized to a normalized
    nonzero vector and a finite norm. *)
Lemma nontrivial_dual_unit_sphere_inhabited (R : realType) (E : lmodType R)
    (N : E -> R) (hN : is_real_norm N) :
  (exists y : E, y<>0) -> exists a : weak_dual_space hN, dual_norm N (val a)= 1.
Proof.
move=> [y hy].
have hNy : 0<N y by rewrite (real_norm_positive hN.1 hN.2); apply/eqP.
pose u := (N y)^-1*:y.
have hu : N u= 1 by rewrite (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 // mulVf // gt_eqF.
have [mu hmu] := norming_family_exists hN.
have [ha he] := hmu u.
have hbound := @dual_norm_evaluation_bound R E N hN (mu u) u ha.1.
rewrite he hu normr1 mulr1 in hbound.
pose a : weak_dual_space hN := @exist (weak_function_space E)
  (fun alpha => alpha \in (dual_space hN : set (weak_function_space E))) (mu u) (mem_set ha.1).
exists a; apply/eqP; rewrite eq_le ha.2 hbound; by [].
Qed.
