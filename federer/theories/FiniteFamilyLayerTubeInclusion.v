(** Federer (1969), 3.2.39, p. 276: every nearby
    layer centre witnesses at least that many nearby family members. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import FiniteFamilyMultiplicity FiniteFamilyLayersUP MetricOpenThickening.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_family_layer_tube_count_bound]: the
    pointwise characteristic inequality for S_(j,r) and t_(C,r)
    in Federer 3.2.39, p. 276, before integration. Each
    actual centre lies in at least j+1 original members, all
    of whose actual open tubes therefore contain the tested
    point. No source or tube measurability premise is needed. *)
Lemma finite_family_layer_tube_count_bound (R:realType) (X:metricType R) (I:finType)
    (K:I->set X) (S:'I_(#|I|)->set X) (r:R):
  is_finite_family_layers K S ->forall j z,metric_open_thickening (S j) r z ->
    (j<finite_family_hit_count (fun i=>metric_open_thickening (K i) r) z)%N.
Proof.
move=>hS j z [y hy hDistance].
have hMono:(finite_family_hit_count K y<=
    finite_family_hit_count (fun i=>metric_open_thickening (K i) r) z)%N.
  apply:finite_family_hit_count_transport=>i hi; by exists y.
exact:leq_trans ((hS j y).1 hy) hMono.
Qed.
