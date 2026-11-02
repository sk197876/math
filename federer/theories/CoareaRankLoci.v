(** Federer (1969), 3.2.11, p. 249: split
    actual differentiability points into full target rank and
    critical target rank. Both loci are Borel for continuous
    maps, using the exact partial Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional NormClassOneUP
  EuclideanLinearJacobian EuclideanTargetJacobianBorel CoareaLinearDuality CoordinateInverseCoverUP
  Jacobian PartialFunctionUP DifferentialRankLociBorel RealMetricBackground
  TopologicalBorel BorelFamilyBasic InnerOwnNormTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_target_differential_locus]: the
    set {x:J_n f(x)=0} in Federer 3.2.11,
    p. 249, restricted to the actual differential domain. *)
Definition critical_target_differential_locus (R:realType) m n (f:R_n R m->R_n R n):=
  [set x|exists D:Hom (R_n R m) (R_n R n),
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x D /\
    euclidean_linear_jacobian n D=0].

(** Source for [critical_target_differential_jacobian]: the
    critical-set description in Federer 3.2.11, p. 249
    is precisely the zero graph of the actual J_n f. *)
Lemma critical_target_differential_jacobian (R:realType) m n (f:R_n R m->R_n R n) x:
  critical_target_differential_locus f x <->
    partial_function_graph (euclidean_jacobian n setT f) x 0.
Proof. exact:iff_sym (euclidean_jacobian_graph n setT f x 0). Qed.

(** Source for [ordinary_target_rank_split]: the two cases
    in Federer 3.2.11, p. 249 exhaust exactly
    the actual differential domain, including target degree zero. *)
Lemma ordinary_target_rank_split (R:realType) m n (f:R_n R m->R_n R n) x:
  norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f x <->
    surjective_differential_locus f x \/ critical_target_differential_locus f x.
Proof.
split; last by move=>[[D [hD _]]|[D [hD _]]]; exists D.
move=>[D hD]; case:(eqVneq (euclidean_linear_jacobian n D) 0)=>hz.
- right; by exists D.
- left; exists D; split=> //.
  apply:(euclidean_target_jacobian_positive_iff_surjective D).1.
  by rewrite lt_def hz (euclidean_linear_jacobian_nonnegative n D).
Qed.

(** Source for [coarea_rank_loci_disjoint]: full target
    rank and critical target rank are mutually exclusive
    in Federer 3.2.11, p. 249, by actual
    differential uniqueness and positivity of the Jacobian. *)
Lemma coarea_rank_loci_disjoint (R:realType) m n (f:R_n R m->R_n R n) x:
  surjective_differential_locus f x ->~critical_target_differential_locus f x.
Proof.
move=>[D [hD hRank]] [E [hE hZero]].
have hEq:D=E:=norm_differential_unique
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hD hE.
have hp:0<euclidean_linear_jacobian n D:=(euclidean_target_jacobian_positive_iff_surjective D).2 hRank.
by rewrite hEq hZero ltxx in hp.
Qed.

(** Source for [critical_target_differential_locus_borel]:
    the Borel critical source reduction in Federer
    3.2.11, p. 249. Continuity suffices. *)
Lemma critical_target_differential_locus_borel (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (critical_target_differential_locus f).
Proof.
move=>hf.
have hZero:borel_set [set (0:real_line_metric R)].
  apply:closed_borel_set; apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
have hPre:=euclidean_target_jacobian_borel_preimage hf hZero.
have hEq:partial_function_preimage (euclidean_jacobian n setT f) [set (0:real_line_metric R)]=
    critical_target_differential_locus f.
  apply/seteqP; split=>x.
  - move=>[j [hj hz]]; change (j=0) in hz; subst j.
    exact ((critical_target_differential_jacobian f x).2 hj).
  - move=>hx; exists 0; split; first exact ((critical_target_differential_jacobian f x).1 hx).
    by [].
rewrite hEq in hPre.
exact ((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hPre).
Qed.

(** Source for [surjective_target_differential_locus_borel]:
    the Borel full-rank source reduction in Federer
    3.2.11, p. 249, obtained by removing the
    critical locus from the actual Borel differential domain. *)
Lemma surjective_target_differential_locus_borel (R:realType) m n (f:R_n R m->R_n R n):
  norm_class_zero (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)]
    (surjective_differential_locus f).
Proof.
move=>hf.
have hEq:surjective_differential_locus f=
    [set x|norm_differentiable_at (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT f x] `\` critical_target_differential_locus f.
  apply/seteqP; split=>x.
  - move=>hx; split; first exact ((ordinary_target_rank_split f x).2 (or_introl hx)).
    exact (coarea_rank_loci_disjoint hx).
  - move=>[hx hn]; have [h|h]:=(ordinary_target_rank_split f x).1 hx; first exact h.
    by exfalso; exact:hn h.
rewrite hEq; exact (borel_set_difference (ordinary_differential_locus_borel hf)
  (critical_target_differential_locus_borel hf)).
Qed.
