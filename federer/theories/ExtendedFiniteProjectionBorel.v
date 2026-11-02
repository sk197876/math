(** Federer (1969), proof of 2.4.4(2), p. 83: supporting real-valued
    replacement when f is finite almost everywhere. The scalar projection
    fixes real values and sends either infinity to zero. It is Borel, not
    continuous at infinity. The scalar continuity imports are the same as
    the existing ExtendedArithmeticContinuity.v; no external integration
    result is used. Source context: MeasureIntegralSqueeze.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal
  topology ereal ereal_normedtype normed_module.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedArithmeticContinuity
  ExtendedArithmeticDomains BorelBooleanSets TopologicalBorel BorelFunctionUP BorelContinuousRegion.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [extended_finite_value_region_borel]: the finite-
    value region used in Federer 2.4.4(2), p. 83,
    is the complement of the two infinite singleton levels. *)
Lemma extended_finite_value_region_borel (R : realType) :
  borel_set [set z : extended_real_line R | z \is a fin_num].
Proof.
have he : [set z : extended_real_line R | z \is a fin_num] =
    [set z | ~~ (z == -oo) && ~~ (z == +oo)].
  by apply/seteqP; split=> z; rewrite /= fin_numE.
rewrite he.
apply: borel_boolean_conjunction; apply: borel_boolean_negation;
  exact: extended_order_singleton_borel.
Qed.

(** Source for [extended_finite_projection_continuous_at_real]:
    supporting scalar-topology fact for the real representative
    in Federer 2.4.4(2), p. 83. Continuity is asserted
    only at finite values. *)
Lemma extended_finite_projection_continuous_at_real (R : realType) (z : extended_real_line R) :
  z \is a fin_num -> {for z, continuous (fun y : extended_real_line R => (fine y : real_line_metric R))}.
Proof.
case: z=> [a| |] //= _; rewrite /continuous_at.
change (@cvg_to _ (fmap (@fine R) (@nbhs _ (extended_real_line R) a%:E))
  (@nbhs _ [the topologicalType of real_line_metric R] a)).
rewrite extended_real_native_neighborhoods.
exact (@fine_fcvg R (@nbhs _ [the topologicalType of (\bar R : Type)] a%:E)
  (@nbhs_filter [the topologicalType of (\bar R : Type)] a%:E) a (@cvg_refl (\bar R) (@nbhs _ [the topologicalType of (\bar R : Type)] a%:E))).
Qed.

(** Source for [extended_finite_projection_borel]: supporting
    Borel replacement of infinite values by zero for the geometric
    approximant of Federer 2.4.4(2), p. 83. Later
    comparison claims separately require those replaced points to be null. *)
Theorem extended_finite_projection_borel (R : realType) :
  is_borel_function (fun y : extended_real_line R => (fine y : real_line_metric R)).
Proof.
have hb := @borel_continuous_region_extension (extended_real_line R)
  [the topologicalType of real_line_metric R] [set z | z \is a fin_num]
  (fun y => (fine y : real_line_metric R)) 0%R
  (@extended_finite_value_region_borel R) (@extended_finite_projection_continuous_at_real R).
have he : (fun y : extended_real_line R =>
    if pselect (y \is a fin_num) then (fine y : real_line_metric R) else 0%R) =
    (fun y : extended_real_line R => (fine y : real_line_metric R)).
  apply: funext=> y; case: (pselect (y \is a fin_num))=> // hy.
  by case: y hy=> [a| |] //=.
by rewrite he in hb.
Qed.
