(** Federer (1969), 3.3.4, p. 289:
    the original B_j and C_j are
    Borel for a continuous frame family.
    No regularity of A, local finiteness
    or numerator Borel regularity is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  StructureConeUP StructureCoordinateGrowth StructureCoordinateGrowthLaws
  StructureCoordinateGrowthBorel StructureCoordinateAlternatives StructurePositiveGrowthLimits
  PositiveRightOrderLimit PositiveRadiusLimits TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Borel.
Variable R:realType.
Variables m k:nat.
Variable P:topologicalType.
Variable f:P->{linear R_n R (m+k)->R_n R (m+k)}.
Variable phi:set (inner_metric_space (@euclidean_inner_productP R (m+k)))->\bar R.
Variable A:set (inner_metric_space (@euclidean_inner_productP R (m+k))).
Variable a:inner_metric_space (@euclidean_inner_productP R (m+k)).
Variable j:'I_k.
Hypothesis hF:continuous (fun z:P*inner_metric_space (@euclidean_inner_productP R (m+k))=>
  (f z.1 (z.2-a):inner_metric_space (@euclidean_inner_productP R (m+k)))).
Hypothesis hPhi:is_structure_measure phi.

(** Source for [structure_coordinate_ordinary_zero_fibre_borel]:
    fixed-cutoff ordinary zero-limit parameters
    are Borel, supporting B_j in Federer
    3.3.4, p. 289. Nonnegative original
    costs identify this ordinary zero limit
    exactly with the zero upper-density fibre. *)
Theorem structure_coordinate_ordinary_zero_fibre_borel (delta:R):
  0<delta ->borel_set [set p:P|positive_right_extended_order_limit
    (structure_coordinate_radial_supremum phi A a (f p) j delta) 0%E].
Proof.
move=>hd.
have hNonnegative p s:0<s ->
    (0<=structure_coordinate_radial_supremum phi A a (f p) j delta s)%E.
  exact:(@structure_coordinate_supremum_nonnegative R m k phi A a (f p) j delta s hPhi.1 hd).
have hEqual:[set p:P|positive_right_extended_order_limit
      (structure_coordinate_radial_supremum phi A a (f p) j delta) 0%E]=
    [set p:P|positive_radius_upper_limit
      (structure_coordinate_radial_supremum phi A a (f p) j delta)=0%E].
  apply/seteqP; split=>p hp.
  - exact:(structure_ordinary_zero_limit_upper (hNonnegative p) hp).
  - exact:(structure_nonnegative_zero_upper_limit_ordinary (hNonnegative p) hp).
rewrite hEqual.
exact:(@structure_coordinate_upper_growth_value_borel R m k P f phi A a j delta 0%E hF hPhi).
Qed.

(** Source for [structure_coordinate_B_borel]: the
    actual set B_j is Borel, Federer
    3.3.4, p. 289. Positive reciprocal
    cutoffs give its exact countable union
    of original ordinary zero-limit loci. *)
Theorem structure_coordinate_B_borel:
  borel_set [set p:P|structure_coordinate_zero_growth phi A a (f p) j].
Proof.
have hEqual:[set p:P|structure_coordinate_zero_growth phi A a (f p) j]=
    \bigcup_i [set p:P|positive_right_extended_order_limit
      (structure_coordinate_radial_supremum phi A a (f p) j ((i.+1)%:R:R)^-1) 0%E].
  apply/seteqP; split=>p hp.
  - have [i hi]:=(@structure_coordinate_zero_reciprocal_iff R m k phi A a (f p) j hPhi.1).1 hp.
    by exists i.
  - have [i _ hi]:=hp.
    apply:(@structure_coordinate_zero_reciprocal_iff R m k phi A a (f p) j hPhi.1).2.
    by exists i.
rewrite hEqual; apply:borel_set_countable_union (countableP setT) _=>i _.
apply:structure_coordinate_ordinary_zero_fibre_borel; by rewrite invr_gt0 ltr0n.
Qed.

(** Source for [structure_coordinate_C_borel]: the
    actual set C_j is Borel, Federer
    3.3.4, p. 289. Its every-positive-
    cutoff infinite upper limit is exactly
    the countable intersection of the original
    infinite-value fibres at reciprocal cutoffs. *)
Theorem structure_coordinate_C_borel:
  borel_set [set p:P|structure_coordinate_infinite_growth phi A a (f p) j].
Proof.
have hEqual:[set p:P|structure_coordinate_infinite_growth phi A a (f p) j]=
    \bigcap_i [set p:P|positive_radius_upper_limit
      (structure_coordinate_radial_supremum phi A a (f p) j ((i.+1)%:R:R)^-1)=+oo%E].
  apply/seteqP; split=>p hp.
  - move=>i _; exact:(@structure_coordinate_infinite_reciprocal_iff R m k phi A a (f p) j).1 hp i.
  - apply:(@structure_coordinate_infinite_reciprocal_iff R m k phi A a (f p) j).2.
    by move=>i; exact:hp i I.
rewrite hEqual; apply:borel_set_countable_intersection (countableP setT) _ _.
- by exists 0%N.
- move=>i _.
  exact:(@structure_coordinate_upper_growth_value_borel R m k P f phi A a j
    ((i.+1)%:R:R)^-1 +oo%E hF hPhi).
Qed.
End Borel.
