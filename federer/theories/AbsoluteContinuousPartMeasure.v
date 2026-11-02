(** The measure law for the operator introduced in Federer (1969), 2.9.1, p.
    152, called obvious in the proof of 2.9.2, p. 153. The argument uses
    only the abstract infimum and attainment laws. Source context:
    AbsoluteContinuousPartUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import AbsoluteContinuousPartUP AbsoluteContinuousPartBasic
  AbsoluteContinuousPartAttainment MeasureUP MeasureAlmostBasic MeasureIndexedCover
  NonnegativeSum NonnegativeSumSupport TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_is_measure]: measure law for psi_phi
    introduced in Federer 2.9.1, p. 152, with the proof opening of 2.9.2, p.
    153 The stronger supporting statement only assumes that phi and psi are
    measures, leaving the Borel-regular decomposition conclusions to 2.9.2. *)
Theorem continuous_part_is_measure (R : realType) (X : topologicalType)
    (phi psi gamma : set X -> \bar R) :
  is_measure phi -> is_measure psi -> is_absolutely_continuous_part phi psi gamma -> is_measure gamma.
Proof.
move=> hphi hpsi hg; constructor; first exact: continuous_part_nonnegative hpsi hg.
move=> A F hF hcover.
pose B C := projT1 (cid (@continuous_part_attained R X phi psi gamma hphi hpsi hg C)).
have hB C : borel_set (B C) /\ phi (C `\` B C)=0 /\ gamma C=psi (B C) :=
  projT2 (cid (@continuous_part_attained R X phi psi gamma hphi hpsi hg C)).
pose U := \bigcup_(C in F) B C.
have hUb : borel_set U.
  apply: (@borel_set_countable_union X _ F B hF)=> C _; exact: (hB C).1.
have hz : phi (A `\` U)=0.
  have hN : phi (\bigcup_(C in F) (C `\` B C))=0.
    apply: (@measure_null_countable_union R X [the choiceType of set X] phi hphi F
      (fun C => C `\` B C) hF)=> C _; exact: (hB C).2.1.
  apply: (@measure_null_subset R X phi hphi _ _) hN.
  move=> x [hx hnU]; have [C hC hxC] := hcover x hx.
  exists C=> //; split=> // hBC; apply: hnU; by exists C.
apply: le_trans (@continuous_part_lower R X phi psi gamma hg A U hUb hz) _.
have hb := @measure_indexed_cover R X [the choiceType of set X] psi hpsi U F B hF (fun x hx => hx).
have he : nonnegative_sum F (fun C => psi (B C))=nonnegative_sum F gamma.
  apply: nonnegative_sum_ext=> C _; exact: esym (hB C).2.2.
by rewrite he in hb.
Qed.
