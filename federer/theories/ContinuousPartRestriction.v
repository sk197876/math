(** The global Borel restriction in Federer (1969), 2.9.2, p. 153. Apply the
    local bounded-set identity on a countable disjoint bounded Borel
    partition, take the union of its selected Borel subsets, and use
    countable additivity on restricted measures twice. Source context:
    MeasureDerivationContext.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import MeasureDerivationContext AbsoluteContinuousPartUP AbsoluteContinuousPartMeasure
  ContinuousPartBorel ContinuousPartLocal BoundedBorelPartitionUP BoundedBorelPartition
  MeasureUP MeasureRestriction MeasureAlmostBasic MeasureDisjointIntersectionSum
  BorelRegularMeasureUP TopologicalBorel NonnegativeSum NonnegativeSumSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [continuous_part_restriction_exists]: the first conclusion of
    Federer 2.9.2, p. 153: psi_phi=psi restricted to a Borel set B whose
    complement is phi-null. The abstract infimum and local restriction laws
    are used throughout. *)
Theorem continuous_part_restriction_exists (R : realType) (X : metricType R)
    (phi psi gamma : set X -> \bar R) :
  is_derivation_measure phi -> is_derivation_measure psi ->
  is_absolutely_continuous_part phi psi gamma ->
  exists B, borel_set B /\ phi (setT `\` B)=0 /\ gamma=measure_restrict psi B.
Proof.
move=> hphi hpsi hg.
have hmphi := derivation_measure_law hphi.
have hmpsi := derivation_measure_law hpsi.
have hrphi := derivation_measure_borel_regular hphi.
have hrpsi := derivation_measure_borel_regular hpsi.
have hbgamma D : borel_set D -> measure_measurable gamma D :=
  @continuous_part_borel_measurable R X phi psi gamma hmphi hmpsi hg
    (fun D => @borel_regular_borel_measurable R X psi hmpsi hrpsi D) D.
have hgamma := @continuous_part_is_measure R X phi psi gamma hmphi hmpsi hg.
have [P hp] := @bounded_borel_partition_exists R X.
have hPb n := @bounded_borel_partition_borel R X P hp n.
have hPbounded n := @bounded_borel_partition_bounded R X P hp n.
have hdP n m hne x : P n x -> P m x -> False :=
  @bounded_borel_partition_disjoint R X P hp n m hne x.
have hex n : exists C, borel_set C /\ C `<=` P n /\ phi (P n `\` C)=0 /\
    forall S, S `<=` P n -> gamma S=psi (C `&` S).
  exact (@continuous_part_local_restriction R X phi psi gamma (P n) hmphi hmpsi hrphi hrpsi hg
    (hPb n) (@derivation_measure_bounded_finite R X phi hphi (P n) (hPbounded n))
    (@derivation_measure_bounded_finite R X psi hpsi (P n) (hPbounded n))).
pose C n := projT1 (cid (hex n)).
have hC n : borel_set (C n) /\ C n `<=` P n /\ phi (P n `\` C n)=0 /\
    forall S, S `<=` P n -> gamma S=psi (C n `&` S) := projT2 (cid (hex n)).
pose B := \bigcup_n C n.
have hB : borel_set B.
  apply: (@borel_set_countable_union X nat setT C (countableP _))=> n _; exact: (hC n).1.
have hnull : phi (setT `\` B)=0.
  have hN : phi (\bigcup_n (P n `\` C n))=0.
    apply: (@measure_null_countable_union R X nat phi hmphi setT (fun n => P n `\` C n) (countableP _)).
    by move=> n _; exact: (hC n).2.2.1.
  apply: (@measure_null_subset R X phi hmphi _ _) hN.
  move=> x [_ hnB].
  have hxP : (\bigcup_n P n) x by rewrite (bounded_borel_partition_union hp).
  have [n _ hx] := hxP; exists n=> //; split=> // hcx; apply: hnB; by exists n.
have hlocal n S : gamma (P n `&` S)=psi (C n `&` S).
  have hsub : P n `&` S `<=` P n by move=> x [].
  rewrite ((hC n).2.2.2 _ hsub); congr (psi _); apply/seteqP; split.
  - by move=> x [hx [_ hs]]; split.
  - move=> x [hx hs]; split=> //; split=> //; exact: (hC n).2.1 x hx.
have hdC n m hne x (hx : C n x) (hy : C m x) : False :=
  hdP n m hne x ((hC n).2.1 x hx) ((hC m).2.1 x hy).
exists B; split=> //; split=> //; apply: funext=> S.
have hsumgamma := @measure_disjoint_union_intersection_sum R X gamma P hgamma
  (fun n => hbgamma (P n) (hPb n)) hdP S.
rewrite (bounded_borel_partition_union hp) setTI in hsumgamma.
have hsumpsi := @measure_disjoint_union_intersection_sum R X psi C hmpsi
  (fun n => @borel_regular_borel_measurable R X psi hmpsi hrpsi (C n) (hC n).1) hdC S.
rewrite hsumgamma /measure_restrict /B hsumpsi.
apply: nonnegative_sum_ext=> n _; exact: hlocal.
Qed.
