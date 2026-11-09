(** Federer (1969), 3.3.12, p. 297: actual finite-source
    regressions of the complete original decomposition theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionSpace
  EuclideanOneCoordinate EuclideanLebesgueDimensions OrthogonalProjectionProbability
  StructureConeUP StructureProjectionConditions StructureProjectionDecomposition
  RectifiableSetUP SuslinSetUP BorelClosedProjection TopologicalBorel
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  PointMassMeasure PointMassRegularity WeightedCountingMeasure NonnegativeSum NonnegativeSumSupport
  PositiveClosedSubsets ApproximateDifferentialAffine.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_decomposition_conclusion]: notation for the
    complete original conclusion of Federer 3.3.12, p. 297, used in
    actual regressions. Retain Borel and countable rectifiability,
    original remainder purity and actual projected nullity. *)
Definition structure_decomposition_conclusion (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))):Prop:=
  exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (E `\` B) /\
    measure_almost_everywhere (@orthogonal_projection_probability R n m hmn)
      [set p|euclidean_lebesgue_measure m (euclidean_projection_linear p @` (E `\` B))=0].

(** Source for [structure_finite_source_all_fibres]: regression support
    for condition (II) in Federer 3.3.12, p. 297. Every original fibre
    of an actual finite source is finite, for every original projection. *)
Lemma structure_finite_source_all_fibres (R:realType) n m
    (E:set (inner_metric_space (@euclidean_inner_productP R n)))
    (p:euclidean_projection_space R n m):
  finite_set E ->structure_projection_almost_finite_fibres E p.
Proof.
move=>hFinite.
have hL:=euclidean_lebesgue_is_measure R m.
apply:(measure_almost_everywhere_mono hL _ (measure_almost_everywhere_true hL)).
move=>y _; apply: (sub_finite_set _ hFinite); by move=>x [hx _].
Qed.

(** Source for [structure_singleton_point_mass_conditions]: actual
    conditions (I) and (II) for a positive singleton atom, supporting
    the regressions of Federer 3.3.12, p. 297. Original null subsets
    of this source are empty; every actual fibre is finite. *)
Lemma structure_singleton_point_mass_conditions (R:realType) n m
    (a:inner_metric_space (@euclidean_inner_productP R n))
    (p:euclidean_projection_space R n m):
  structure_projection_preserves_null_subsets (point_mass R a) [set a] p /\
  structure_projection_almost_finite_fibres [set a] p.
Proof.
split; last exact:structure_finite_source_all_fibres (finite_set1 a).
move=>B hB hNull.
have hEmpty:B=set0.
  apply/seteqP; split; last by move=>x [].
  move=>x hx; have hxa:=hB x hx; change (x=a) in hxa.
  have ha:B a by rewrite -hxa.
  have hPositive:(0<point_mass R a B)%E by rewrite (point_mass_in R ha) lte_fin ltr01.
  by rewrite hNull ltxx in hPositive.
have hImage:euclidean_projection_linear p @` B=set0.
  rewrite hEmpty; apply/seteqP; split; [by move=>y [x []]|by move=>y []].
rewrite hImage; exact:measure_empty (euclidean_lebesgue_is_measure R m).
Qed.

(** Source for [structure_singleton_atom_complete_decomposition]:
    complete-theorem regression support for Federer 3.3.12, p. 297.
    Derive both original hypotheses for actual positive singleton mass
    and apply the numbered theorem, retaining every natural 0<=m<=n. *)
Lemma structure_singleton_atom_complete_decomposition (R:realType) n m (hmn:(m<=n)%N)
    (a:inner_metric_space (@euclidean_inner_productP R n)):
  structure_decomposition_conclusion hmn (point_mass R a) [set a].
Proof.
have hStructure:is_structure_measure (point_mass R a).
  split; first exact:point_mass_is_measure.
  move=>C _; exact:point_mass_every_set_measurable.
have hSuslin:is_suslin_set R [set a].
  apply:metric_borel_suslin; apply:closed_borel_set.
  apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
apply:(@federer_3_3_12 R n m hmn (point_mass R a) [set a] hStructure hSuslin).
- rewrite point_mass_in; last by [].
  exact:ltry.
- have hTheta:=theta_star_is_measure R hmn.
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta)).
  move=>p _; exact:structure_singleton_point_mass_conditions.
Qed.

(** Source for [structure_decomposition_positive_zero_atom]: actual
    positive R^0 unit atom in COMPLETE Federer 3.3.12, p. 297.
    Both dimensions are zero and the source mass is one. *)
Example structure_decomposition_positive_zero_atom (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 0) in
  point_mass R (0:X) [set 0]= 1%E /\
  structure_decomposition_conclusion (leqnn 0) (point_mass R (0:X)) [set 0].
Proof.
cbn zeta; split; first exact:point_mass_in.
exact:structure_singleton_atom_complete_decomposition.
Qed.

(** Source for [structure_decomposition_noncentral_line_atom]: actual
    positive line atom at coordinate one in COMPLETE Federer 3.3.12,
    p. 297. Original E is noncentral and the full-dimensional endpoint
    m=n=1 is retained with both hypotheses proved for every projection. *)
Example structure_decomposition_noncentral_line_atom (R:realType):
  let a:=euclidean_one_embed (1:R) in
  point_mass R a [set a]= 1%E /\
  structure_decomposition_conclusion (leqnn 1) (point_mass R a) [set a].
Proof.
cbn zeta; split; first exact:point_mass_in.
exact:structure_singleton_atom_complete_decomposition.
Qed.

(** Source for [structure_decomposition_infinite_ambient_measure]: actual
    weighted line measure of infinite whole mass in COMPLETE Federer
    3.3.12, p. 297. The original source is the nonempty null singleton;
    original projected subsets and original fibres prove (I) and (II).
    No local finiteness or finite whole-space mass is supplied. *)
Example structure_decomposition_infinite_ambient_measure (R:realType):
  let X:=inner_metric_space (@euclidean_inner_productP R 1) in
  let w:X->\bar R:=fun x=>if x==0 then 0%E else +oo%E in
  let phi:=weighted_counting_measure w in
  phi setT=+oo%E /\structure_decomposition_conclusion (leqnn 1) phi [set (0:X)].
Proof.
cbn zeta.
pose X:=inner_metric_space (@euclidean_inner_productP R 1).
pose w:X->\bar R:=fun x=>if x==0 then 0%E else +oo%E.
pose phi:=weighted_counting_measure w.
have hWeight x:(0<=w x)%E by rewrite /w; case:ifP=>_; [exact:lexx|exact:leey].
have hStructure:is_structure_measure phi.
  split; first exact:weighted_counting_measure_is_measure hWeight.
  move=>S _; exact:weighted_counting_measure_measurable hWeight.
have hNull:phi [set (0:X)]=0%E.
  rewrite /phi weighted_counting_measure_sum nonnegative_sum_singleton; last exact:hWeight.
  by rewrite /w eqxx.
have hOne:euclidean_one_embed (1:R)!=(0:X).
  apply/eqP=>h; have hAt:=congr1 (fun x:X=>x ord0) h.
  have hBad:(1:R)=0 by move:hAt; rewrite /euclidean_one_embed !ffunE.
  have hPositive:=@ltr01 R; by rewrite hBad ltxx in hPositive.
have hWhole:phi setT=+oo%E.
  apply/eqP; rewrite eq_le leey /= /phi weighted_counting_measure_sum.
  have hTerm:=@nonnegative_sum_term R [the choiceType of X] setT w
    (euclidean_one_embed (1:R)) Logic.I.
  by rewrite /w (negbTE hOne) in hTerm.
split; first exact:hWhole.
have hSuslin:is_suslin_set R [set (0:X)].
  apply:metric_borel_suslin; apply:closed_borel_set.
  apply:accessible_closed_set1; apply:hausdorff_accessible; exact:metric_hausdorff.
apply:(@federer_3_3_12 R 1 1 (leqnn 1) phi [set (0:X)] hStructure hSuslin).
- rewrite hNull; exact:ltry.
- have hTheta:=theta_star_is_measure R (leqnn 1).
  apply:(measure_almost_everywhere_mono hTheta _ (measure_almost_everywhere_true hTheta)).
  move=>p _; split; last exact:structure_finite_source_all_fibres (finite_set1 (0:X)).
  move=>B hB _.
  apply:(@measure_null_subset R [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)]
    _ (euclidean_lebesgue_is_measure R 1) _ [set euclidean_projection_linear p (0:X)] _
    (@positive_euclidean_singleton_null R 0 (euclidean_projection_linear p (0:X)))).
  by move=>y [x hx <-]; have h:=hB x hx; change (x=0) in h; rewrite h.
Qed.
