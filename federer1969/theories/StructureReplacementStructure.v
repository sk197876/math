(** Federer (1969), 3.3.16, p. 299: the complete original
    theorem, every exponent and both directions of the equality criterion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric StructureReplacementMeasureUP IntegralGeometricMeasure
  StructureReplacementPureDecomposition StructureReplacementRectifiableMass
  RectifiableSetUP RectifiableGeometricMeasureEquality MeasureUP MeasureBasic MeasureAlmostUP TopologicalBorel.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [structure_replacement_structure_theorem]: the
    full 3.3.13 theorem with an independent replacement measure,
    as required by Federer 3.3.16, p. 299. Original arbitrary E
    of finite original replacement outer mass has a Borel
    countably rectifiable part, original pure remainder null for
    EVERY final integral-geometric exponent, the literal mass
    identity and BOTH directions of the equality criterion.
    Every comparison, counting and carrier-agreement premise is
    discharged for the four actual measures in separate public
    instances. No finite original Hausdorff mass is added. *)
Theorem structure_replacement_structure_theorem (R:realType) n m (hmn:(m<=n)%N)
    (phi:set (inner_metric_space (@euclidean_inner_productP R n))->\bar R)
    (E:set (inner_metric_space (@euclidean_inner_productP R n))) (t: \bar R):
  is_structure_replacement_measure m phi ->phi E< +oo ->1<=t ->
  (exists B,borel_set B /\is_countably_m_rectifiable m B /\
    is_purely_measure_m_unrectifiable phi m (E `\` B) /\
    @integral_geometric_measure R n m hmn t (E `\` B)=0 /\
    phi E=@integral_geometric_measure R n m hmn t E+phi (E `\` B)) /\
  (phi E=@integral_geometric_measure R n m hmn t E <->is_measure_m_rectifiable phi m E).
Proof.
move=>hLaws hFinite ht.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose H:=phi.
pose I:=@integral_geometric_measure R n m hmn t.
have hH:is_measure H:=structure_replacement_measure_law hLaws.
have [B [hBorel [hRectifiable [hPure hNullAll]]]]:=
  @structure_replacement_pure_decomposition R n m hmn phi E hLaws hFinite.
have hNull:I (E `\` B)=0:=hNullAll t ht.
have hSplit:=@structure_replacement_rectifiable_mass_split R n m hmn phi E B t hLaws hFinite ht hBorel hRectifiable hNull.
split; first by exists B; split=>//; split=>//; split=>//; split.
split.
- move=>hEqual.
  rewrite -hEqual in hSplit.
  change (H E=H E+H (E `\` B)) in hSplit.
  have hRemainderFinite:H (E `\` B)< +oo.
    apply:le_lt_trans _ hFinite; apply:(@measure_mono R _ H hH)=>x [hx _]; exact:hx.
  have hEFin:H E \is a fin_num.
    by rewrite (ge0_fin_numE (@measure_nonnegative R [the choiceType of X] H hH E)).
  have hAFin:H (E `\` B) \is a fin_num.
    by rewrite (ge0_fin_numE (@measure_nonnegative R [the choiceType of X] H hH (E `\` B))).
  have hEValue:H E=(fine (H E))%:E by rewrite fineK.
  have hAValue:H (E `\` B)=(fine (H (E `\` B)))%:E by rewrite fineK.
  rewrite hEValue hAValue -EFinD in hSplit.
  have hReal:fine (H E)=(fine (H E)+fine (H (E `\` B)))%R:=EFin_inj hSplit.
  have hCancel:=congr1 (fun z:R=>(z-fine (H E))%R) hReal.
  rewrite subrr addrAC subrr add0r in hCancel.
  have hZero:H (E `\` B)=0 by rewrite hAValue -hCancel.
  split; last exact:hFinite.
  split; first exact:hH.
  exists B; by split.
- move=>hRect.
  exact:(@structure_replacement_rectifiable_integral_geometric R n m hmn phi E t hLaws hRect ht).
Qed.
