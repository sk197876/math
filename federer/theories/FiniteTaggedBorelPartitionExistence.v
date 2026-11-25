(** Federer (1969), 4.1.2, p. 348: arbitrarily
    small finite Borel partitions of the original compact
    support exist. A finite ball cover and the
    previously proved disjointification supply their existence. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality reals topology lra.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  CompactFiniteCover MetricClosedBalls TopologicalBorel BorelFamilyBasic
  SetSequenceDisjointification FiniteTaggedBorelPartitionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_tagged_compact_borel_partition_exists]: the
    arbitrarily fine partitions used in Federer 4.1.2,
    p. 348. Empty compacts and zero-dimensional
    source spaces are retained; no positive-volume hypothesis occurs. *)
Theorem finite_tagged_compact_borel_partition_exists (R:realType) n
    (K:set (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))) (e:R):
  compact K ->0<e ->exists m (A:'I_m->set (R_n R n)) (tag:'I_m->R_n R n),
    is_finite_tagged_borel_partition K e A tag.
Proof.
move=>hK he.
pose T:=real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)).
have he2:0<e/2 by rewrite divr_gt0 // ltr0n.
pose B (a:T):set T:=[set x|mdist a x<e/2].
have hOpen a:K a ->open (B a) by move=>_; exact:metric_open_ball_open.
have hCover:K `<=` \bigcup_(a in K) B a.
  move=>x hx; exists x=>//.
  change (is_true (mdist x x<e/2)); by rewrite mdistxx.
have[F hFK hF]:=@compact_open_finite_cover T T K B K hK hOpen hCover.
pose J:=Finite.clone F _.
pose m:=#|J|.
pose center (i:'I_m):T:=val (enum_val i:J).
pose V (k:nat):set T:=
  if pselect (k<m)%N is left hk then K `&` B (center (@Ordinal m k hk)) else set0.
have hVi (i:'I_m):V i=K `&` B (center i).
  rewrite /V; case:pselect=>hi.
  - have hEqual:@Ordinal m i hi= i by apply:val_inj.
    by rewrite hEqual.
  - exfalso; exact:hi (ltn_ord i).
have hVSubset k:V k `<=` K.
  rewrite /V; case:pselect=>hk; first by move=>x [hx _].
  by move=>x [].
have hKBorel:borel_set K:=closed_borel_set (compact_closed (@metric_hausdorff R T) hK).
have hVBorel k:borel_set (V k).
  rewrite /V; case:pselect=>hk; last exact:open_borel_set open0.
  apply:(borel_family_binary_intersection (borel_sets_family T) hKBorel).
  exact:(open_borel_set (@metric_open_ball_open R T (center (@Ordinal m k hk)) (e/2))).
pose A (i:'I_m):set T:=set_sequence_disjointify V i.
have hInside i:A i `<=` K by move=>x [hx _]; exact:hVSubset i x hx.
have hABorel i:borel_set (A i).
  apply:borel_set_difference; first exact:hVBorel i.
  apply:borel_set_countable_union; first exact:countableP.
  by move=>j _; exact:hVBorel j.
have hDisjoint i j x:A i x ->A j x ->i=j.
  move=>hi hj; case:(eqVneq i j)=>[hEqual|hne]; first exact hEqual.
  exfalso.
  have hNat:i!=j :>nat.
    apply/negP=>/eqP heq; apply:(negP hne); apply/eqP; exact:val_inj heq.
  exact:(@set_sequence_disjointify_disjoint T V i j hNat x hi hj).
have hACover x:K x ->exists i,A i x.
  move=>hx.
  have[a ha hax]:=hF x hx.
  pose j:J:=[` ha]%fset.
  pose i:'I_m:=enum_rank j.
  have hMember:V i x.
    rewrite hVi; split=>//.
    have hCenter:center i=a by rewrite /center /i enum_rankK.
    by rewrite hCenter.
  have hPrefix:set_sequence_prefix V m x by exists i=>//; exact:ltn_ord.
  rewrite -set_sequence_disjointify_prefix in hPrefix.
  have[k hk hA]:=hPrefix; exists (@Ordinal m k hk); exact hA.
have hFor i:exists a:T,A i !=set0 ->A i a.
  case:(pselect (A i !=set0))=>hNonempty.
  - have[a ha]:=hNonempty; exists a; by move=>_.
  - exists 0; by move=>h; exfalso; exact:hNonempty h.
have[tag hTag]:=choice hFor.
exists m,A,tag; constructor.
- exact hABorel.
- exact hInside.
- exact hACover.
- exact hDisjoint.
- exact hTag.
- move=>i x hx.
  have hNonempty:A i !=set0 by exists x.
  have htag:=hTag i hNonempty.
  have hX:mdist (center i) x<e/2.
    have h:=hx.1; by rewrite hVi in h; exact:h.2.
  have hTagDistance:mdist (center i) (tag i)<e/2.
    have h:=htag.1; by rewrite hVi in h; exact:h.2.
  have hTriangle:=metric_triangle x (center i) (tag i).
  rewrite (metric_sym x (center i)) in hTriangle.
  apply:ltW; apply:le_lt_trans hTriangle _; lra.
Qed.
