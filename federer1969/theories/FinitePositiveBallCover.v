(** Federer (1969), 3.2.31, p. 269: supporting finite
    localization of a compact source. General-topology compactness
    selects finitely many positive-radius neighborhoods. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals topology.
From Federer Require Import MetricClosedBalls CompactFiniteCover.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_positive_ball_cover]: supporting compact
    localization in Federer 3.2.31, p. 269. A prescribed positive
    radius at each source point admits a finite sequence of
    centers covering K. Empty K permits an empty sequence. The
    arbitrary default point never becomes an active center. *)
Theorem finite_positive_ball_cover (R:realType) (X:metricType R)
    (x0:X) (K:set X) (r:X->R):
  compact K ->(forall x,K x ->0<r x) ->
  exists N (a:nat->X),
    (forall i,(i<N)%N ->K (a i)) /\
    K `<=` \bigcup_(i in [set i|(i<N)%N]) [set x|mdist (a i) x<r (a i)].
Proof.
move=>hK hr.
pose U a:=[set x|mdist a x<r a].
have hCover:K `<=` \bigcup_(a in K) U a.
  move=>x hx; exists x=>//; by rewrite /U /= mdistxx; exact:hr.
have [F hF hCov]:=@compact_open_finite_cover X X K U K hK
  (fun a _=>@metric_open_ball_open R X a (r a)) hCover.
pose s:seq X:=F.
pose a i:=nth x0 s i.
exists (size s),a; split.
- move=>i hi.
  have hmem:a i \in F by exact:mem_nth.
  exact (set_mem (hF (a i) hmem)).
- move=>x hx; have [y hy hxy]:=hCov x hx.
  have hyMem:y \in s:=hy.
  exists (index y s); first by change (is_true (index y s<size s)%N); rewrite index_mem.
  by rewrite /a nth_index.
Qed.
