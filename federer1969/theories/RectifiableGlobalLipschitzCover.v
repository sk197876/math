(** Federer (1969), 3.2.23, p. 260: the reduction to globally
    Lipschitz parametrizations. One map suffices in positive degree;
    the finite-set convention of 3.2.14, p. 252, requires finitely
    many point maps in degree zero. State a countable cover uniformly. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  RectifiableSetUP EuclideanRectifiableGlobalParametrization LipschitzUP LipschitzBasic
  CountableDefaultEnumeration.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_global_lipschitz_cover]: supporting
    globally Lipschitz maps f,g in Federer 3.2.23, p. 260.
    This uniform cover includes zero degree by a finite family of
    constant maps, rather than incorrectly parametrizing a multipoint
    zero-rectifiable set by a single point. Selection is local to
    the existence proof; no new global chosen witness is exposed. *)
Theorem rectifiable_global_lipschitz_cover (R:realType) m n (W:set (R_n R n)):
  (@is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) m W) ->
  exists F:nat->R_n R m->R_n R n,
    (forall i,@is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R m))
      (inner_metric_space (@euclidean_inner_productP R n)) setT (F i)) /\
    W `<=` \bigcup_i (F i @` setT).
Proof.
case:m=>[|m] hW.
- have [u [_ hCover]]:=countable_default_enumeration (0%R:R_n R n) (finite_set_countable hW).
  exists (fun i (_:R_n R 0)=>u i); split.
  + move=>i; exists 1%R; split; first exact:ltr01.
    split; first exact:ler01.
    move=>x y _ _; rewrite mdistxx mul1r; exact:mdist_ge0.
  + move=>w hw; have [i hi]:=hCover w hw; exists i; first exact Logic.I.
    exists (0%R:R_n R 0); first exact Logic.I.
    exact hi.
- have [A [f [_ [hf hImage]]]]:=positive_rectifiable_global_parametrization hW.
  exists (fun _=>f); split; first by move=>i.
  move=>w hw; rewrite -hImage in hw; have [x hx hfx]:=hw.
  exists 0%N; first exact Logic.I; by exists x.
Qed.
