(** Federer (1969), 4.1.8, p. 361: the original
    product of the two Radon variation measures is
    Radon on their product domain. Reuse the Borel
    product theorem of 2.6.5, p. 120, and the
    proved countable local-finiteness criterion of 2.2.5.
    The original factor domains discharge the cover inputs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets cardinality
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic ProductMeasure RadonMeasureUP RadonBorelRegularity
  ProductBorelRegularity CountableOpenBaseUP CountableDefaultEnumeration
  CountableLocalFiniteMetricRadon RadonProductCompactFinite MetricProductBackground
  TopologicalProductMaps AffineGroupTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.
Section CountableMetricRadonProduct.
Variable R:realType.
Variables X Y:metricType R.
Variables (alpha:set X->\bar R) (beta:set Y->\bar R).
Hypothesis hAlpha:is_measure alpha.
Hypothesis hBeta:is_measure beta.
Hypothesis hRA:is_radon_measure alpha.
Hypothesis hRB:is_radon_measure beta.
Variables (B1:nat->set X) (B2:nat->set Y).
Hypothesis hB1:is_countable_open_base B1.
Hypothesis hB2:is_countable_open_base B2.
Variables (C1 W1:nat->set X) (C2 W2:nat->set Y).
Hypothesis hC1:forall n,compact (C1 n).
Hypothesis hC2:forall n,compact (C2 n).
Hypothesis hW1:forall n,open (W1 n).
Hypothesis hW2:forall n,open (W2 n).
Hypothesis hWC1:forall n,W1 n `<=` C1 n.
Hypothesis hWC2:forall n,W2 n `<=` C2 n.
Hypothesis hCover1:setT `<=` \bigcup_n W1 n.
Hypothesis hCover2:setT `<=` \bigcup_n W2 n.
Local Notation P := [the metricType R of (metric_product X Y)].
Local Notation mu := (product_measure hAlpha hBeta).

(** Source for [countable_metric_radon_product]: the original
    product of Radon measures is Radon on the given
    countably based metric domains with compact neighbourhood
    covers, supporting Federer 4.1.8, p. 361.
    No whole-space finiteness or nonemptiness is assumed. *)
Theorem countable_metric_radon_product:@is_radon_measure R P mu.
Proof.
have hCount:countable (@setT (nat*nat)%type):=countableP setT.
have[u [_ hSurj]]:=@countable_default_enumeration (Choice.clone (nat*nat)%type _)
  setT (0%N,0%N) hCount.
pose CP (n:nat):set P:=C1 (u n).1 `*` C2 (u n).2.
pose WP (n:nat):set P:=W1 (u n).1 `*` W2 (u n).2.
have hCP n:compact (CP n):=compact_setX (@hC1 (u n).1) (@hC2 (u n).2).
have hWP n:open (WP n).
  have hEqual:WP n=(@fst X Y @^-1` W1 (u n).1) `&`
      (@snd X Y @^-1` W2 (u n).2) by [].
  rewrite hEqual;apply:openI.
  - apply:open_comp (@hW1 (u n).1)=>z _;exact:first_projection_continuous.
  - apply:open_comp (@hW2 (u n).2)=>z _;exact:second_projection_continuous.
have hWCP n:WP n `<=` CP n.
  move=>z [hx hy];exact:conj (@hWC1 (u n).1 z.1 hx) (@hWC2 (u n).2 z.2 hy).
have hCoverWP:setT `<=` \bigcup_n WP n.
  move=>[x y] _.
  have[i _ hi]:=@hCover1 x Logic.I.
  have[j _ hj]:=@hCover2 y Logic.I.
  have[k hk]:=@hSurj (i,j) Logic.I.
  exists k;first exact:Logic.I.
  change (W1 (u k).1 x /\W2 (u k).2 y).
  by rewrite hk;split.
have hCoverCP:setT `<=` \bigcup_n CP n.
  move=>z hz;have[n _ hn]:=@hCoverWP z hz.
  exists n;first exact:Logic.I;exact:(@hWCP n z hn).
have hFinite K:compact K->mu K< +oo.
  exact:(@radon_product_compact_finite R X Y alpha beta hAlpha hBeta hRA hRB K).
have hWPFinite n:mu (WP n)< +oo.
  exact:(le_lt_trans (measure_mono (product_measure_is_measure hAlpha hBeta) (@hWCP n))
    (@hFinite (CP n) (@hCP n))).
apply:(@countable_locally_finite_metric_radon R P mu CP WP
  (product_measure_is_measure hAlpha hBeta)
  (@product_measure_borel_regular R X Y alpha beta hAlpha hBeta B1 B2 hB1 hB2
    (radon_borel_regular hAlpha hRA) (radon_borel_regular hBeta hRB))
  (product_locally_compact (radon_locally_compact hRA) (radon_locally_compact hRB))
  hFinite hCP hCoverCP _ hCoverWP).
move=>n;exact:conj (@hWP n) (@hWPFinite n).
Qed.
End CountableMetricRadonProduct.
