(** Federer (1969), 3.2.38, p. 274: the first good-point
    condition is Borel without selecting a derivative field. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  NormMetric NormDifferentialUP NormClassOneUP EuclideanLipschitzClassZero LipschitzUP
  HilbertFormCompactness EuclideanHomOperator HomSpaceNormTopology ContinuousOperatorUP ContinuousOperatorNorm
  MetricProductBackground TopologicalBorel InnerOwnNormTopology
  NormDifferentialRemainderOpen NormDifferentialBorelTests.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_uniform_remainder_points]: the actual
    differential approximation on B(a,delta) in Federer 3.2.38,
    p. 274. The derivative is existential and actual; no field or
    values at nondifferentiability points enter the specification. *)
Definition euclidean_uniform_remainder_points (R:realType) m n
    (f:R_n R m->R_n R n) (e d:R):
    set (inner_metric_space (@euclidean_inner_productP R m)):=
  [set a|exists D,has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a D /\
    forall x,inner_norm (@euclidean_inner_productP R m) (x-a)<d ->
      inner_norm (@euclidean_inner_productP R n) (f x-f a-D (x-a))<=
      e*inner_norm (@euclidean_inner_productP R m) (x-a)].

(** Source for [euclidean_uniform_remainder_points_borel]: supporting
    measurable good-point selection in Federer 3.2.38, p. 274.
    Fixed-increment strict violations are open in the point/operator
    product. Their arbitrary union is open, so its complement is a
    Borel condition on the single-valued actual differential graph. *)
Theorem euclidean_uniform_remainder_points_borel (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (e d:R):
  is_metric_lipschitz setT f ->borel_set (euclidean_uniform_remainder_points f e d).
Proof.
move=>hLip.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose NY:=inner_norm (@euclidean_inner_productP R n).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose hNY:=inner_norm_real_norm (@euclidean_inner_productP R n).
pose ev:=hom_of_linear (linear_id (Hom (R_n R m) (R_n R n))).
pose hZ:=@euclidean_hom_operator_space R m n.
pose E:=real_norm_metric_space hNX.
pose T:=real_norm_metric_space (continuous_operator_norm_is_norm hNY hZ).
pose P:=metric_product E T.
have hf:=euclidean_lipschitz_norm_class_zero hLip.
pose Bad:set P:=\bigcup_(h in [set h:R_n R m|NX h<d])
  [set p:P|setT p.1 /\setT (p.1+h) /\e*NX h<NY (f (p.1+h)-f p.1-ev p.2 h)].
have hBad:open Bad.
  apply:bigcup_open=>h hh.
  exact:(@norm_differential_remainder_violation_open R (R_n R m) (R_n R n)
    (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
    hZ setT f h (e*NX h) hf).
have hGood:borel_set (~` Bad):=closed_borel_set (open_closedC hBad).
have [q [b hb]]:=@hom_space_finite_basis R (R_n R m) (R_n R n)
  m (@coordinate_basis R m) (@coordinate_basisP R m)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
have hTest:=@norm_differential_borel_domain_test R (R_n R m) (R_n R n)
  (Hom (R_n R m) (R_n R n)) NX NY hNX hNY ev (@euclidean_operator_norm R m n)
  hZ m (@coordinate_basis R m) (@coordinate_basisP R m) q b hb setT f hf (~` Bad) hGood.
have hEq:[set a:E|exists D,has_norm_differential NX NY setT f a (ev D) /\(~` Bad) (a,D)]=
    euclidean_uniform_remainder_points f e d.
  apply/seteqP; split=>a.
  - move=>[D [hD hNot]]; exists D; split=>// x hx.
    rewrite leNgt; apply/negP=>hViolation; apply:hNot.
    exists (x-a); first exact hx.
    split; first exact Logic.I; split; first exact Logic.I.
    by rewrite [a+(x-a)]addrCA subrr addr0.
  - move=>[D [hD hRemainder]]; exists D; split=>//.
    move=>[h hh [_ [_ hViolation]]].
    have hSmall:NX (a+h-a)<d by rewrite addrAC subrr add0r.
    have hBound:=hRemainder (a+h) hSmall.
    rewrite [a+h-a]addrAC subrr add0r in hBound.
    by have hFalse:=lt_le_trans hViolation hBound; rewrite ltxx in hFalse.
rewrite hEq in hTest.
exact:((inner_own_norm_borel_iff (@euclidean_inner_productP R m) _).2 hTest).
Qed.

(** Source for [euclidean_uniform_remainder_from_differential]:
    pointwise availability of the first good-point condition in
    Federer 3.2.38, p. 274, directly from the actual remainder
    law. The subsequent finite-measure argument chooses one common
    radius; this lemma adds no uniform differentiability hypothesis. *)
Lemma euclidean_uniform_remainder_from_differential (R:realType) m n
    (f:R_n R m->R_n R n) a D e:
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT f a D ->0<e ->
  exists d:R,0<d /\euclidean_uniform_remainder_points f e d a.
Proof.
move=>hD he; have [d [hd hRemainder]]:=norm_differential_remainder hD he.
exists d; split=>//; exists D; split=>// x hx.
have hSmall:inner_norm (@euclidean_inner_productP R m) (x-a)<d:=hx.
have hh:=hRemainder (x-a) Logic.I hSmall.
by rewrite [a+(x-a)]addrCA subrr addr0 in hh.
Qed.
