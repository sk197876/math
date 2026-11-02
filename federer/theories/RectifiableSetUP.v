(** Federer (1969), 3.2.14, pp. 251–252: definitions
    of rectifiable, countably rectifiable, measure rectifiable and
    purely unrectifiable sets, with the printed finite-set convention
    in dimension zero. Existence assertions are separate theorems. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric PartialFunctionUP
  PartialMetricLipschitz CoveringFamilyUP MeasureUP MeasureAlmostUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_m_rectifiable]: m rectifiable means the
    image of a bounded Euclidean m-set under a Lipschitzian map,
    Federer 3.2.14(1), p. 251. The final convention on p. 252
    replaces the m=0 case by finiteness. A partial graph retains
    the actual domain and permits an empty target. *)
Definition is_m_rectifiable (R:realType) (X:metricType R) m (E:set X):Prop:=
  match m with
  | 0%N=>finite_set E
  | _=>exists f:partial_function (inner_metric_space (@euclidean_inner_productP R m)) X,
      metric_set_bounded (partial_function_domain f) /\
      (exists L,is_partial_metric_lipschitz_bound f L) /\partial_function_range f=E
  end.

(** Source for [is_countably_m_rectifiable]: E is the union
    of a countable family of m rectifiable sets, Federer
    3.2.14(2), p. 251. A countable family is specified abstractly;
    no particular enumeration is part of the definition. *)
Definition is_countably_m_rectifiable (R:realType) (X:metricType R) m (E:set X):Prop:=
  exists C:set (set X),countable C /\(forall F,C F->is_m_rectifiable m F) /\
    E=\bigcup_(F in C) F.

(** Source for [is_countably_measure_m_rectifiable]: phi measures
    X and some countably m rectifiable set contains phi almost
    all of E, Federer 3.2.14(3), p. 251. *)
Definition is_countably_measure_m_rectifiable (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E:set X):Prop:=
  is_measure phi /\exists S,is_countably_m_rectifiable m S /\measure_almost_included phi E S.

(** Source for [is_measure_m_rectifiable]: countable (phi,m)
    rectifiability together with phi(E)<infinity, Federer 3.2.14(4),
    p. 252. This uses the original measure, including nonmeasurable E. *)
Definition is_measure_m_rectifiable (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E:set X):Prop:=
  is_countably_measure_m_rectifiable phi m E /\(phi E < +oo)%E.

(** Source for [is_purely_measure_m_unrectifiable]: phi measures
    X and E contains no m rectifiable set of positive phi
    measure, Federer 3.2.14, p. 252, third paragraph. *)
Definition is_purely_measure_m_unrectifiable (R:realType) (X:metricType R)
    (phi:set X->\bar R) m (E:set X):Prop:=
  is_measure phi /\~exists F,F `<=` E /\is_m_rectifiable m F /\(0<phi F)%E.
